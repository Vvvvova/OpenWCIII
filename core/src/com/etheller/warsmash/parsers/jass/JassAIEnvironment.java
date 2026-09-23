package com.etheller.warsmash.parsers.jass;

import java.io.StringReader;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.Iterator;
import java.util.List;

import net.warsmash.parsers.jass.SmashJassParser;

import com.badlogic.gdx.math.Rectangle;
import com.badlogic.gdx.utils.viewport.Viewport;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.abilities.queue.CAbilityQueue;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.CUnitType;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.CUpgradeType;
import com.etheller.interpreter.ast.debug.JassException;
import com.etheller.interpreter.ast.definition.JassDefinitionBlock;
import com.etheller.interpreter.ast.execution.JassThread;
import com.etheller.interpreter.ast.function.JassFunction;
import com.etheller.interpreter.ast.function.JassParameter;
import com.etheller.interpreter.ast.function.NativeJassFunction;
import com.etheller.interpreter.ast.scope.GlobalScope;
import com.etheller.interpreter.ast.scope.TriggerExecutionScope;
import com.etheller.interpreter.ast.util.JassProgram;
import com.etheller.interpreter.ast.value.BooleanJassValue;
import com.etheller.interpreter.ast.value.CodeJassValue;
import com.etheller.interpreter.ast.value.HandleJassType;
import com.etheller.interpreter.ast.value.HandleJassValue;
import com.etheller.interpreter.ast.value.IntegerJassValue;
import com.etheller.interpreter.ast.value.JassType;
import com.etheller.interpreter.ast.value.RealJassValue;
import com.badlogic.gdx.utils.IntMap;
import com.etheller.interpreter.ast.value.visitor.BooleanJassValueVisitor;
import com.etheller.interpreter.ast.value.visitor.CodeJassValueVisitor;
import com.etheller.interpreter.ast.value.visitor.IntegerJassValueVisitor;
import com.etheller.interpreter.ast.value.visitor.ObjectJassValueVisitor;
import com.etheller.interpreter.ast.value.visitor.RealJassValueVisitor;
import com.etheller.warsmash.datasources.DataSource;
import com.etheller.warsmash.parsers.jass.ai.AITown;
import com.etheller.warsmash.parsers.jass.ai.AIUnit;
import com.etheller.warsmash.parsers.jass.scope.CommonTriggerExecutionScope;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.abilities.hero.CAbilityHero;
import com.etheller.warsmash.parsers.fdf.GameUI;
import com.etheller.warsmash.units.Element;
import com.etheller.warsmash.viewer5.Scene;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.CSimulation;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.CUnit;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.CUnitClassification;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.HandleIdAllocator;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.CDestructable;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.abilities.CAbility;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.abilities.harvest.CAbilityHarvest;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.abilities.targeting.AbilityPointTarget;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.behaviors.CBehavior;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.behaviors.CBehaviorAttack;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.behaviors.CBehaviorAttackMove;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.behaviors.build.CBehaviorHumanBuild;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.behaviors.build.CBehaviorHumanRepair;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.behaviors.build.CBehaviorNightElfBuild;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.behaviors.build.CBehaviorOrcBuild;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.behaviors.build.CBehaviorRepair;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.behaviors.build.CBehaviorUndeadBuild;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.behaviors.harvest.CBehaviorHarvest;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.config.War3MapConfig;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.orders.OrderIds;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.players.CAllianceType;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.players.CPlayer;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.players.CPlayerState;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.players.CPlayerUnitOrderExecutor;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.timers.CTimerSleepAction;
import com.etheller.warsmash.util.WarsmashConstants;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.players.CRace;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.trigger.enumtypes.CMapDifficulty;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.state.CGameState;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.util.BooleanAbilityActivationReceiver;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.util.PointAbilityTargetCheckReceiver;
import com.etheller.warsmash.viewer5.handlers.w3x.simulation.util.ResourceType;
import com.etheller.warsmash.util.War3ID;

/**
 * Separate JASS VM used for campaign/melee AI scripts ({@code common.ai} +
 * race {@code *.ai} files). Cooperative {@code StartThread}/{@code Sleep}
 * mirror the map script VM so AI scripts can run without blocking simulation.
 */
public class JassAIEnvironment {
	private final GameUI gameUI;
	private Element skin;
	private final JassProgram jassProgramVisitor;
	private final CSimulation simulation;
	private final int aiPlayerIndex;
	private final HandleJassType playerType;
	private final HandleJassType unitType;
	private float captainHomeX;
	private float captainHomeY;
	private float captainX;
	private float captainY;
	private boolean captainAtHome = true;
	private final List<CUnit> assaultGroup = new ArrayList<>();
	private boolean paused;
	private final List<AITown> aiTowns = new ArrayList<>();
	private final IntMap<AIUnit> handleIdToAIUnit = new IntMap<>();
	private boolean isCampaignAI = false;

	private static final String COMMON_AI_EXTRA_NATIVES =
			"native Player takes integer number returns player\n"
			+ "constant native GetPlayerState takes player whichPlayer, playerstate whichPlayerState returns integer\n"
			+ "constant native GetPlayerAlliance takes player whichPlayer, player otherPlayer, alliancetype whichAllianceSetting returns boolean\n"
			+ "constant native GetPlayerStructureCount takes player whichPlayer, boolean includeUnfinished returns integer\n"
			+ "constant native GetRandomInt takes integer lowBound, integer highBound returns integer\n"
			+ "constant native GetFloatGameState takes fgamestate whichFloatGameState returns real\n"
			+ "constant native GetGameDifficulty takes nothing returns gamedifficulty\n"
			+ "constant native GetFoodMade takes integer unitid returns integer\n"
			+ "constant native GetFoodUsed takes integer unitid returns integer\n"
			+ "constant native VersionCompatible takes version whichVersion returns boolean\n"
			+ "constant native SuicideSleep takes integer seconds returns nothing\n"
			+ "native Cheat takes string cheatStr returns nothing\n"
			+ "constant native Deg2Rad takes real degrees returns real\n"
			+ "constant native Rad2Deg takes real radians returns real\n"
			+ "constant native Sin takes real radians returns real\n"
			+ "constant native Cos takes real radians returns real\n"
			+ "constant native Tan takes real radians returns real\n"
			+ "constant native Asin takes real y returns real\n"
			+ "constant native Acos takes real x returns real\n"
			+ "constant native Atan takes real x returns real\n"
			+ "constant native Atan2 takes real y, real x returns real\n"
			+ "constant native SquareRoot takes real x returns real\n"
			+ "constant native Pow takes real x, real power returns real\n"
			+ "constant native I2R takes integer i returns real\n"
			+ "constant native R2I takes real r returns integer\n"
			+ "constant native I2S takes integer i returns string\n"
			+ "constant native R2S takes real r returns string\n"
			+ "constant native R2SW takes real r, integer width, integer precision returns string\n"
			+ "constant native S2I takes string s returns integer\n"
			+ "constant native S2R takes string s returns real\n"
			+ "constant native StringHash takes string s returns integer\n"
			+ "constant native StringLength takes string s returns integer\n"
			+ "constant native SubString takes string source, integer start, integer end returns string\n"
			+ "constant native StringCase takes string source, boolean upper returns string\n"
			+ "constant native Max takes integer a, integer b returns integer\n"
			+ "constant native GetPlayers takes nothing returns integer\n"
			+ "constant native GetStartLocationX takes integer whichStartLocation returns real\n"
			+ "constant native GetStartLocationY takes integer whichStartLocation returns real\n"
			+ "constant native GetPlayerStartLocation takes player whichPlayer returns integer\n"
			+ "constant native IsUnitDetected takes unit whichUnit, player whichPlayer returns boolean\n";

	public static final class AICommand {
		private final int command;
		private final int data;

		public AICommand(final int command, final int data) {
			this.command = command;
			this.data = data;
		}

		public int getCommand() {
			return this.command;
		}

		public int getData() {
			return this.data;
		}
	}

	private final Deque<AICommand> aiCommandQueue = new ArrayDeque<>();

	public void enqueueCommand(final int command, final int data) {
		this.aiCommandQueue.addLast(new AICommand(command, data));
	}

	public int commandsWaiting() {
		return this.aiCommandQueue.size();
	}

	public int getLastCommand() {
		return this.aiCommandQueue.isEmpty() ? 0 : this.aiCommandQueue.peekFirst().getCommand();
	}

	public int getLastData() {
		return this.aiCommandQueue.isEmpty() ? 0 : this.aiCommandQueue.peekFirst().getData();
	}

	public void popLastCommand() {
		if (!this.aiCommandQueue.isEmpty()) {
			this.aiCommandQueue.pollFirst();
		}
	}

	public JassAIEnvironment() {
		this.gameUI = null;
		this.jassProgramVisitor = null;
		this.simulation = null;
		this.aiPlayerIndex = -1;
		this.playerType = null;
		this.unitType = null;
	}

	private JassAIEnvironment(final JassProgram jassProgramVisitor, final DataSource dataSource,
			final Viewport uiViewport, final Scene uiScene, final GameUI gameUI, final War3MapConfig mapConfig,
			final CSimulation simulation, final int aiPlayerIndex) {
		this.jassProgramVisitor = jassProgramVisitor;
		this.gameUI = gameUI;
		this.simulation = simulation;
		this.aiPlayerIndex = aiPlayerIndex;
		final Rectangle tempRect = new Rectangle();
		final GlobalScope globals = jassProgramVisitor.getGlobals();
		globals.registerHandleType("agent");
		globals.registerHandleType("event");
		this.playerType = globals.registerHandleType("player");
		globals.registerHandleType("widget");
		this.unitType = globals.registerHandleType("unit");
		globals.registerHandleType("destructable");
		globals.registerHandleType("item");
		globals.registerHandleType("ability");
		globals.registerHandleType("buff");
		globals.registerHandleType("force");
		globals.registerHandleType("group");
		globals.registerHandleType("trigger");
		globals.registerHandleType("triggercondition");
		globals.registerHandleType("triggeraction");
		globals.registerHandleType("timer");
		final HandleJassType locationType = globals.registerHandleType("location");
		globals.registerHandleType("region");
		globals.registerHandleType("rect");
		globals.registerHandleType("boolexpr");
		globals.registerHandleType("sound");
		globals.registerHandleType("conditionfunc");
		globals.registerHandleType("filterfunc");
		globals.registerHandleType("unitpool");
		globals.registerHandleType("itempool");
		final HandleJassType raceType = globals.registerHandleType("race");
		final HandleJassType alliancetypeType = globals.registerHandleType("alliancetype");
		final HandleJassType racepreferenceType = globals.registerHandleType("racepreference");
		globals.registerHandleType("gamestate");
		final HandleJassType igamestateType = globals.registerHandleType("igamestate");
		final HandleJassType fgamestateType = globals.registerHandleType("fgamestate");
		final HandleJassType playerstateType = globals.registerHandleType("playerstate");
		final HandleJassType playerscoreType = globals.registerHandleType("playerscore");
		final HandleJassType playergameresultType = globals.registerHandleType("playergameresult");
		final HandleJassType unitstateType = globals.registerHandleType("unitstate");
		final HandleJassType aidifficultyType = globals.registerHandleType("aidifficulty");
		globals.registerHandleType("eventid");
		final HandleJassType gameeventType = globals.registerHandleType("gameevent");
		final HandleJassType playereventType = globals.registerHandleType("playerevent");
		final HandleJassType playeruniteventType = globals.registerHandleType("playerunitevent");
		final HandleJassType uniteventType = globals.registerHandleType("unitevent");
		final HandleJassType limitopType = globals.registerHandleType("limitop");
		final HandleJassType widgeteventType = globals.registerHandleType("widgetevent");
		final HandleJassType dialogeventType = globals.registerHandleType("dialogevent");
		final HandleJassType unittypeType = globals.registerHandleType("unittype");
		final HandleJassType gamespeedType = globals.registerHandleType("gamespeed");
		final HandleJassType gamedifficultyType = globals.registerHandleType("gamedifficulty");
		final HandleJassType gametypeType = globals.registerHandleType("gametype");
		final HandleJassType mapflagType = globals.registerHandleType("mapflag");
		final HandleJassType mapvisibilityType = globals.registerHandleType("mapvisibility");
		final HandleJassType mapsettingType = globals.registerHandleType("mapsetting");
		final HandleJassType mapdensityType = globals.registerHandleType("mapdensity");
		final HandleJassType mapcontrolType = globals.registerHandleType("mapcontrol");
		final HandleJassType playerslotstateType = globals.registerHandleType("playerslotstate");
		final HandleJassType volumegroupType = globals.registerHandleType("volumegroup");
		final HandleJassType camerafieldType = globals.registerHandleType("camerafield");
		globals.registerHandleType("camerasetup");
		final HandleJassType playercolorType = globals.registerHandleType("playercolor");
		final HandleJassType placementType = globals.registerHandleType("placement");
		final HandleJassType startlocprioType = globals.registerHandleType("startlocprio");
		final HandleJassType raritycontrolType = globals.registerHandleType("raritycontrol");
		final HandleJassType blendmodeType = globals.registerHandleType("blendmode");
		final HandleJassType texmapflagsType = globals.registerHandleType("texmapflags");
		globals.registerHandleType("effect");
		final HandleJassType effecttypeType = globals.registerHandleType("effecttype");
		globals.registerHandleType("weathereffect");
		globals.registerHandleType("terraindeformation");
		final HandleJassType fogstateType = globals.registerHandleType("fogstate");
		globals.registerHandleType("fogmodifier");
		globals.registerHandleType("dialog");
		globals.registerHandleType("button");
		globals.registerHandleType("quest");
		globals.registerHandleType("questitem");
		globals.registerHandleType("defeatcondition");
		globals.registerHandleType("timerdialog");
		globals.registerHandleType("leaderboard");
		globals.registerHandleType("multiboard");
		globals.registerHandleType("multiboarditem");
		globals.registerHandleType("trackable");
		globals.registerHandleType("gamecache");
		final HandleJassType versionType = globals.registerHandleType("version");
		final HandleJassType itemtypeType = globals.registerHandleType("itemtype");
		globals.registerHandleType("texttag");
		final HandleJassType attacktypeType = globals.registerHandleType("attacktype");
		final HandleJassType damagetypeType = globals.registerHandleType("damagetype");
		final HandleJassType weapontypeType = globals.registerHandleType("weapontype");
		final HandleJassType soundtypeType = globals.registerHandleType("soundtype");
		globals.registerHandleType("lightning");
		final HandleJassType pathingtypeType = globals.registerHandleType("pathingtype");
		globals.registerHandleType("image");
		globals.registerHandleType("ubersplat");
		globals.registerHandleType("hashtable");
		globals.registerHandleType("framehandle");
		globals.registerHandleType("abilitytype");
		globals.registerHandleType("ordercommandcard");
		globals.registerHandleType("ordercommandcardtype");
		globals.registerHandleType("abilitybehavior");
		globals.registerHandleType("behaviorexpr");
		globals.registerHandleType("iconui");

		Jass2.registerTypingNatives(jassProgramVisitor, raceType, alliancetypeType, racepreferenceType, igamestateType,
				fgamestateType, playerstateType, playerscoreType, playergameresultType, unitstateType, aidifficultyType,
				gameeventType, playereventType, playeruniteventType, uniteventType, limitopType, widgeteventType,
				dialogeventType, unittypeType, gamespeedType, gamedifficultyType, gametypeType, mapflagType,
				mapvisibilityType, mapsettingType, mapdensityType, mapcontrolType, playerslotstateType, volumegroupType,
				camerafieldType, playercolorType, placementType, startlocprioType, raritycontrolType, blendmodeType,
				texmapflagsType, effecttypeType, fogstateType, versionType, itemtypeType, attacktypeType,
				damagetypeType, weapontypeType, soundtypeType, pathingtypeType);
		Jass2.registerConversionAndStringNatives(jassProgramVisitor, gameUI);
		Jass2.registerConfigNatives(jassProgramVisitor, mapConfig, startlocprioType, gametypeType, placementType,
				gamespeedType, gamedifficultyType, mapdensityType, locationType, this.playerType, playercolorType,
				mapcontrolType, playerslotstateType, mapConfig, new HandleIdAllocator());
		Jass2.registerRandomNatives(jassProgramVisitor, simulation);

		globals.createGlobal("PLAYER_STATE_RESOURCE_GOLD", playerstateType,
				new HandleJassValue(playerstateType, CPlayerState.RESOURCE_GOLD));
		globals.createGlobal("PLAYER_STATE_RESOURCE_LUMBER", playerstateType,
				new HandleJassValue(playerstateType, CPlayerState.RESOURCE_LUMBER));
		globals.createGlobal("PLAYER_STATE_RESOURCE_HERO_TOKENS", playerstateType,
				new HandleJassValue(playerstateType, CPlayerState.RESOURCE_HERO_TOKENS));
		globals.createGlobal("PLAYER_STATE_RESOURCE_FOOD_CAP", playerstateType,
				new HandleJassValue(playerstateType, CPlayerState.RESOURCE_FOOD_CAP));
		globals.createGlobal("PLAYER_STATE_RESOURCE_FOOD_USED", playerstateType,
				new HandleJassValue(playerstateType, CPlayerState.RESOURCE_FOOD_USED));
		globals.createGlobal("PLAYER_STATE_FOOD_CAP_CEILING", playerstateType,
				new HandleJassValue(playerstateType, CPlayerState.FOOD_CAP_CEILING));

		globals.createGlobal("FALSE", JassType.BOOLEAN, BooleanJassValue.FALSE);
		globals.createGlobal("TRUE", JassType.BOOLEAN, BooleanJassValue.TRUE);

		globals.createGlobal("RACE_HUMAN", raceType, new HandleJassValue(raceType, getAiRace(1)));
		globals.createGlobal("RACE_ORC", raceType, new HandleJassValue(raceType, getAiRace(2)));
		globals.createGlobal("RACE_UNDEAD", raceType, new HandleJassValue(raceType, getAiRace(3)));
		globals.createGlobal("RACE_NIGHTELF", raceType, new HandleJassValue(raceType, getAiRace(4)));
		globals.createGlobal("RACE_DEMON", raceType, new HandleJassValue(raceType, getAiRace(5)));
		globals.createGlobal("RACE_OTHER", raceType, new HandleJassValue(raceType, getAiRace(7)));

		globals.createGlobal("ALLIANCE_PASSIVE", alliancetypeType,
				new HandleJassValue(alliancetypeType, CAllianceType.PASSIVE));
		globals.createGlobal("ALLIANCE_HELP_REQUEST", alliancetypeType,
				new HandleJassValue(alliancetypeType, CAllianceType.HELP_REQUEST));
		globals.createGlobal("ALLIANCE_HELP_RESPONSE", alliancetypeType,
				new HandleJassValue(alliancetypeType, CAllianceType.HELP_RESPONSE));
		globals.createGlobal("ALLIANCE_SHARED_XP", alliancetypeType,
				new HandleJassValue(alliancetypeType, CAllianceType.SHARED_XP));
		globals.createGlobal("ALLIANCE_SHARED_SPELLS", alliancetypeType,
				new HandleJassValue(alliancetypeType, CAllianceType.SHARED_SPELLS));
		globals.createGlobal("ALLIANCE_SHARED_VISION", alliancetypeType,
				new HandleJassValue(alliancetypeType, CAllianceType.SHARED_VISION));
		globals.createGlobal("ALLIANCE_SHARED_CONTROL", alliancetypeType,
				new HandleJassValue(alliancetypeType, CAllianceType.SHARED_CONTROL));
		globals.createGlobal("ALLIANCE_SHARED_ADVANCED_CONTROL", alliancetypeType,
				new HandleJassValue(alliancetypeType, CAllianceType.SHARED_ADVANCED_CONTROL));
		globals.createGlobal("ALLIANCE_RESCUABLE", alliancetypeType,
				new HandleJassValue(alliancetypeType, CAllianceType.RESCUABLE));
		globals.createGlobal("ALLIANCE_SHARED_VISION_FORCED", alliancetypeType,
				new HandleJassValue(alliancetypeType, CAllianceType.SHARED_VISION_FORCED));

		globals.createGlobal("GAME_STATE_TIME_OF_DAY", fgamestateType,
				new HandleJassValue(fgamestateType, CGameState.TIME_OF_DAY));

		globals.createGlobal("MAP_DIFFICULTY_EASY", gamedifficultyType,
				new HandleJassValue(gamedifficultyType, CMapDifficulty.EASY));
		globals.createGlobal("MAP_DIFFICULTY_NORMAL", gamedifficultyType,
				new HandleJassValue(gamedifficultyType, CMapDifficulty.NORMAL));
		globals.createGlobal("MAP_DIFFICULTY_HARD", gamedifficultyType,
				new HandleJassValue(gamedifficultyType, CMapDifficulty.HARD));
		globals.createGlobal("MAP_DIFFICULTY_INSANE", gamedifficultyType,
				new HandleJassValue(gamedifficultyType, CMapDifficulty.INSANE));

		globals.createGlobal("VERSION_REIGN_OF_CHAOS", versionType,
				new HandleJassValue(versionType, 0));
		globals.createGlobal("VERSION_FROZEN_THRONE", versionType,
				new HandleJassValue(versionType, 1));

		jassProgramVisitor.getJassNativeManager().createNative("GetPlayerState",
				(arguments, globalScope, triggerScope) -> {
					final CPlayer p = arguments.size() > 0 && arguments.get(0) != null
							? arguments.get(0).visit(ObjectJassValueVisitor.getInstance()) : null;
					final CPlayerState whichPlayerState = arguments.size() > 1 && arguments.get(1) != null
							? arguments.get(1).visit(ObjectJassValueVisitor.getInstance()) : null;
					if (p != null && whichPlayerState != null) {
						return IntegerJassValue.of(p.getPlayerState(simulation, whichPlayerState));
					}
					return IntegerJassValue.ZERO;
				});
		jassProgramVisitor.getJassNativeManager().createNative("GetPlayerAlliance",
				(arguments, globalScope, triggerScope) -> {
					final CPlayer p1 = arguments.size() > 0 && arguments.get(0) != null
							? arguments.get(0).visit(ObjectJassValueVisitor.getInstance()) : null;
					final CPlayer p2 = arguments.size() > 1 && arguments.get(1) != null
							? arguments.get(1).visit(ObjectJassValueVisitor.getInstance()) : null;
					final CAllianceType setting = arguments.size() > 2 && arguments.get(2) != null
							? arguments.get(2).visit(ObjectJassValueVisitor.getInstance()) : null;
					if (p1 != null && p2 != null && setting != null) {
						return BooleanJassValue.of(p1.hasAlliance(p2.getId(), setting));
					}
					return BooleanJassValue.FALSE;
				});
		jassProgramVisitor.getJassNativeManager().createNative("GetPlayerStructureCount",
				(arguments, globalScope, triggerScope) -> {
					final CPlayer p = arguments.size() > 0 && arguments.get(0) != null
							? arguments.get(0).visit(ObjectJassValueVisitor.getInstance()) : null;
					final boolean includeUnfinished = arguments.size() > 1 && arguments.get(1) != null
							&& arguments.get(1).visit(BooleanJassValueVisitor.getInstance());
					if (p != null && simulation != null) {
						int count = 0;
						for (final CUnit unit : simulation.getUnits()) {
							if (unit != null && !unit.isDead() && unit.getPlayerIndex() == p.getId() && unit.isBuilding()) {
								if (includeUnfinished || (!unit.isConstructing() && !unit.isUpgrading())) {
									count++;
								}
							}
						}
						return IntegerJassValue.of(count);
					}
					return IntegerJassValue.ZERO;
				});
		jassProgramVisitor.getJassNativeManager().createNative("GetFloatGameState",
				(arguments, globalScope, triggerScope) -> RealJassValue.ZERO);
		jassProgramVisitor.getJassNativeManager().createNative("GetGameDifficulty",
				(arguments, globalScope, triggerScope) -> gamedifficultyType.getNullValue());
		jassProgramVisitor.getJassNativeManager().createNative("GetFoodMade",
				(arguments, globalScope, triggerScope) -> {
					final int unitId = arguments.get(0).visit(IntegerJassValueVisitor.getInstance());
					if (simulation != null) {
						final CUnitType unitType = simulation.getUnitData().getUnitType(new War3ID(unitId));
						return IntegerJassValue.of(unitType != null ? unitType.getFoodMade() : 0);
					}
					return IntegerJassValue.ZERO;
				});
		jassProgramVisitor.getJassNativeManager().createNative("GetFoodUsed",
				(arguments, globalScope, triggerScope) -> {
					final int unitId = arguments.get(0).visit(IntegerJassValueVisitor.getInstance());
					if (simulation != null) {
						final CUnitType unitType = simulation.getUnitData().getUnitType(new War3ID(unitId));
						return IntegerJassValue.of(unitType != null ? unitType.getFoodUsed() : 0);
					}
					return IntegerJassValue.ZERO;
				});
		jassProgramVisitor.getJassNativeManager().createNative("VersionCompatible",
				(arguments, globalScope, triggerScope) -> BooleanJassValue.TRUE);
		jassProgramVisitor.getJassNativeManager().createNative("SuicideSleep",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("Cheat",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("Max",
				(arguments, globalScope, triggerScope) -> {
					final int a = arguments.get(0).visit(IntegerJassValueVisitor.getInstance());
					final int b = arguments.get(1).visit(IntegerJassValueVisitor.getInstance());
					return IntegerJassValue.of(Math.max(a, b));
				});
		jassProgramVisitor.getJassNativeManager().createNative("GetPlayerStartLocation",
				(arguments, globalScope, triggerScope) -> {
					final CPlayer p = arguments.size() > 0 && arguments.get(0) != null
							? arguments.get(0).visit(ObjectJassValueVisitor.getInstance()) : null;
					return IntegerJassValue.of(p != null ? p.getId() : 0);
				});
		jassProgramVisitor.getJassNativeManager().createNative("IsUnitDetected",
				(arguments, globalScope, triggerScope) -> {
					final CUnit unit = arguments.size() > 0 && arguments.get(0) != null
							? arguments.get(0).visit(ObjectJassValueVisitor.getInstance()) : null;
					return BooleanJassValue.of(unit != null && !unit.isDead());
				});

		jassProgramVisitor.getJassNativeManager().createNative("StartThread",
				(arguments, globalScope, triggerScope) -> {
					final CodeJassValue threadFunc = arguments.get(0).visit(CodeJassValueVisitor.getInstance());
					if (threadFunc != null) {
						globalScope.queueThread(globalScope.createThread(threadFunc));
					}
					return null;
				});
		jassProgramVisitor.getJassNativeManager().createNative("Sleep", (arguments, globalScope, triggerScope) -> {
			float seconds;
			if (arguments.size() >= 2) {
				final float lowBound = arguments.get(0).visit(RealJassValueVisitor.getInstance()).floatValue();
				final float highBound = arguments.get(1).visit(RealJassValueVisitor.getInstance()).floatValue();
				if (highBound > lowBound) {
					seconds = lowBound + (simulation.getSeededRandom().nextFloat() * (highBound - lowBound));
				}
				else {
					seconds = lowBound;
				}
			}
			else {
				seconds = arguments.get(0).visit(RealJassValueVisitor.getInstance()).floatValue();
			}
			final JassThread currentThread = globalScope.getCurrentThread();
			if (currentThread != null) {
				currentThread.setSleeping(true);
				final CTimerSleepAction timer = new CTimerSleepAction(currentThread);
				timer.setRepeats(false);
				timer.setTimeoutTime(Math.max(0f, seconds));
				timer.start(simulation);
			}
			return null;
		});
		jassProgramVisitor.getJassNativeManager().createNative("DoAiScriptDebug",
				(arguments, globalScope, triggerScope) -> BooleanJassValue.TRUE);
		jassProgramVisitor.getJassNativeManager().createNative("GetHeroId",
				(arguments, globalScope, triggerScope) -> {
					if (triggerScope instanceof CommonTriggerExecutionScope) {
						final CUnit levelingUnit = ((CommonTriggerExecutionScope) triggerScope).getLevelingUnit();
						if (levelingUnit != null && levelingUnit.getTypeId() != null) {
							return IntegerJassValue.of(levelingUnit.getTypeId().getValue());
						}
					}
					return IntegerJassValue.ZERO;
				});
		jassProgramVisitor.getJassNativeManager().createNative("GetHeroLevelAI",
				(arguments, globalScope, triggerScope) -> {
					if (triggerScope instanceof CommonTriggerExecutionScope) {
						final CUnit levelingUnit = ((CommonTriggerExecutionScope) triggerScope).getLevelingUnit();
						if (levelingUnit != null) {
							final CAbilityHero heroData = levelingUnit.getHeroData();
							if (heroData != null) {
								return IntegerJassValue.of(heroData.getHeroLevel());
							}
						}
					}
					return IntegerJassValue.ZERO;
				});
		jassProgramVisitor.getJassNativeManager().createNative("GetAiPlayer",
				(arguments, globalScope, triggerScope) -> {
					return IntegerJassValue.of(JassAIEnvironment.this.aiPlayerIndex);
				});
		final JassFunction playerFunc = (arguments, globalScope, triggerScope) -> {
			final int index = arguments.get(0).visit(IntegerJassValueVisitor.getInstance());
			final CPlayer player = simulation != null ? simulation.getPlayer(index) : null;
			return new HandleJassValue(JassAIEnvironment.this.playerType, player);
		};
		globals.defineFunction(0, "native", "Player",
				new NativeJassFunction(Collections.singletonList(new JassParameter(JassType.INTEGER, "number")),
						this.playerType, "Player", playerFunc));
		jassProgramVisitor.getJassNativeManager().createNative("Player", playerFunc);
		jassProgramVisitor.getJassNativeManager().createNative("UnitAlive",
				(arguments, globalScope, triggerScope) -> {
					final CUnit unit = arguments.get(0).visit(ObjectJassValueVisitor.getInstance());
					return BooleanJassValue.of((unit != null) && !unit.isDead());
				});
		jassProgramVisitor.getJassNativeManager().createNative("DoNothing",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("DisplayText",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("DisplayTextI",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("DisplayTextII",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("DisplayTextIII",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("Trace",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("TraceI",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("TraceII",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("TraceIII",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("DebugS",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("DebugFI",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("DebugUnitID",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("SetMeleeDifficulty",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("SetTargetHeroes",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("SetPeonsRepair",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("SetHeroesFlee",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("SetUnitsFlee",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("SetGroupsFlee",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("SetSlowChopping",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("SetDefendPlayer",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("SetHeroesTakeItems",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("SetUnitsTakeItems",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("SetIgnoreInjured",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("SetCaptainChanges",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("SetSmartArtillery",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("SetWatchMegaTargets",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("InitAssault",
				(arguments, globalScope, triggerScope) -> {
					JassAIEnvironment.this.assaultGroup.clear();
					return null;
				});
		jassProgramVisitor.getJassNativeManager().createNative("InitDefense",
				(arguments, globalScope, triggerScope) -> {
					JassAIEnvironment.this.assaultGroup.clear();
					return null;
				});
		jassProgramVisitor.getJassNativeManager().createNative("WaitForSignal",
				(arguments, globalScope, triggerScope) -> IntegerJassValue.ZERO);
		jassProgramVisitor.getJassNativeManager().createNative("GetGold",
				(arguments, globalScope, triggerScope) -> {
					final CPlayer player = simulation.getPlayer(JassAIEnvironment.this.aiPlayerIndex);
					return IntegerJassValue.of(player != null ? player.getGold() : 0);
				});
		jassProgramVisitor.getJassNativeManager().createNative("GetWood",
				(arguments, globalScope, triggerScope) -> {
					final CPlayer player = simulation.getPlayer(JassAIEnvironment.this.aiPlayerIndex);
					return IntegerJassValue.of(player != null ? player.getLumber() : 0);
				});
		jassProgramVisitor.getJassNativeManager().createNative("GetUnitCount",
				(arguments, globalScope, triggerScope) -> {
					final int unitId = arguments.get(0).visit(IntegerJassValueVisitor.getInstance());
					final War3ID typeId = new War3ID(unitId);
					final CPlayer player = simulation.getPlayer(JassAIEnvironment.this.aiPlayerIndex);
					if (player == null) {
						return IntegerJassValue.ZERO;
					}
					final int techtreeUnlocked = player.getTechtreeUnlocked(typeId);
					final int techtreeInProgress = player.getTechtreeInProgress(typeId);
					return IntegerJassValue.of(techtreeUnlocked + techtreeInProgress);
				});
		jassProgramVisitor.getJassNativeManager().createNative("GetPlayerUnitTypeCount",
				(arguments, globalScope, triggerScope) -> {
					final CPlayer whichPlayer = arguments.get(0).visit(ObjectJassValueVisitor.getInstance());
					final int unitId = arguments.get(1).visit(IntegerJassValueVisitor.getInstance());
					final War3ID typeId = new War3ID(unitId);
					final CPlayer player = whichPlayer != null ? whichPlayer
							: simulation.getPlayer(JassAIEnvironment.this.aiPlayerIndex);
					if (player == null) {
						return IntegerJassValue.ZERO;
					}
					final int techtreeUnlocked = player.getTechtreeUnlocked(typeId);
					final int techtreeInProgress = player.getTechtreeInProgress(typeId);
					return IntegerJassValue.of(techtreeUnlocked + techtreeInProgress);
				});
		jassProgramVisitor.getJassNativeManager().createNative("GetUnitCountDone",
				(arguments, globalScope, triggerScope) -> {
					final int unitId = arguments.get(0).visit(IntegerJassValueVisitor.getInstance());
					final War3ID typeId = new War3ID(unitId);
					final CPlayer player = simulation.getPlayer(JassAIEnvironment.this.aiPlayerIndex);
					if (player == null) {
						return IntegerJassValue.ZERO;
					}
					final int techtreeUnlocked = player.getTechtreeUnlocked(typeId);
					return IntegerJassValue.of(techtreeUnlocked);
				});
		jassProgramVisitor.getJassNativeManager().createNative("GetTownUnitCount",
				(arguments, globalScope, triggerScope) -> {
					final int unitId = arguments.get(0).visit(IntegerJassValueVisitor.getInstance());
					final int townId = arguments.get(1).visit(IntegerJassValueVisitor.getInstance());
					final boolean done = arguments.get(2).visit(BooleanJassValueVisitor.getInstance());

					int countSum = 0;
					for (final CUnit unit : simulation.getUnits()) {
						if ((unit == null) || unit.isDead() || (unit.getPlayerIndex() != JassAIEnvironment.this.aiPlayerIndex)) {
							continue;
						}
						final AIUnit aiUnit = JassAIEnvironment.this.handleIdToAIUnit.get(unit.getHandleId());
						if ((townId == -1) || (aiUnit == null) || (aiUnit.getTownId() == townId)) {
							final boolean constructing = unit.isConstructing();
							final boolean upgrading = unit.isUpgrading();
							if (upgrading) {
								final War3ID typeId = done ? unit.getTypeId() : unit.getUpgradeIdType();
								if ((typeId != null) && (typeId.getValue() == unitId)) {
									countSum++;
								}
							}
							else if (!done || !constructing) {
								if ((unit.getTypeId() != null) && (unit.getTypeId().getValue() == unitId)) {
									countSum++;
								}
							}
						}
					}
					return IntegerJassValue.of(countSum);
				});
		jassProgramVisitor.getJassNativeManager().createNative("GetEnemyUnitCount",
				(arguments, globalScope, triggerScope) -> {
					final int unitId = arguments.get(0).visit(IntegerJassValueVisitor.getInstance());
					return IntegerJassValue.of(countEnemyUnitsOfType(unitId));
				});
		jassProgramVisitor.getJassNativeManager().createNative("GetEnemyStrength",
				(arguments, globalScope, triggerScope) -> IntegerJassValue
						.of(countEnemyUnitsOfType(0)));
		jassProgramVisitor.getJassNativeManager().createNative("TownWithGreatestNeed",
				(arguments, globalScope, triggerScope) -> IntegerJassValue.ZERO);
		jassProgramVisitor.getJassNativeManager().createNative("GetNextExpansion",
				(arguments, globalScope, triggerScope) -> IntegerJassValue.of(-1));
		jassProgramVisitor.getJassNativeManager().createNative("GetExpansionX",
				(arguments, globalScope, triggerScope) -> RealJassValue.ZERO);
		jassProgramVisitor.getJassNativeManager().createNative("GetExpansionY",
				(arguments, globalScope, triggerScope) -> RealJassValue.ZERO);
		jassProgramVisitor.getJassNativeManager().createNative("GetUnitGoldCost",
				(arguments, globalScope, triggerScope) -> {
					final int unitId = arguments.get(0).visit(IntegerJassValueVisitor.getInstance());
					final CUnitType unitType = simulation.getUnitData().getUnitType(new War3ID(unitId));
					return IntegerJassValue.of(unitType != null ? unitType.getGoldCost() : 0);
				});
		jassProgramVisitor.getJassNativeManager().createNative("GetUnitWoodCost",
				(arguments, globalScope, triggerScope) -> {
					final int unitId = arguments.get(0).visit(IntegerJassValueVisitor.getInstance());
					final CUnitType unitType = simulation.getUnitData().getUnitType(new War3ID(unitId));
					return IntegerJassValue.of(unitType != null ? unitType.getLumberCost() : 0);
				});
		jassProgramVisitor.getJassNativeManager().createNative("GetUnitBuildTime",
				(arguments, globalScope, triggerScope) -> {
					final int unitId = arguments.get(0).visit(IntegerJassValueVisitor.getInstance());
					final CUnitType unitType = simulation.getUnitData().getUnitType(new War3ID(unitId));
					return IntegerJassValue.of(unitType != null ? (int) unitType.getBuildTime() : 0);
				});
		jassProgramVisitor.getJassNativeManager().createNative("GetUpgradeGoldCost",
				(arguments, globalScope, triggerScope) -> {
					final int upgrId = arguments.get(0).visit(IntegerJassValueVisitor.getInstance());
					final War3ID rawcode = new War3ID(upgrId);
					final CPlayer player = simulation.getPlayer(JassAIEnvironment.this.aiPlayerIndex);
					final int currentLevel = player != null ? player.getTechtreeUnlocked(rawcode) : 0;
					final CUpgradeType upgrType = simulation.getUpgradeData().getType(rawcode);
					return IntegerJassValue.of(upgrType != null ? upgrType.getGoldCost(currentLevel) : 0);
				});
		jassProgramVisitor.getJassNativeManager().createNative("GetUpgradeWoodCost",
				(arguments, globalScope, triggerScope) -> {
					final int upgrId = arguments.get(0).visit(IntegerJassValueVisitor.getInstance());
					final War3ID rawcode = new War3ID(upgrId);
					final CPlayer player = simulation.getPlayer(JassAIEnvironment.this.aiPlayerIndex);
					final int currentLevel = player != null ? player.getTechtreeUnlocked(rawcode) : 0;
					final CUpgradeType upgrType = simulation.getUpgradeData().getType(rawcode);
					return IntegerJassValue.of(upgrType != null ? upgrType.getLumberCost(currentLevel) : 0);
				});
		jassProgramVisitor.getJassNativeManager().createNative("SetProduce",
				(arguments, globalScope, triggerScope) -> {
					final int qty = arguments.get(0).visit(IntegerJassValueVisitor.getInstance());
					final int unitId = arguments.get(1).visit(IntegerJassValueVisitor.getInstance());
					final int town = arguments.get(2).visit(IntegerJassValueVisitor.getInstance());
					return BooleanJassValue.of(setProduce(qty, unitId, town));
				});
		jassProgramVisitor.getJassNativeManager().createNative("SetUpgrade",
				(arguments, globalScope, triggerScope) -> {
					final int upgrId = arguments.get(0).visit(IntegerJassValueVisitor.getInstance());
					return BooleanJassValue.of(setUpgrade(upgrId));
				});
		jassProgramVisitor.getJassNativeManager().createNative("SetBuildUnit",
				(arguments, globalScope, triggerScope) -> {
					final int count = arguments.get(0).visit(IntegerJassValueVisitor.getInstance());
					final int unitId = arguments.get(1).visit(IntegerJassValueVisitor.getInstance());
					return BooleanJassValue.of(setBuildUnit(count, unitId));
				});
		jassProgramVisitor.getJassNativeManager().createNative("SetBuildUnitEx",
				(arguments, globalScope, triggerScope) -> {
					final int count = arguments.get(1).visit(IntegerJassValueVisitor.getInstance());
					final int unitId = arguments.get(2).visit(IntegerJassValueVisitor.getInstance());
					return BooleanJassValue.of(setBuildUnit(count, unitId));
				});
		jassProgramVisitor.getJassNativeManager().createNative("SetBuildUpgr",
				(arguments, globalScope, triggerScope) -> {
					final int count = arguments.get(0).visit(IntegerJassValueVisitor.getInstance());
					final int upgrId = arguments.get(1).visit(IntegerJassValueVisitor.getInstance());
					return BooleanJassValue.of(setBuildUpgr(count, upgrId));
				});
		jassProgramVisitor.getJassNativeManager().createNative("SetBuildUpgrEx",
				(arguments, globalScope, triggerScope) -> {
					final int count = arguments.get(1).visit(IntegerJassValueVisitor.getInstance());
					final int upgrId = arguments.get(2).visit(IntegerJassValueVisitor.getInstance());
					return BooleanJassValue.of(setBuildUpgr(count, upgrId));
				});
		jassProgramVisitor.getJassNativeManager().createNative("SetBuildDone",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("ClearBuildQueue",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("AddAssault",
				(arguments, globalScope, triggerScope) -> {
					final int count = arguments.get(0).visit(IntegerJassValueVisitor.getInstance());
					final int unitId = arguments.get(1).visit(IntegerJassValueVisitor.getInstance());
					return BooleanJassValue.of(addUnitsToAssault(count, unitId));
				});
		jassProgramVisitor.getJassNativeManager().createNative("AddDefenders",
				(arguments, globalScope, triggerScope) -> {
					final int count = arguments.get(0).visit(IntegerJassValueVisitor.getInstance());
					final int unitId = arguments.get(1).visit(IntegerJassValueVisitor.getInstance());
					return BooleanJassValue.of(addUnitsToAssault(count, unitId));
				});
		jassProgramVisitor.getJassNativeManager().createNative("GetCaptainX",
				(arguments, globalScope, triggerScope) -> RealJassValue.of(JassAIEnvironment.this.captainX));
		jassProgramVisitor.getJassNativeManager().createNative("GetCaptainY",
				(arguments, globalScope, triggerScope) -> RealJassValue.of(JassAIEnvironment.this.captainY));
		jassProgramVisitor.getJassNativeManager().createNative("GetCaptainLoc",
				(arguments, globalScope, triggerScope) -> locationType.getNullValue());
		jassProgramVisitor.getJassNativeManager().createNative("CaptainInCombat",
				(arguments, globalScope, triggerScope) -> {
					pruneAssaultGroup();
					for (final CUnit unit : JassAIEnvironment.this.assaultGroup) {
						if (unit != null && !unit.isDead()) {
							final CBehavior behavior = unit.getCurrentBehavior();
							if (behavior instanceof CBehaviorAttack || behavior instanceof CBehaviorAttackMove) {
								return BooleanJassValue.TRUE;
							}
						}
					}
					return BooleanJassValue.FALSE;
				});
		jassProgramVisitor.getJassNativeManager().createNative("CaptainIsHome",
				(arguments, globalScope, triggerScope) -> BooleanJassValue.of(JassAIEnvironment.this.captainAtHome));
		jassProgramVisitor.getJassNativeManager().createNative("CaptainIsEmpty",
				(arguments, globalScope, triggerScope) -> {
					pruneAssaultGroup();
					return BooleanJassValue.of(JassAIEnvironment.this.assaultGroup.isEmpty());
				});
		jassProgramVisitor.getJassNativeManager().createNative("CaptainIsFull",
				(arguments, globalScope, triggerScope) -> {
					pruneAssaultGroup();
					return BooleanJassValue.of(!JassAIEnvironment.this.assaultGroup.isEmpty());
				});
		jassProgramVisitor.getJassNativeManager().createNative("CaptainRetreating",
				(arguments, globalScope, triggerScope) -> BooleanJassValue.FALSE);
		jassProgramVisitor.getJassNativeManager().createNative("CaptainAtGoal",
				(arguments, globalScope, triggerScope) -> BooleanJassValue.of(JassAIEnvironment.this.captainAtHome));
		jassProgramVisitor.getJassNativeManager().createNative("CaptainGoHome",
				(arguments, globalScope, triggerScope) -> {
					JassAIEnvironment.this.captainX = JassAIEnvironment.this.captainHomeX;
					JassAIEnvironment.this.captainY = JassAIEnvironment.this.captainHomeY;
					JassAIEnvironment.this.captainAtHome = true;
					issueAssaultPointOrder(JassAIEnvironment.this.captainX, JassAIEnvironment.this.captainY,
							OrderIds.move);
					return null;
				});
		jassProgramVisitor.getJassNativeManager().createNative("ClearCaptainTargets",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("CaptainAttack",
				(arguments, globalScope, triggerScope) -> {
					final float x = arguments.get(0).visit(RealJassValueVisitor.getInstance()).floatValue();
					final float y = arguments.get(1).visit(RealJassValueVisitor.getInstance()).floatValue();
					JassAIEnvironment.this.captainX = x;
					JassAIEnvironment.this.captainY = y;
					JassAIEnvironment.this.captainAtHome = false;
					issueAssaultPointOrder(x, y, OrderIds.attack);
					return null;
				});
		jassProgramVisitor.getJassNativeManager().createNative("CaptainVsUnits",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("CaptainVsPlayer",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("CaptainReadiness",
				(arguments, globalScope, triggerScope) -> IntegerJassValue.of(100));
		jassProgramVisitor.getJassNativeManager().createNative("CaptainReadinessHP",
				(arguments, globalScope, triggerScope) -> IntegerJassValue.of(100));
		jassProgramVisitor.getJassNativeManager().createNative("CaptainGroupSize",
				(arguments, globalScope, triggerScope) -> {
					pruneAssaultGroup();
					return IntegerJassValue.of(JassAIEnvironment.this.assaultGroup.size());
				});
		jassProgramVisitor.getJassNativeManager().createNative("SetCaptainHome",
				(arguments, globalScope, triggerScope) -> {
					// common.ai: SetCaptainHome(which, x, y) — which often ignored for single captain
					final float x;
					final float y;
					if (arguments.size() >= 3) {
						x = arguments.get(1).visit(RealJassValueVisitor.getInstance()).floatValue();
						y = arguments.get(2).visit(RealJassValueVisitor.getInstance()).floatValue();
					}
					else {
						x = arguments.get(0).visit(RealJassValueVisitor.getInstance()).floatValue();
						y = arguments.get(1).visit(RealJassValueVisitor.getInstance()).floatValue();
					}
					JassAIEnvironment.this.captainHomeX = x;
					JassAIEnvironment.this.captainHomeY = y;
					if (JassAIEnvironment.this.captainAtHome) {
						JassAIEnvironment.this.captainX = x;
						JassAIEnvironment.this.captainY = y;
					}
					return null;
				});
		jassProgramVisitor.getJassNativeManager().createNative("SuicidePlayer",
				(arguments, globalScope, triggerScope) -> {
					final CPlayer target = arguments.get(0).visit(ObjectJassValueVisitor.getInstance());
					if (target == null) {
						return BooleanJassValue.FALSE;
					}
					float tx = 0f;
					float ty = 0f;
					int count = 0;
					for (final CUnit unit : JassAIEnvironment.this.simulation.getUnits()) {
						if ((unit != null) && !unit.isDead() && (unit.getPlayerIndex() == target.getId())) {
							tx += unit.getX();
							ty += unit.getY();
							count++;
						}
					}
					if (count == 0) {
						return BooleanJassValue.FALSE;
					}
					tx /= count;
					ty /= count;
					pruneAssaultGroup();
					if (!JassAIEnvironment.this.assaultGroup.isEmpty()) {
						issueAssaultPointOrder(tx, ty, OrderIds.attack);
					}
					else {
						issueAllCombatUnitsAttack(tx, ty);
					}
					return BooleanJassValue.TRUE;
				});
		jassProgramVisitor.getJassNativeManager().createNative("SuicidePlayerUnits",
				(arguments, globalScope, triggerScope) -> {
					final CPlayer target = arguments.get(0).visit(ObjectJassValueVisitor.getInstance());
					if (target == null) {
						return BooleanJassValue.FALSE;
					}
					float tx = 0f;
					float ty = 0f;
					int count = 0;
					for (final CUnit unit : JassAIEnvironment.this.simulation.getUnits()) {
						if ((unit != null) && !unit.isDead() && (unit.getPlayerIndex() == target.getId())) {
							tx += unit.getX();
							ty += unit.getY();
							count++;
						}
					}
					if (count == 0) {
						return BooleanJassValue.FALSE;
					}
					tx /= count;
					ty /= count;
					pruneAssaultGroup();
					if (!JassAIEnvironment.this.assaultGroup.isEmpty()) {
						issueAssaultPointOrder(tx, ty, OrderIds.attack);
					}
					else {
						issueAllCombatUnitsAttack(tx, ty);
					}
					return BooleanJassValue.TRUE;
				});
		jassProgramVisitor.getJassNativeManager().createNative("SuicideUnit",
				(arguments, globalScope, triggerScope) -> {
					final int count = arguments.get(0).visit(IntegerJassValueVisitor.getInstance());
					final int unitId = arguments.get(1).visit(IntegerJassValueVisitor.getInstance());
					suicideUnits(count, unitId, -1);
					return null;
				});
		jassProgramVisitor.getJassNativeManager().createNative("SuicideUnitEx",
				(arguments, globalScope, triggerScope) -> {
					final int count = arguments.get(0).visit(IntegerJassValueVisitor.getInstance());
					final int unitId = arguments.get(1).visit(IntegerJassValueVisitor.getInstance());
					final int targetPlayer = arguments.size() >= 3 ? arguments.get(2).visit(IntegerJassValueVisitor.getInstance()) : -1;
					suicideUnits(count, unitId, targetPlayer);
					return null;
				});
		jassProgramVisitor.getJassNativeManager().createNative("UnitAliveCheck",
				(arguments, globalScope, triggerScope) -> BooleanJassValue.FALSE);
		jassProgramVisitor.getJassNativeManager().createNative("GroupTimedLife",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("DisablePathing",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("SetAmphibious",
				(arguments, globalScope, triggerScope) -> null);
		// Ignore unused locals that some AI scripts declare against BooleanJassValueVisitor
		jassProgramVisitor.getJassNativeManager().createNative("CommandsWaiting",
				(arguments, globalScope, triggerScope) -> IntegerJassValue.of(commandsWaiting()));
		jassProgramVisitor.getJassNativeManager().createNative("PopLastCommand",
				(arguments, globalScope, triggerScope) -> {
					popLastCommand();
					return null;
				});
		jassProgramVisitor.getJassNativeManager().createNative("GetLastCommand",
				(arguments, globalScope, triggerScope) -> IntegerJassValue.of(getLastCommand()));
		jassProgramVisitor.getJassNativeManager().createNative("GetLastData",
				(arguments, globalScope, triggerScope) -> IntegerJassValue.of(getLastData()));

		// -------------------------------------------------------------
		// common.ai campaign economy, towns, and tactical natives
		// -------------------------------------------------------------
		jassProgramVisitor.getJassNativeManager().createNative("ClearHarvestAI",
				(arguments, globalScope, triggerScope) -> {
					return null;
				});
		jassProgramVisitor.getJassNativeManager().createNative("HarvestGold",
				(arguments, globalScope, triggerScope) -> {
					final int town = arguments.get(0).visit(IntegerJassValueVisitor.getInstance());
					final int peons = arguments.get(1).visit(IntegerJassValueVisitor.getInstance());
					harvestGold(town, peons);
					return null;
				});
		jassProgramVisitor.getJassNativeManager().createNative("HarvestWood",
				(arguments, globalScope, triggerScope) -> {
					final int town = arguments.get(0).visit(IntegerJassValueVisitor.getInstance());
					final int peons = arguments.get(1).visit(IntegerJassValueVisitor.getInstance());
					harvestWood(town, peons);
					return null;
				});
		jassProgramVisitor.getJassNativeManager().createNative("StopGathering",
				(arguments, globalScope, triggerScope) -> {
					stopGathering();
					return null;
				});
		jassProgramVisitor.getJassNativeManager().createNative("GetMinesOwned",
				(arguments, globalScope, triggerScope) -> IntegerJassValue.of(1));
		jassProgramVisitor.getJassNativeManager().createNative("GetGoldOwned",
				(arguments, globalScope, triggerScope) -> {
					final CPlayer player = JassAIEnvironment.this.simulation.getPlayer(JassAIEnvironment.this.aiPlayerIndex);
					return IntegerJassValue.of(player != null ? player.getGold() : 0);
				});
		jassProgramVisitor.getJassNativeManager().createNative("TownWithMine",
				(arguments, globalScope, triggerScope) -> IntegerJassValue.ZERO);
		jassProgramVisitor.getJassNativeManager().createNative("TownHasMine",
				(arguments, globalScope, triggerScope) -> {
					final int townId = arguments.get(0).visit(IntegerJassValueVisitor.getInstance());
					return BooleanJassValue.of(townId == 0);
				});
		jassProgramVisitor.getJassNativeManager().createNative("TownHasHall",
				(arguments, globalScope, triggerScope) -> {
					final int townId = arguments.get(0).visit(IntegerJassValueVisitor.getInstance());
					return BooleanJassValue.of(townId == 0);
				});
		jassProgramVisitor.getJassNativeManager().createNative("TownThreatened",
				(arguments, globalScope, triggerScope) -> BooleanJassValue.FALSE);
		jassProgramVisitor.getJassNativeManager().createNative("ShiftTownSpot",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("SetExpansion",
				(arguments, globalScope, triggerScope) -> BooleanJassValue.TRUE);
		jassProgramVisitor.getJassNativeManager().createNative("GetExpansionPeon",
				(arguments, globalScope, triggerScope) -> JassAIEnvironment.this.unitType.getNullValue());
		jassProgramVisitor.getJassNativeManager().createNative("GetExpansionFoe",
				(arguments, globalScope, triggerScope) -> JassAIEnvironment.this.unitType.getNullValue());
		jassProgramVisitor.getJassNativeManager().createNative("GetEnemyExpansion",
				(arguments, globalScope, triggerScope) -> JassAIEnvironment.this.unitType.getNullValue());
		jassProgramVisitor.getJassNativeManager().createNative("GetUpgradeLevel",
				(arguments, globalScope, triggerScope) -> {
					final int upgrId = arguments.get(0).visit(IntegerJassValueVisitor.getInstance());
					final CPlayer player = JassAIEnvironment.this.simulation.getPlayer(JassAIEnvironment.this.aiPlayerIndex);
					if (player != null) {
						return IntegerJassValue.of(player.getTechtreeUnlocked(new War3ID(upgrId)));
					}
					return IntegerJassValue.ZERO;
				});
		jassProgramVisitor.getJassNativeManager().createNative("SetCampaignAI",
				(arguments, globalScope, triggerScope) -> {
					JassAIEnvironment.this.isCampaignAI = true;
					final CPlayer player = JassAIEnvironment.this.simulation.getPlayer(JassAIEnvironment.this.aiPlayerIndex);
					if (player != null) {
						player.setFoodCapCeiling(200);
						player.setFoodCap(200);
						player.setGold(1000000);
						player.setLumber(1000000);
					}
					return null;
				});
		jassProgramVisitor.getJassNativeManager().createNative("SetMeleeAI",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("SetNewHeroes",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("SetHeroLevels",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("SetReplacementCount",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("SetRandomPaths",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("SetHeroesBuyItems",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("MeleeDifficulty",
				(arguments, globalScope, triggerScope) -> IntegerJassValue.of(1));
		jassProgramVisitor.getJassNativeManager().createNative("CreateCaptains",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("ResetCaptainLocs",
				(arguments, globalScope, triggerScope) -> {
					JassAIEnvironment.this.captainHomeX = 0f;
					JassAIEnvironment.this.captainHomeY = 0f;
					return null;
				});
		jassProgramVisitor.getJassNativeManager().createNative("TeleportCaptain",
				(arguments, globalScope, triggerScope) -> {
					final float x = arguments.get(0).visit(RealJassValueVisitor.getInstance()).floatValue();
					final float y = arguments.get(1).visit(RealJassValueVisitor.getInstance()).floatValue();
					JassAIEnvironment.this.captainX = x;
					JassAIEnvironment.this.captainY = y;
					return null;
				});
		jassProgramVisitor.getJassNativeManager().createNative("CaptainReadinessMa",
				(arguments, globalScope, triggerScope) -> IntegerJassValue.of(100));
		jassProgramVisitor.getJassNativeManager().createNative("AttackMoveXY",
				(arguments, globalScope, triggerScope) -> {
					final float x = arguments.get(0).visit(RealJassValueVisitor.getInstance()).floatValue();
					final float y = arguments.get(1).visit(RealJassValueVisitor.getInstance()).floatValue();
					JassAIEnvironment.this.captainX = x;
					JassAIEnvironment.this.captainY = y;
					JassAIEnvironment.this.captainAtHome = false;
					issueAssaultPointOrder(x, y, OrderIds.attack);
					return null;
				});
		jassProgramVisitor.getJassNativeManager().createNative("AttackMoveKill",
				(arguments, globalScope, triggerScope) -> {
					final CUnit target = arguments.get(0).visit(ObjectJassValueVisitor.getInstance());
					if (target != null && !target.isDead()) {
						issueAssaultPointOrder(target.getX(), target.getY(), OrderIds.attack);
					}
					return null;
				});
		jassProgramVisitor.getJassNativeManager().createNative("SetStagePoint",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("LoadZepWave",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("PurchaseZeppelin",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("AddGuardPost",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("FillGuardPosts",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("ReturnGuardPosts",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("ConvertUnits",
				(arguments, globalScope, triggerScope) -> BooleanJassValue.FALSE);
		jassProgramVisitor.getJassNativeManager().createNative("MergeUnits",
				(arguments, globalScope, triggerScope) -> BooleanJassValue.FALSE);
		jassProgramVisitor.getJassNativeManager().createNative("IgnoredUnits",
				(arguments, globalScope, triggerScope) -> IntegerJassValue.ZERO);
		jassProgramVisitor.getJassNativeManager().createNative("Unsummon",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("RemoveInjuries",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("RemoveSiege",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("GetCreepCamp",
				(arguments, globalScope, triggerScope) -> JassAIEnvironment.this.unitType.getNullValue());
		jassProgramVisitor.getJassNativeManager().createNative("StartGetEnemyBase",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("WaitGetEnemyBase",
				(arguments, globalScope, triggerScope) -> BooleanJassValue.FALSE);
		jassProgramVisitor.getJassNativeManager().createNative("GetEnemyBase",
				(arguments, globalScope, triggerScope) -> JassAIEnvironment.this.unitType.getNullValue());
		jassProgramVisitor.getJassNativeManager().createNative("GetMegaTarget",
				(arguments, globalScope, triggerScope) -> JassAIEnvironment.this.unitType.getNullValue());
		jassProgramVisitor.getJassNativeManager().createNative("GetBuilding",
				(arguments, globalScope, triggerScope) -> JassAIEnvironment.this.unitType.getNullValue());
		jassProgramVisitor.getJassNativeManager().createNative("GetEnemyPower",
				(arguments, globalScope, triggerScope) -> IntegerJassValue.ZERO);
		jassProgramVisitor.getJassNativeManager().createNative("SetAllianceTarget",
				(arguments, globalScope, triggerScope) -> null);
		jassProgramVisitor.getJassNativeManager().createNative("GetAllianceTarget",
				(arguments, globalScope, triggerScope) -> JassAIEnvironment.this.unitType.getNullValue());
		jassProgramVisitor.getJassNativeManager().createNative("IsTowered",
				(arguments, globalScope, triggerScope) -> BooleanJassValue.FALSE);
		jassProgramVisitor.getJassNativeManager().createNative("CreepsOnMap",
				(arguments, globalScope, triggerScope) -> BooleanJassValue.FALSE);
		jassProgramVisitor.getJassNativeManager().createNative("UnitInvis",
				(arguments, globalScope, triggerScope) -> {
					final CUnit unit = arguments.get(0).visit(ObjectJassValueVisitor.getInstance());
					return BooleanJassValue.of(unit != null && unit.getInvisLevels() > 0);
				});
	}

	public GlobalScope getGlobalScope() {
		return this.jassProgramVisitor.getGlobals();
	}

	public int getAiPlayerIndex() {
		return this.aiPlayerIndex;
	}

	private int countUnitsOfType(final int playerIndex, final int unitTypeId, final boolean enemiesOnly) {
		int count = 0;
		final War3ID typeId = unitTypeId == 0 ? null : new War3ID(unitTypeId);
		final CPlayer self = this.simulation.getPlayer(this.aiPlayerIndex);
		for (final CUnit unit : this.simulation.getUnits()) {
			if ((unit == null) || unit.isDead()) {
				continue;
			}
			if (enemiesOnly) {
				if (self != null && self.hasAlliance(unit.getPlayerIndex(), CAllianceType.PASSIVE)) {
					continue;
				}
				if (unit.getPlayerIndex() == this.aiPlayerIndex) {
					continue;
				}
			}
			else if (unit.getPlayerIndex() != playerIndex) {
				continue;
			}
			if ((typeId != null) && (unit.getTypeId().getValue() != typeId.getValue())) {
				continue;
			}
			count++;
		}
		return count;
	}

	private int countEnemyUnitsOfType(final int unitTypeId) {
		return countUnitsOfType(-1, unitTypeId, true);
	}

	private void pruneAssaultGroup() {
		final Iterator<CUnit> it = this.assaultGroup.iterator();
		while (it.hasNext()) {
			final CUnit unit = it.next();
			if ((unit == null) || unit.isDead() || (unit.getPlayerIndex() != this.aiPlayerIndex)) {
				it.remove();
			}
		}
	}

	private boolean addUnitsToAssault(final int count, final int unitTypeId) {
		if (count <= 0) {
			return false;
		}
		final War3ID typeId = unitTypeId == 0 ? null : new War3ID(unitTypeId);
		int added = 0;
		for (final CUnit unit : this.simulation.getUnits()) {
			if (added >= count) {
				break;
			}
			if ((unit == null) || unit.isDead() || (unit.getPlayerIndex() != this.aiPlayerIndex)) {
				continue;
			}
			if ((typeId != null) && (unit.getTypeId().getValue() != typeId.getValue())) {
				continue;
			}
			if (this.assaultGroup.contains(unit)) {
				continue;
			}
			this.assaultGroup.add(unit);
			added++;
		}
		return added > 0;
	}

	private void issueAssaultPointOrder(final float x, final float y, final int orderId) {
		pruneAssaultGroup();
		for (final CUnit unit : this.assaultGroup) {
			issuePointOrder(unit, x, y, orderId);
		}
	}

	private void issueAllCombatUnitsAttack(final float x, final float y) {
		for (final CUnit unit : this.simulation.getUnits()) {
			if ((unit == null) || unit.isDead() || (unit.getPlayerIndex() != this.aiPlayerIndex)) {
				continue;
			}
			if (unit.isBuilding() || unit.getClassifications().contains(CUnitClassification.PEON)) {
				continue;
			}
			issuePointOrder(unit, x, y, OrderIds.attack);
		}
	}

	private void issuePointOrder(final CUnit whichUnit, final float x, final float y, final int preferredOrderId) {
		final CPlayerUnitOrderExecutor executor = this.simulation
				.getDefaultPlayerUnitOrderExecutor(whichUnit.getPlayerIndex());
		if (executor == null) {
			return;
		}
		final int[] tryOrders = new int[] { preferredOrderId, OrderIds.attack, OrderIds.smart, OrderIds.move };
		for (final int orderId : tryOrders) {
			final BooleanAbilityActivationReceiver activationReceiver = BooleanAbilityActivationReceiver.INSTANCE;
			int abilityHandleId = 0;
			AbilityPointTarget targetAsPoint = new AbilityPointTarget(x, y);
			for (final CAbility ability : whichUnit.getAbilities()) {
				ability.checkCanUse(this.simulation, whichUnit, orderId, activationReceiver);
				if (activationReceiver.isOk()) {
					final PointAbilityTargetCheckReceiver targetReceiver = PointAbilityTargetCheckReceiver.INSTANCE;
					ability.checkCanTarget(this.simulation, whichUnit, orderId, targetAsPoint, targetReceiver.reset());
					if (targetReceiver.getTarget() != null) {
						targetAsPoint = targetReceiver.getTarget();
						abilityHandleId = ability.getHandleId();
					}
				}
			}
			if (abilityHandleId != 0) {
				executor.issuePointOrder(whichUnit.getHandleId(), abilityHandleId, orderId, targetAsPoint.x,
						targetAsPoint.y, false);
				return;
			}
		}
	}

	private boolean setProduce(final int qty, final int unitTypeId, final int town) {
		if (qty <= 0 || unitTypeId == 0) {
			return true;
		}
		final War3ID rawcode = new War3ID(unitTypeId);
		final CPlayer player = this.simulation.getPlayer(this.aiPlayerIndex);
		if (player == null) {
			return false;
		}
		final CUnitType unitType = this.simulation.getUnitData().getUnitType(rawcode);
		if (unitType == null) {
			return false;
		}
		int produced = 0;
		for (int q = 0; q < qty; q++) {
			if (!this.isCampaignAI) {
				if (player.getGold() < unitType.getGoldCost() || player.getLumber() < unitType.getLumberCost()) {
					break;
				}
				if (unitType.getFoodUsed() > 0 && (player.getFoodUsed() + unitType.getFoodUsed() > player.getFoodCap())) {
					break;
				}
			}
			boolean queuedOne = false;
			for (final CUnit unit : this.simulation.getUnits()) {
				if (unit == null || unit.isDead() || unit.getPlayerIndex() != this.aiPlayerIndex
						|| unit.isConstructing() || unit.isUpgrading()) {
					continue;
				}
				for (final CAbility ability : unit.getAbilities()) {
					if (ability instanceof CAbilityQueue) {
						final CAbilityQueue queue = (CAbilityQueue) ability;
						if (queue.getUnitsTrained().contains(rawcode)) {
							final War3ID[] buildQueue = unit.getBuildQueue();
							for (int i = 0; i < buildQueue.length; i++) {
								if (buildQueue[i] == null) {
									unit.queueTrainingUnit(this.simulation, rawcode);
									queuedOne = true;
									produced++;
									break;
								}
							}
						}
					}
					if (queuedOne) {
						break;
					}
				}
				if (queuedOne) {
					break;
				}
			}
			if (!queuedOne) {
				break;
			}
		}
		return produced > 0;
	}

	private boolean setUpgrade(final int upgrId) {
		if (upgrId == 0) {
			return true;
		}
		final War3ID rawcode = new War3ID(upgrId);
		final CPlayer player = this.simulation.getPlayer(this.aiPlayerIndex);
		if (player == null) {
			return false;
		}
		final int currentLevel = player.getTechtreeUnlocked(rawcode) + player.getTechtreeInProgress(rawcode);
		final CUpgradeType upgrType = this.simulation.getUpgradeData().getType(rawcode);
		if (upgrType == null) {
			return false;
		}
		if (!this.isCampaignAI) {
			if (player.getGold() < upgrType.getGoldCost(currentLevel) || player.getLumber() < upgrType.getLumberCost(currentLevel)) {
				return false;
			}
		}
		for (final CUnit unit : this.simulation.getUnits()) {
			if (unit == null || unit.isDead() || unit.getPlayerIndex() != this.aiPlayerIndex
					|| unit.isConstructing() || unit.isUpgrading()) {
				continue;
			}
			for (final CAbility ability : unit.getAbilities()) {
				if (ability instanceof CAbilityQueue) {
					final CAbilityQueue queue = (CAbilityQueue) ability;
					if (queue.getResearchesAvailable().contains(rawcode)) {
						final War3ID[] buildQueue = unit.getBuildQueue();
						for (int i = 0; i < buildQueue.length; i++) {
							if (buildQueue[i] == null) {
								unit.queueResearch(this.simulation, rawcode);
								return true;
							}
						}
					}
				}
			}
		}
		return false;
	}

	private boolean setBuildUnit(final int count, final int unitTypeId) {
		if (count <= 0 || unitTypeId == 0) {
			return true;
		}
		final War3ID rawcode = new War3ID(unitTypeId);
		final CPlayer player = this.simulation.getPlayer(this.aiPlayerIndex);
		if (player == null) {
			return false;
		}
		final int currentCount = player.getTechtreeUnlocked(rawcode) + player.getTechtreeInProgress(rawcode);
		if (currentCount >= count) {
			return true;
		}
		return setProduce(count - currentCount, unitTypeId, -1);
	}

	private boolean setBuildUpgr(final int count, final int upgrId) {
		if (count <= 0 || upgrId == 0) {
			return true;
		}
		final War3ID rawcode = new War3ID(upgrId);
		final CPlayer player = this.simulation.getPlayer(this.aiPlayerIndex);
		if (player == null) {
			return false;
		}
		final int currentLevel = player.getTechtreeUnlocked(rawcode) + player.getTechtreeInProgress(rawcode);
		if (currentLevel >= count) {
			return true;
		}
		return setUpgrade(upgrId);
	}

	private void suicideUnits(final int count, final int unitTypeId, final int targetPlayerIndex) {
		if (count <= 0) {
			return;
		}
		final War3ID typeId = unitTypeId == 0 ? null : new War3ID(unitTypeId);
		float tx = this.captainX;
		float ty = this.captainY;
		boolean hasTarget = !this.captainAtHome;

		final CPlayer self = this.simulation.getPlayer(this.aiPlayerIndex);
		if (!hasTarget) {
			int targetCount = 0;
			float sumX = 0f;
			float sumY = 0f;
			for (final CUnit unit : this.simulation.getUnits()) {
				if (unit == null || unit.isDead()) {
					continue;
				}
				if (targetPlayerIndex >= 0) {
					if (unit.getPlayerIndex() == targetPlayerIndex) {
						sumX += unit.getX();
						sumY += unit.getY();
						targetCount++;
					}
				}
				else if (self != null && !self.hasAlliance(unit.getPlayerIndex(), CAllianceType.PASSIVE)
						&& (unit.getPlayerIndex() != this.aiPlayerIndex)) {
					if (unit.isBuilding()) {
						sumX += unit.getX();
						sumY += unit.getY();
						targetCount++;
					}
				}
			}
			if (targetCount > 0) {
				tx = sumX / targetCount;
				ty = sumY / targetCount;
				hasTarget = true;
			}
		}

		if (!hasTarget) {
			for (final CUnit unit : this.simulation.getUnits()) {
				if ((unit != null) && !unit.isDead() && (unit.getPlayerIndex() == 0)) {
					tx = unit.getX();
					ty = unit.getY();
					hasTarget = true;
					break;
				}
			}
		}

		if (!hasTarget) {
			return;
		}

		int dispatched = 0;
		for (final CUnit unit : this.simulation.getUnits()) {
			if (dispatched >= count) {
				break;
			}
			if ((unit == null) || unit.isDead() || (unit.getPlayerIndex() != this.aiPlayerIndex) || unit.isBuilding()
					|| unit.getClassifications().contains(CUnitClassification.PEON)) {
				continue;
			}
			if ((typeId != null) && (unit.getTypeId().getValue() != typeId.getValue())) {
				continue;
			}
			issuePointOrder(unit, tx, ty, OrderIds.attack);
			dispatched++;
		}
	}

	private void harvestGold(final int town, final int targetPeons) {
		if (this.simulation == null || targetPeons <= 0) {
			return;
		}
		int currentAssigned = 0;
		final List<CUnit> availableWorkers = new ArrayList<>();
		for (final CUnit unit : this.simulation.getUnits()) {
			if (unit == null || unit.isDead() || unit.getPlayerIndex() != this.aiPlayerIndex) {
				continue;
			}
			if (unit.isBuilding() || !unit.getClassifications().contains(CUnitClassification.PEON)) {
				continue;
			}
			final CAbilityHarvest harvest = unit.getFirstAbilityOfType(CAbilityHarvest.class);
			if (harvest == null) {
				continue;
			}
			final CBehavior curBehavior = unit.getCurrentBehavior();
			if (curBehavior instanceof CBehaviorHumanBuild || curBehavior instanceof CBehaviorOrcBuild
					|| curBehavior instanceof CBehaviorUndeadBuild || curBehavior instanceof CBehaviorNightElfBuild
					|| curBehavior instanceof CBehaviorRepair || curBehavior instanceof CBehaviorHumanRepair) {
				continue;
			}
			if (isWorkerHarvestingGold(unit, harvest)) {
				currentAssigned++;
			}
			else if (!isWorkerHarvestingWood(unit, harvest)) {
				availableWorkers.add(unit);
			}
		}

		for (int i = 0; i < availableWorkers.size() && currentAssigned < targetPeons; i++) {
			final CUnit worker = availableWorkers.get(i);
			if (worker.order(this.simulation, OrderIds.autoharvestgold, null)) {
				currentAssigned++;
			}
		}
	}

	private void harvestWood(final int town, final int targetPeons) {
		if (this.simulation == null || targetPeons <= 0) {
			return;
		}
		int currentAssigned = 0;
		final List<CUnit> availableWorkers = new ArrayList<>();
		for (final CUnit unit : this.simulation.getUnits()) {
			if (unit == null || unit.isDead() || unit.getPlayerIndex() != this.aiPlayerIndex) {
				continue;
			}
			if (unit.isBuilding() || !unit.getClassifications().contains(CUnitClassification.PEON)) {
				continue;
			}
			final CAbilityHarvest harvest = unit.getFirstAbilityOfType(CAbilityHarvest.class);
			if (harvest == null) {
				continue;
			}
			final CBehavior curBehavior = unit.getCurrentBehavior();
			if (curBehavior instanceof CBehaviorHumanBuild || curBehavior instanceof CBehaviorOrcBuild
					|| curBehavior instanceof CBehaviorUndeadBuild || curBehavior instanceof CBehaviorNightElfBuild
					|| curBehavior instanceof CBehaviorRepair || curBehavior instanceof CBehaviorHumanRepair) {
				continue;
			}
			if (isWorkerHarvestingWood(unit, harvest)) {
				currentAssigned++;
			}
			else if (!isWorkerHarvestingGold(unit, harvest)) {
				availableWorkers.add(unit);
			}
		}

		for (int i = 0; i < availableWorkers.size() && currentAssigned < targetPeons; i++) {
			final CUnit worker = availableWorkers.get(i);
			if (worker.order(this.simulation, OrderIds.autoharvestlumber, null)) {
				currentAssigned++;
			}
		}
	}

	private boolean isWorkerHarvestingGold(final CUnit unit, final CAbilityHarvest harvest) {
		if (unit.getCurrentOrder() != null && unit.getCurrentOrder().getOrderId() == OrderIds.autoharvestgold) {
			return true;
		}
		if (harvest.getCarriedResourceType() == ResourceType.GOLD) {
			return true;
		}
		if (unit.getCurrentBehavior() instanceof CBehaviorHarvest && harvest.getLastHarvestTarget() instanceof CUnit) {
			return true;
		}
		return false;
	}

	private boolean isWorkerHarvestingWood(final CUnit unit, final CAbilityHarvest harvest) {
		if (unit.getCurrentOrder() != null && unit.getCurrentOrder().getOrderId() == OrderIds.autoharvestlumber) {
			return true;
		}
		if (harvest.getCarriedResourceType() == ResourceType.LUMBER) {
			return true;
		}
		if (unit.getCurrentBehavior() instanceof CBehaviorHarvest && harvest.getLastHarvestTarget() instanceof CDestructable) {
			return true;
		}
		return false;
	}

	private void stopGathering() {
		if (this.simulation == null) {
			return;
		}
		for (final CUnit unit : this.simulation.getUnits()) {
			if (unit == null || unit.isDead() || unit.getPlayerIndex() != this.aiPlayerIndex) {
				continue;
			}
			if (unit.isBuilding() || !unit.getClassifications().contains(CUnitClassification.PEON)) {
				continue;
			}
			final CAbilityHarvest harvest = unit.getFirstAbilityOfType(CAbilityHarvest.class);
			if (harvest != null) {
				final CBehavior curBehavior = unit.getCurrentBehavior();
				if (curBehavior instanceof CBehaviorHumanBuild || curBehavior instanceof CBehaviorOrcBuild
						|| curBehavior instanceof CBehaviorUndeadBuild || curBehavior instanceof CBehaviorNightElfBuild
						|| curBehavior instanceof CBehaviorRepair || curBehavior instanceof CBehaviorHumanRepair) {
					continue;
				}
				unit.order(this.simulation, OrderIds.stop, null);
			}
		}
	}

	public void main() {
		try {
			final JassThread mainThread = this.jassProgramVisitor.getGlobals().createThread("main",
					Collections.emptyList(), TriggerExecutionScope.EMPTY);
			this.jassProgramVisitor.getGlobals().queueThread(mainThread);
		}
		catch (final Exception exc) {
			throw new JassException(this.jassProgramVisitor.getGlobals(),
					"Exception on Line " + this.jassProgramVisitor.getGlobals().getLineNumber(), exc);
		}
	}
	private static volatile List<JassDefinitionBlock> cachedCommonAiBlocks = null;
	private static final Object COMMON_AI_LOCK = new Object();

	public static void preloadCommonAi(final DataSource dataSource) {
		if (cachedCommonAiBlocks == null) {
			synchronized (COMMON_AI_LOCK) {
				if (cachedCommonAiBlocks == null) {
					loadCommonAiBlocks(dataSource);
				}
			}
		}
	}

	public static void resetCachedCommonAi() {
		synchronized (COMMON_AI_LOCK) {
			cachedCommonAiBlocks = null;
		}
	}

	private static List<JassDefinitionBlock> loadCommonAiBlocks(final DataSource dataSource) {
		final List<JassDefinitionBlock> collected = new ArrayList<>();
		final JassProgram collector = new JassProgram() {
			@Override
			public void addAll(final List<JassDefinitionBlock> blocks) {
				super.addAll(blocks);
				collected.addAll(blocks);
			}
		};
		String commonPath = "Scripts\\common.ai";
		if (!dataSource.has(commonPath) && dataSource.has("common.ai")) {
			commonPath = "common.ai";
		}
		if (dataSource.has(commonPath)) {
			try {
				final SmashJassParser extraParser = new SmashJassParser(new StringReader(COMMON_AI_EXTRA_NATIVES));
				extraParser.scanAndParse("COMMON_AI_EXTRA_NATIVES", collector);
				Jass2.readJassFile(dataSource, collector, commonPath);
				cachedCommonAiBlocks = Collections.unmodifiableList(collected);
			}
			catch (final Exception e) {
				System.err.println("Failed to cache common.ai: " + e.getMessage());
			}
		}
		return cachedCommonAiBlocks;
	}

	/**
	 * Loads {@code Scripts\common.ai} plus the race/campaign script and returns a
	 * ready AI environment. Missing scripts are tolerated (returns null) so maps
	 * without AI assets do not crash.
	 */
	public static JassAIEnvironment loadAI(final DataSource dataSource, final Viewport uiViewport, final Scene uiScene,
			final GameUI gameUI, final War3MapConfig mapConfig, final CSimulation simulation, final int aiPlayerIndex,
			final String scriptPath) {
		if ((scriptPath == null) || scriptPath.isEmpty()) {
			System.err.println("StartCampaignAI: empty script path for player " + aiPlayerIndex);
			return null;
		}
		final JassProgram jassProgramVisitor = new JassProgram();
		final JassAIEnvironment environment = new JassAIEnvironment(jassProgramVisitor, dataSource, uiViewport, uiScene,
				gameUI, mapConfig, simulation, aiPlayerIndex);

		preloadCommonAi(dataSource);
		boolean loadedAny = false;
		if (cachedCommonAiBlocks != null) {
			jassProgramVisitor.addAll(cachedCommonAiBlocks);
			loadedAny = true;
		}

		final String[] files = new String[] { scriptPath, "Scripts\\" + scriptPath };
		boolean loadedScript = false;
		for (final String file : files) {
			String path = file;
			if (!dataSource.has(path)) {
				// try basename only
				final int slash = Math.max(path.lastIndexOf('\\'), path.lastIndexOf('/'));
				if (slash >= 0) {
					path = path.substring(slash + 1);
				}
			}
			if (!dataSource.has(path)) {
				continue;
			}
			try {
				Jass2.readJassFile(dataSource, jassProgramVisitor, path);
				loadedScript = true;
				loadedAny = true;
				break;
			}
			catch (final Exception e) {
				System.err.println("StartCampaignAI: failed reading " + path + ": " + e.getMessage());
			}
		}
		if (!loadedAny) {
			System.err.println("StartCampaignAI: no AI script found for \"" + scriptPath + "\" (player "
					+ aiPlayerIndex + ")");
			return null;
		}
		try {
			jassProgramVisitor.initialize();
		}
		catch (final Exception e) {
			System.err.println("StartCampaignAI: initialize failed for " + scriptPath + ": " + e.getMessage());
			e.printStackTrace();
			return null;
		}
		jassProgramVisitor.getJassNativeManager().checkUnregisteredNatives();
		final CPlayer player = simulation != null ? simulation.getPlayer(aiPlayerIndex) : null;
		if (player != null) {
			player.setAiScript(environment);
		}
		return environment;
	}

	public boolean isPaused() {
		return this.paused;
	}

	public void setPaused(final boolean paused) {
		this.paused = paused;
		if (paused) {
			this.simulation.removeAiGlobalScope(getGlobalScope());
		}
		else {
			this.simulation.addAiGlobalScope(getGlobalScope());
		}
	}

	public JassProgram getJassProgram() {
		return this.jassProgramVisitor;
	}

	public List<AITown> getAiTowns() {
		return this.aiTowns;
	}

	public IntMap<AIUnit> getHandleIdToAIUnit() {
		return this.handleIdToAIUnit;
	}

	private static CRace getAiRace(final int id) {
		if (WarsmashConstants.RACE_MANAGER != null) {
			final CRace race = WarsmashConstants.RACE_MANAGER.getRace(id);
			if (race != null) {
				return race;
			}
		}
		return new CRace(id);
	}
}
