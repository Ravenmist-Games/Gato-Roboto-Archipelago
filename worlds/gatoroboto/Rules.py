from typing import Dict, Any

from BaseClasses import CollectionState
from worlds.generic.Rules import set_rule, add_item_rule

from . import GatoRobotoWorld
from .Names import RegionName, ItemName, LocationName


def set_rules(world: GatoRobotoWorld):
    player = world.player

    def has_rocket_jumps(state: CollectionState, w: GatoRobotoWorld) -> bool:
        return w.options.rocket_jumps and state.has(ItemName.module_missile, w.player)

    def has_coolant_jumps(state: CollectionState, w: GatoRobotoWorld) -> bool:
        return (w.options.rocket_jumps and state.has(ItemName.module_missile, w.player) and state.has(
            ItemName.module_coolant, w.player))

    def has_precise_coolant_jumps(state: CollectionState, w: GatoRobotoWorld) -> bool:
        return (w.options.rocket_jumps and w.options.precise_tricks and state.has(
            ItemName.module_missile, w.player) and state.has(ItemName.module_coolant, w.player))

    def has_spin_boost(state: CollectionState, w: GatoRobotoWorld) -> bool:
        return (w.options.rocket_jumps and w.options.precise_tricks and state.has_all([
            ItemName.module_missile, ItemName.module_spinjump], w.player))

    def has_rocket_or_spin(state: CollectionState, w: GatoRobotoWorld) -> bool:
        return has_rocket_jumps(state, w) or state.has(ItemName.module_spinjump, w.player)

    def can_water_mech(state: CollectionState, w: GatoRobotoWorld) -> bool:
        return w.options.water_mech and state.has(ItemName.module_missile, w.player)

    def has_water_rocket_jumps(state: CollectionState, w: GatoRobotoWorld) -> bool:
        return has_rocket_jumps(state, w) and can_water_mech(state, w)

    def has_aqueducts_state(state: CollectionState, w: GatoRobotoWorld, amt: int) -> bool:
        return state.has_from_list(ItemName.ProgressiveAqueducts, w.player, amt)

    def has_heater_core_state(state: CollectionState, w: GatoRobotoWorld, amt: int) -> bool:
        return state.has_from_list(ItemName.ProgressiveHeaterCore, w.player, amt)

    def has_ventilation_state(state: CollectionState, w: GatoRobotoWorld, amt: int) -> bool:
        return state.has_from_list(ItemName.ProgressiveVentilation, w.player, amt)

    def has_all_progressive_checks(state: CollectionState, w: GatoRobotoWorld) -> bool:
        return (has_aqueducts_state(state, w, 3) and
                has_heater_core_state(state, w, 3) and
                has_ventilation_state(state, w, 3))

    def can_reach_decoder(state: CollectionState, w: GatoRobotoWorld) -> bool:
        return has_all_progressive_checks(state, w) and state.has(ItemName.module_spinjump, w.player)

    def aqueducts_1_rule(item) -> bool:
        if (item.name == ItemName.module_spinjump) or (item.name in ItemName.ProgressiveAqueducts):
            return True

        if not item.advancement:
            return True

        return world.multiworld.state.has_any(([ItemName.module_spinjump] + ItemName.ProgressiveAqueducts), player)

    # Location logic dictionary
    location_logic: Dict[str, Any] = {

        # LANDING SITE

        # West Healthkit
        # LocationName.loc_healthkit_landing_site_west: lambda state: True,

        # East Healthkit
        LocationName.loc_healthkit_landing_site_east:
            lambda state: state.has(ItemName.module_missile, player),

        # Bark Cartridge
        LocationName.loc_cartridge_bark:
            lambda state: state.has(ItemName.module_missile, player),

        # Nicotine Cartridge
        LocationName.loc_cartridge_nicotine:
            lambda state: state.has_all(
                [ItemName.module_missile, ItemName.module_spinjump], player
            ) or has_rocket_jumps(state, world),

        # Missile Module
        # LocationName.loc_module_missile: lambda state: True,

        # Decoder Module
        LocationName.loc_module_decoder:
            lambda state: can_reach_decoder(state, world) or has_spin_boost(state, world),

        # NEXUS

        # Nexus West Healthkit
        LocationName.loc_healthkit_nexus_west:
            lambda state: state.has_all(
                [ItemName.module_spinjump, ItemName.module_phase], player
            ) or has_precise_coolant_jumps(state, world) or has_spin_boost(state, world),

        # Nexus East Healthkit
        LocationName.loc_healthkit_nexus_east:
            lambda state: state.has(ItemName.module_spinjump, player) or has_rocket_jumps(state, world),

        # Coffee Stain Cartridge
        LocationName.loc_cartridge_coffee_stain:
            lambda state: has_aqueducts_state(state, world, 2) or can_water_mech(state, world),

        # Urine Cartridge
        LocationName.loc_cartridge_urine:
            lambda state: state.has(
                ItemName.module_spinjump, player
            ) or has_coolant_jumps(state, world) or world.options.precise_tricks,

        # Swamp Matcha Cartridge
        LocationName.loc_cartridge_swamp_matcha:
            lambda state: has_ventilation_state(state, world, 3) or world.options.precise_tricks,

        # Repeater Module
        LocationName.loc_module_repeater:
            lambda state: state.has_from_list(ItemName.Cartridges, player, 7),

        # Hopper Module
        LocationName.loc_module_hopper:
            lambda state: state.has_from_list(ItemName.Cartridges, player, 14),

        # AQUEDUCTS

        # Aqueducts West Healthkit
        LocationName.loc_healthkit_aqueducts_west:
            lambda state: has_aqueducts_state(state, world, 1) or can_water_mech(state, world),

        # Aqueducts East Healthkit
        LocationName.loc_healthkit_aqueducts_east:
            lambda state: (has_aqueducts_state(state, world, 2) and
                           has_rocket_or_spin(state, world)) or has_water_rocket_jumps(state, world),

        # Port Cartridge
        LocationName.loc_cartridge_port:
            lambda state: state.has_from_list(ItemName.ProgressiveAqueducts, player, 2) and state.has(
                ItemName.module_spinjump, player),

        # Goop Cartridge
        LocationName.loc_cartridge_goop:
            lambda state: has_aqueducts_state(state, world, 3) and state.has(ItemName.module_spinjump, player),

        # Starboard Cartridge
        LocationName.loc_cartridge_starboard:
            lambda state: (has_aqueducts_state(state, world, 2) and
                           has_rocket_or_spin(state, world)) or has_water_rocket_jumps(state, world),

        # Spin Jump Module
        LocationName.loc_module_spinjump:
            lambda state: has_aqueducts_state(state, world, 3),

        # Progressive Aqueducts 1
        # LocationName.loc_progressive_aqueducts_1: lambda state: True,

        # Progressive Aqueducts 2
        LocationName.loc_progressive_aqueducts_2:
            lambda state: has_aqueducts_state(state, world, 1) or has_water_rocket_jumps(state, world),

        # Progressive Aqueducts 3
        LocationName.loc_progressive_aqueducts_3:
            lambda state: has_aqueducts_state(state, world, 2) and has_rocket_or_spin(state, world),

        # HEATER CORE

        # Heater Core West Healthkit
        LocationName.loc_healthkit_heater_core_west:
            lambda state: has_heater_core_state(state, world, 3),

        # Heater Core East Healthkit
        LocationName.loc_healthkit_heater_core_east:
            lambda state: has_heater_core_state(state, world, 3),

        # Virtual Cat Cartridge
        LocationName.loc_cartridge_virtual_cat:
            lambda state: has_heater_core_state(state, world, 3),

        # Meowtrix Cartridge
        LocationName.loc_cartridge_meowtrix:
            lambda state: has_heater_core_state(state, world, 3),

        # Chewed Gum Cartridge
        LocationName.loc_cartridge_chewed_gum:
            lambda state: has_heater_core_state(state, world, 3),

        # Phase Module
        LocationName.loc_module_phase:
            lambda state: has_heater_core_state(state, world, 2) or state.has(ItemName.module_phase, player),

        # Coolant Module
        LocationName.loc_module_coolant:
            lambda state: state.has(ItemName.module_phase, player),

        # Progressive Heater Core 1
        # LocationName.loc_progressive_heater_core_1: lambda state: True,

        # Progressive Heater Core 2
        LocationName.loc_progressive_heater_core_2:
            lambda state: has_heater_core_state(state, world, 1) or state.has(ItemName.module_phase, player),

        # Progressive Heater Core 3
        LocationName.loc_progressive_heater_core_3:
            lambda state: state.has(ItemName.module_phase, player),

        # VENTILATION

        # Ventilation Healthkit
        LocationName.loc_healthkit_ventilation:
            lambda state: state.has_any(ItemName.ProgressiveVentilation, player),

        # Gris Cartridge
        LocationName.loc_cartridge_gris:
            lambda state: has_ventilation_state(state, world, 3),

        # Grape Cartridge
        LocationName.loc_cartridge_grape:
            lambda state: has_ventilation_state(state, world, 3),

        # Bigshot Module
        LocationName.loc_module_bigshot:
            lambda state: has_ventilation_state(state, world, 1),

        # Progressive Ventilation 1
        # LocationName.loc_progressive_ventilation_1: lambda state: True,

        # Progressive Ventilation 2
        LocationName.loc_progressive_ventilation_2:
            lambda state: has_ventilation_state(state, world, 1),

        # Progressive Ventilation 3
        LocationName.loc_progressive_ventilation_3:
            lambda state: has_ventilation_state(state, world, 2),

        # INCUBATOR

        # Incubator Healthkit
        LocationName.loc_healthkit_incubator:
            lambda state: state.has_all([ItemName.module_spinjump,
                                         ItemName.module_hopper,
                                         ItemName.module_phase], player)

        # Tamagato Cartridge
        # LocationName.loc_cartridge_tamagato: lambda state: True

    }

    region_logic: Dict[str, Any] = {
        RegionName.region_nexus:
            lambda state: state.has(ItemName.module_missile, player),
        RegionName.region_heater_core:
            lambda state: has_rocket_or_spin(state, world),
        RegionName.region_ventilation:
            lambda state: has_heater_core_state(state, world, 2) and has_rocket_or_spin(state, world),
        RegionName.region_incubator:
            lambda state: has_all_progressive_checks(state, world) and state.has(ItemName.module_decoder, player),
        RegionName.region_laboratory:
            lambda state: state.has(ItemName.module_phase, player) and has_rocket_or_spin(state, world),
    }

    for location in location_logic:
        set_rule(world.get_location(location), location_logic[location])

    for region in region_logic:
        set_rule(world.get_region(region).entrances[0], region_logic[region])

    add_item_rule(world.get_location(LocationName.loc_progressive_aqueducts_1), aqueducts_1_rule)

    world.multiworld.completion_condition[player] = lambda state: state.has(ItemName.victory, player)
