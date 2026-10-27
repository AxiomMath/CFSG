module

public import CFSG.Quasithin.EmptyFaithful.S151S9P0
public import CFSG.Quasithin.EmptyFaithful.S151S9P2A

public section

namespace CFSG.Quasithin

namespace HSRuLoc

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint Lift
open scoped Pointwise

variable {G : Type} [Group G]

theorem ker_le_center [Finite G] {L S : Subgroup G} {H : Type} [Group H] [Finite H] {π : ↥L →* H}
    {P Kb Rb : Subgroup H} {e : ℕ} (c : LiftCtx L S π P Kb Rb e) : π.ker ≤ Subgroup.center ↥L := by
  obtain ⟨a, ha, -⟩ := c.hm.quot
  have hH : ¬ IsPGroup 2 H := fun hH2 =>
    not_isPGroup_statedSL3 ((hH2.to_subgroup Kb).of_surjective a ha)
  exact ker_le_center_aux π c.hπ c.hLq.2 c.hZ hH

theorem liftK_le [Finite G] {L S : Subgroup G} {H : Type} [Group H] [Finite H] {π : ↥L →* H}
    {P Kb Rb : Subgroup H} {e : ℕ} (c : LiftCtx L S π P Kb Rb e) : liftK L π Kb ≤ L := by
  have _ := c
  exact Subgroup.map_subtype_le _

theorem map_liftK [Finite G] {L S : Subgroup G} {H : Type} [Group H] [Finite H] {π : ↥L →* H}
    {P Kb Rb : Subgroup H} {e : ℕ} (c : LiftCtx L S π P Kb Rb e) :
    ((liftK L π Kb).subgroupOf L).map π = Kb := by
  have h1 : (liftK L π Kb).subgroupOf L = ⁅Kb.comap π, Kb.comap π⁆ :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  rw [h1]
  exact map_commutator_comap π c.hπ c.hm.perf

theorem liftK_perf [Finite G] {L S : Subgroup G} {H : Type} [Group H] [Finite H] {π : ↥L →* H}
    {P Kb Rb : Subgroup H} {e : ℕ} (c : LiftCtx L S π P Kb Rb e) :
    ⁅liftK L π Kb, liftK L π Kb⁆ = liftK L π Kb := by
  unfold liftK
  rw [← Subgroup.map_commutator,
    commutator_commutator_comap π c.hπ (ker_le_center c) c.hm.perf]

theorem pCoreOf_liftK [Finite G] {L S : Subgroup G} {H : Type} [Group H] [Finite H] {π : ↥L →* H}
    {P Kb Rb : Subgroup H} {e : ℕ} (c : LiftCtx L S π P Kb Rb e) :
    pCoreOf 2 (liftK L π Kb) = liftR L π Kb Rb := by
  obtain ⟨a, ha, hak⟩ := c.hm.quot
  have := isSimpleGroup_statedSL3
  have hkerP : IsPGroup 2 ↥π.ker := by
    rw [c.hker]; exact CFSG.pCore_isPGroup
  have hD := map_commutator_comap π c.hπ c.hm.perf
  have hR := pCoreOf_eq_inf_comap π hkerP hD c.hm.R_le c.hm.R_normal c.hm.R_two
    not_isPGroup_statedSL3 a ha hak
  unfold liftR liftK
  rw [← map_pCoreOf_subtype, hR, Subgroup.map_inf _ _ _ L.subtype_injective]

end HSRuLoc

end CFSG.Quasithin
