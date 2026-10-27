module

public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Background.E1Amb

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

section Perfect

variable {G : Type*} [Group G]

theorem isPerfect_of_comm_eq {Y : Subgroup G} (h : ⁅Y, Y⁆ = Y) : Group.IsPerfect ↥Y := by
  rw [Group.isPerfect_def]
  have h1 : (commutator ↥Y).map Y.subtype = ⁅Y, Y⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have h2 : (commutator ↥Y).map Y.subtype = (⊤ : Subgroup ↥Y).map Y.subtype := by
    rw [h1, h, Subgroup.map_top, Subgroup.range_subtype]
  exact Subgroup.map_injective Y.subtype_injective h2

theorem le_normalizer_commutator' {H P Q : Subgroup G}
    (hHP : H ≤ Subgroup.normalizer (P : Set G)) (hHQ : H ≤ Subgroup.normalizer (Q : Set G)) :
    H ≤ Subgroup.normalizer ((⁅P, Q⁆ : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHP hh),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHQ hh)]

theorem comm_map_eq {H : Type*} [Group H] (f : G →* H) {Y : Subgroup G} (h : ⁅Y, Y⁆ = Y) :
    ⁅Y.map f, Y.map f⁆ = Y.map f := by
  rw [← Subgroup.map_commutator, h]

variable [Finite G]

theorem twoResidual_eq_self_of_perfect' {Y : Subgroup G} (h : ⁅Y, Y⁆ = Y) :
    twoResidual Y = Y := by
  have hp : Group.IsPerfect ↥Y := isPerfect_of_comm_eq h
  have hpt : Group.IsPerfect ↥(⊤ : Subgroup ↥Y) :=
    Group.IsPerfect.ofSurjective
      (f := (Subgroup.topEquiv : (⊤ : Subgroup ↥Y) ≃* ↥Y).symm.toMonoidHom)
      Subgroup.topEquiv.symm.surjective
  have htop : twoResidual (⊤ : Subgroup ↥Y) = ⊤ :=
    top_le_iff.mp (B6.perfect_le_twoResidual (P := ⊤))
  rw [E1.twoResidual_eq_map_top Y, htop, Subgroup.map_top, Subgroup.range_subtype]

end Perfect

end CFSG.Quasithin.C124
