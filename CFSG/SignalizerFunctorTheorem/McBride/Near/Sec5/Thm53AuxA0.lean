module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Defs
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Bijection

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Thm53A

variable {G : Type u} [Group G]

theorem perfRes_le (X : Subgroup G) : perfRes X ≤ X :=
  Subgroup.map_subtype_le _

theorem isPerfect_perfRes [Finite G] (X : Subgroup G) : Group.IsPerfect ↥(perfRes X) :=
  Nonsolvable.isPerfect_perfectResidual_map X

theorem le_perfRes_of_isPerfect {P X : Subgroup G} (hP : Group.IsPerfect ↥P) (h : P ≤ X) :
    P ≤ perfRes X :=
  Nonsolvable.le_perfectResidual_map_of_isPerfect hP h

theorem perfRes_mono [Finite G] {X Y : Subgroup G} (h : X ≤ Y) : perfRes X ≤ perfRes Y :=
  le_perfRes_of_isPerfect (isPerfect_perfRes X) ((perfRes_le X).trans h)

theorem perfRes_eq_self_of_isPerfect {P : Subgroup G} (hP : Group.IsPerfect ↥P) :
    perfRes P = P :=
  Nonsolvable.perfectResidual_map_eq_of_isPerfect hP

theorem admits_perfRes {Q X : Subgroup G} (h : Admits Q X) : Admits Q (perfRes X) :=
  le_trans h (Nonsolvable.normalizer_le_normalizer_perfectResidual_map X)

theorem perfRes_eq_bot_iff [Finite G] (X : Subgroup G) :
    perfRes X = ⊥ ↔ Group.IsSolvable ↥X := by
  rw [← CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_eq_bot_iff_solvable]
  unfold perfRes
  constructor
  · intro hbot
    exact Subgroup.map_injective X.subtype_injective (hbot.trans (Subgroup.map_bot _).symm)
  · intro hbot
    rw [show CFSG.perfectResidual ↥X = ⊥ from hbot, Subgroup.map_bot]

theorem kOf_le_perfRes_sup_sol [Finite G] (X : Subgroup G) : kOf X ≤ perfRes X ⊔ sol X := by
  have hperf : Group.IsPerfect ↥(CFSG.layer (↥X ⧸ CFSG.solvableRadical ↥X)) :=
    CFSG.LocalCores.layer_isPerfect
  have hle := CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidual _ hperf
  rw [← CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq
    (QuotientGroup.mk' (CFSG.solvableRadical ↥X)) (QuotientGroup.mk'_surjective _)] at hle
  have h1 : Nonsolvable.oStar ↥X ≤ CFSG.perfectResidual ↥X ⊔ CFSG.solvableRadical ↥X := by
    rw [Nonsolvable.oStar_eq_comap_layer]
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hle hx
    have hker : y⁻¹ * x ∈ CFSG.solvableRadical ↥X := by
      rw [← QuotientGroup.ker_mk' (CFSG.solvableRadical ↥X), MonoidHom.mem_ker, map_mul, map_inv,
        hyx]
      exact inv_mul_cancel _
    have : x = y * (y⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hy hker
  unfold kOf perfRes sol
  rw [← Subgroup.map_sup]
  exact Subgroup.map_mono h1

end Thm53A

end CFSG.SignalizerFunctorTheorem.McBride.Near
