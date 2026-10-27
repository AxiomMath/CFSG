module

public import CFSG.LocalAnalysis.SteinbergCECommutingBlockSuzukiTits
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SuzukiOuterOdd
public import CFSG.LocalAnalysis.ComponentInitial.EscapingBlockQuotient
public import CFSG.Sporadic.Schreier.TitsComponent

public section

namespace CFSG.LocalAnalysis

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.OuterAutomorphisms

theorem faithful_Suzuki_socle_involution_component_exclusion
    {A : Type} [Group A] [Finite A]
    {W : Subgroup A} [W.Normal] (_hWsimple : IsSimpleGroup W)
    (_hWnonab : ∃ x y : W, x * y ≠ y * x) (hCW : centralizer (W : Set A) = ⊥) {a : A}
    (ha : orderOf a = 2) {L : Subgroup A} (hLW : L ≤ W)
    (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A))) :
    ∀ ℓ e : ℕ, ¬ CFSG.Blueprint.SuzukiModel W ℓ e := by
  rintro ℓ e ⟨-, b, hb, K, _, _, he, hK, ⟨φ⟩⟩
  have hK' : Nat.card K = 2 ^ (2 * b + 1) := by rw [hK, he]
  have hodd : Odd (Nat.card (Outer W)) := by
    rw [Nat.card_congr (equivalence φ).toEquiv]
    exact (CFSG.ProperTwoGeneratedCore.HighRankPair.suzuki_outer_automorphism_group_has_odd_order
      hb hK').1
  have hc2 : (MulAut.conjNormal a : MulAut W) ^ 2 = 1 := by
    rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  have hP : IsPGroup 2 (zpowers (MulAut.conjNormal a : MulAut W)) := by
    rintro ⟨_, n, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change ((MulAut.conjNormal a : MulAut W) ^ n) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc2, one_zpow]
  obtain ⟨z, hz⟩ := CFSG.ProperTwoGeneratedCore.HighRankPair.le_inner_of_isPGroup_two hodd _ hP
    (mem_zpowers _)
  have haz : a = (z : A) := by
    have hcen : (z : A)⁻¹ * a ∈ centralizer (W : Set A) := by
      rw [mem_centralizer_iff]
      intro w hw
      have h1 : (z : A) * w * (z : A)⁻¹ = a * w * a⁻¹ :=
        congrArg (fun f : MulAut W => (f ⟨w, hw⟩ : A)) hz
      calc w * ((z : A)⁻¹ * a) = (z : A)⁻¹ * ((z : A) * w * (z : A)⁻¹) * a := by group
        _ = (z : A)⁻¹ * (a * w * a⁻¹) * a := by rw [h1]
        _ = (z : A)⁻¹ * a * w := by group
    rw [hCW, Subgroup.mem_bot] at hcen
    calc a = (z : A) * ((z : A)⁻¹ * a) := by group
      _ = z := by rw [hcen, mul_one]
  have haW : a ∈ W := haz ▸ z.2
  have hu : orderOf (⟨a, haW⟩ : W) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact ha
  have hL1 : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer ({a} : Set A)) :=
    isComponentOf_of_le hL (le_inf hLW hL.1) inf_le_right
  have hL2 : CFSG.Assembly.IsComponentOf (L.subgroupOf W)
      (centralizer ({(⟨a, haW⟩ : W)} : Set W)) := by
    rw [← isComponentOf_map_iff W.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hLW,
      map_subtype_centralizer_singleton]
    exact hL1
  obtain ⟨K', hK'c⟩ := exists_isComponent_centralizer_of_mulEquiv φ hL2
  have := CFSG.Sporadic.Schreier.Tits.suzuki_involution_centralizer_solvable hK' (φ ⟨a, haW⟩)
    (by rw [MulEquiv.orderOf_eq]; exact hu)
  exact CFSG.Sporadic.Schreier.Tits.not_isComponent_of_solvable K' inferInstance hK'c

end CFSG.LocalAnalysis
