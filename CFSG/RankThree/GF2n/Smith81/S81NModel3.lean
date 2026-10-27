module

public import CFSG.RankThree.GF2n.Smith81.S81NMask
public import CFSG.RankThree.GF2n.Smith81.S81NComm
public import CFSG.RankThree.GF2n.Smith81.S81NModelDef

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open scoped commutatorElement

variable {K : Type*} [Field K]

section Model3

@[expose] def ranG3 (K : Type*) [Field K] : Fin 10 → Cube K :=
  ![ub K 0 1 2, ub K 0 1 4, ub K 0 2 3, ub K 0 2 4, ub K 0 4 5, ub K 2 3 4, ub K 2 4 5,
    ub K 0 2 5 + ub K 0 3 4, ub K 0 2 5 + ub K 1 2 4,
    ub K 0 2 5 + ub K 0 3 5 + ub K 1 2 5 + ub K 1 3 4]

@[expose] def ranPre3 (K : Type*) [Field K] : Fin 10 → Cube K :=
  ![ub K 0 1 3, ub K 0 1 5, ub K 1 2 3, ub K 0 2 5, ub K 1 4 5, ub K 2 3 5, ub K 3 4 5,
    ub K 0 3 5 + ub K 0 3 4, ub K 1 2 5 + ub K 1 2 4,
    ub K 1 3 5 + ub K 0 2 5 + (ub K 0 3 5 + ub K 0 3 4) + (ub K 1 2 5 + ub K 1 2 4)]

@[expose] def ranP3 : Fin 10 → ℕ := ![7, 19, 13, 21, 49, 28, 52, 25, 22, 26]

variable [CharP K 2]

theorem ranP3_card : ∀ j, (mset (ranP3 j)).card = 3 := by
  intro j; fin_cases j <;> decide

theorem ranG3_pivots : ∀ i j, cfm K (ranG3 K i) (ranP3 j) = if i = j then (1 : K) else 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [ranG3, ranP3, cfm_ub, cfm_add, CharTwo.add_self_eq_zero]

private theorem model3_F_ranPre_0 : (rho K (tInv3 K) - 1) (ranPre3 K 0) = ranG3 K 0 := by
  rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_iff_eq_add, rho_tInv3,
    Module.End.mul_apply, Module.End.mul_apply]
  apply cfm_ext3
  intro m hm hc
  rcases exists_mask3 hm hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [ranPre3, ranG3, cfm_rho_X01, cfm_rho_X23, cfm_rho_X45,
      cfm_add, cfm_ub_mask, CharTwo.add_self_eq_zero, -Representation.exteriorPower_apply]

private theorem model3_F_ranPre_1 : (rho K (tInv3 K) - 1) (ranPre3 K 1) = ranG3 K 1 := by
  rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_iff_eq_add, rho_tInv3,
    Module.End.mul_apply, Module.End.mul_apply]
  apply cfm_ext3
  intro m hm hc
  rcases exists_mask3 hm hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [ranPre3, ranG3, cfm_rho_X01, cfm_rho_X23, cfm_rho_X45,
      cfm_add, cfm_ub_mask, CharTwo.add_self_eq_zero, -Representation.exteriorPower_apply]

private theorem model3_F_ranPre_2 : (rho K (tInv3 K) - 1) (ranPre3 K 2) = ranG3 K 2 := by
  rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_iff_eq_add, rho_tInv3,
    Module.End.mul_apply, Module.End.mul_apply]
  apply cfm_ext3
  intro m hm hc
  rcases exists_mask3 hm hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [ranPre3, ranG3, cfm_rho_X01, cfm_rho_X23, cfm_rho_X45,
      cfm_add, cfm_ub_mask, CharTwo.add_self_eq_zero, -Representation.exteriorPower_apply]

private theorem model3_F_ranPre_3 : (rho K (tInv3 K) - 1) (ranPre3 K 3) = ranG3 K 3 := by
  rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_iff_eq_add, rho_tInv3,
    Module.End.mul_apply, Module.End.mul_apply]
  apply cfm_ext3
  intro m hm hc
  rcases exists_mask3 hm hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [ranPre3, ranG3, cfm_rho_X01, cfm_rho_X23, cfm_rho_X45,
      cfm_add, cfm_ub_mask, CharTwo.add_self_eq_zero, -Representation.exteriorPower_apply]

private theorem model3_F_ranPre_4 : (rho K (tInv3 K) - 1) (ranPre3 K 4) = ranG3 K 4 := by
  rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_iff_eq_add, rho_tInv3,
    Module.End.mul_apply, Module.End.mul_apply]
  apply cfm_ext3
  intro m hm hc
  rcases exists_mask3 hm hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [ranPre3, ranG3, cfm_rho_X01, cfm_rho_X23, cfm_rho_X45,
      cfm_add, cfm_ub_mask, CharTwo.add_self_eq_zero, -Representation.exteriorPower_apply]

private theorem model3_F_ranPre_5 : (rho K (tInv3 K) - 1) (ranPre3 K 5) = ranG3 K 5 := by
  rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_iff_eq_add, rho_tInv3,
    Module.End.mul_apply, Module.End.mul_apply]
  apply cfm_ext3
  intro m hm hc
  rcases exists_mask3 hm hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [ranPre3, ranG3, cfm_rho_X01, cfm_rho_X23, cfm_rho_X45,
      cfm_add, cfm_ub_mask, CharTwo.add_self_eq_zero, -Representation.exteriorPower_apply]

private theorem model3_F_ranPre_6 : (rho K (tInv3 K) - 1) (ranPre3 K 6) = ranG3 K 6 := by
  rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_iff_eq_add, rho_tInv3,
    Module.End.mul_apply, Module.End.mul_apply]
  apply cfm_ext3
  intro m hm hc
  rcases exists_mask3 hm hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [ranPre3, ranG3, cfm_rho_X01, cfm_rho_X23, cfm_rho_X45,
      cfm_add, cfm_ub_mask, CharTwo.add_self_eq_zero, -Representation.exteriorPower_apply]

private theorem model3_F_ranPre_7 : (rho K (tInv3 K) - 1) (ranPre3 K 7) = ranG3 K 7 := by
  rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_iff_eq_add, rho_tInv3,
    Module.End.mul_apply, Module.End.mul_apply]
  apply cfm_ext3
  intro m hm hc
  rcases exists_mask3 hm hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [ranPre3, ranG3, cfm_rho_X01, cfm_rho_X23, cfm_rho_X45,
      cfm_add, cfm_ub_mask, CharTwo.add_self_eq_zero, -Representation.exteriorPower_apply]

private theorem model3_F_ranPre_8 : (rho K (tInv3 K) - 1) (ranPre3 K 8) = ranG3 K 8 := by
  rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_iff_eq_add, rho_tInv3,
    Module.End.mul_apply, Module.End.mul_apply]
  apply cfm_ext3
  intro m hm hc
  rcases exists_mask3 hm hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [ranPre3, ranG3, cfm_rho_X01, cfm_rho_X23, cfm_rho_X45,
      cfm_add, cfm_ub_mask, CharTwo.add_self_eq_zero, -Representation.exteriorPower_apply]

private theorem model3_F_ranPre_9 : (rho K (tInv3 K) - 1) (ranPre3 K 9) = ranG3 K 9 := by
  rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_iff_eq_add, rho_tInv3,
    Module.End.mul_apply, Module.End.mul_apply]
  apply cfm_ext3
  intro m hm hc
  rcases exists_mask3 hm hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [ranPre3, ranG3, cfm_rho_X01, cfm_rho_X23, cfm_rho_X45,
      cfm_add, cfm_ub_mask, CharTwo.add_self_eq_zero, -Representation.exteriorPower_apply]

theorem model3_F_ranPre (i : Fin 10) : (rho K (tInv3 K) - 1) (ranPre3 K i) = ranG3 K i := by
  fin_cases i
  exacts [model3_F_ranPre_0, model3_F_ranPre_1, model3_F_ranPre_2, model3_F_ranPre_3,
    model3_F_ranPre_4, model3_F_ranPre_5, model3_F_ranPre_6, model3_F_ranPre_7,
    model3_F_ranPre_8, model3_F_ranPre_9]

private theorem model3_neg_eq_self (x : Cube K) : -x = x := by
  have h2 : (2 : K) • x = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
  rw [two_smul] at h2
  exact neg_eq_of_add_eq_zero_left h2

private theorem model3_sq_pair {G : Type*} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) : x * y * (x * y) = 1 := by
  calc x * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
    _ = x * (x * y) * y := by rw [← hxy]
    _ = x * x * (y * y) := by simp only [mul_assoc]
    _ = 1 := by rw [hx, hy, one_mul]

private theorem model3_sq_triple {G : Type*} [Group G] {a b c : G} (ha : a * a = 1)
    (hb : b * b = 1) (hc : c * c = 1) (hab : a * b = b * a) (hac : a * c = c * a)
    (hbc : b * c = c * b) : a * b * c * (a * b * c) = 1 := by
  have hp : a * b * (a * b) = 1 := model3_sq_pair ha hb hab
  have hpc : a * b * c = c * (a * b) := by
    rw [← mul_assoc c a b, ← hac, mul_assoc a c b, ← hbc, mul_assoc a b c]
  exact model3_sq_pair hp hc hpc

private theorem model3_tInv3_mul_self : tInv3 K * tInv3 K = 1 := by
  have h2 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two, CharTwo.two_eq_zero]
  have hz : ∀ (i j : Fin 6) (hij : i ≠ j), transvGL K i j hij 0 = 1 := by
    intro i j hij
    apply Units.ext
    simp only [transvGL_val, Matrix.transvection_zero, Units.val_one]
  have hsq : ∀ (i j : Fin 6) (hij : i ≠ j), transvGL K i j hij 1 * transvGL K i j hij 1 = 1 := by
    intro i j hij
    rw [transvGL_mul_same, h2, hz]
  unfold tInv3 tInv2 tInv1
  exact model3_sq_triple (hsq 0 1 (by decide)) (hsq 2 3 (by decide)) (hsq 4 5 (by decide))
    (transvGL_commute 0 1 2 3 (by decide) (by decide) (by decide) (by decide) 1 1)
    (transvGL_commute 0 1 4 5 (by decide) (by decide) (by decide) (by decide) 1 1)
    (transvGL_commute 2 3 4 5 (by decide) (by decide) (by decide) (by decide) 1 1)

private theorem model3_range_le_ker :
    LinearMap.range (rho K (tInv3 K) - 1) ≤ LinearMap.ker (rho K (tInv3 K) - 1) :=
  range_le_ker_of_mul_self model3_tInv3_mul_self

theorem model3_finrank_range :
    10 ≤ Module.finrank K (LinearMap.range (rho K (tInv3 K) - 1)) := by
  have hli : LinearIndependent K (ranG3 K) :=
    linearIndependent_of_pivots_mask _ ranP3 ranP3_card ranG3_pivots
  have hr : Submodule.span K (Set.range (ranG3 K)) ≤ LinearMap.range (rho K (tInv3 K) - 1) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨ranPre3 K i, model3_F_ranPre i⟩
  have fr : Module.finrank K (Submodule.span K (Set.range (ranG3 K))) = 10 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hm : Module.finrank K (Submodule.span K (Set.range (ranG3 K))) ≤
      Module.finrank K (LinearMap.range (rho K (tInv3 K) - 1)) := Submodule.finrank_mono hr
  omega

theorem model3_CR :
    LinearMap.ker (rho K (tInv3 K) - 1) ≤ LinearMap.range (rho K (tInv3 K) - 1) := by
  have hrk := model3_range_le_ker (K := K)
  have hge := model3_finrank_range (K := K)
  have hle : Module.finrank K (LinearMap.range (rho K (tInv3 K) - 1)) ≤
      Module.finrank K (LinearMap.ker (rho K (tInv3 K) - 1)) := Submodule.finrank_mono hrk
  have rn := LinearMap.finrank_range_add_finrank_ker (rho K (tInv3 K) - 1)
  rw [finrank_cube] at rn
  have heq : LinearMap.range (rho K (tInv3 K) - 1) = LinearMap.ker (rho K (tInv3 K) - 1) :=
    Submodule.eq_of_le_of_finrank_le hrk (by omega)
  exact heq.ge

private theorem model3_beta_ub_zero {a b d p q r : Fin 6} (hab : a < b) (hbd : b < d)
    (hpq : p < q) (hqr : q < r) (h : ¬ Disjoint ({a, b, d} : Finset (Fin 6)) {p, q, r}) :
    beta K (ub K a b d hab hbd) (ub K p q r hpq hqr) = 0 := by
  unfold ub
  exact beta_cubeBasis_of_not_disjoint h

private theorem model3_beta_ub_ne_zero {a b d p q r : Fin 6} (hab : a < b) (hbd : b < d)
    (hpq : p < q) (hqr : q < r) (h : Disjoint ({a, b, d} : Finset (Fin 6)) {p, q, r}) :
    beta K (ub K a b d hab hbd) (ub K p q r hpq hqr) ≠ 0 := by
  unfold ub
  exact beta_cubeBasis_ne_zero_of_disjoint h

theorem model3_rho_ub135 : rho K (tInv3 K) (ub K 1 3 5) = ub K 1 3 5 + ub K 0 2 4 + ub K 0 2 5 +
    ub K 0 3 4 + ub K 0 3 5 + ub K 1 2 4 + ub K 1 2 5 + ub K 1 3 4 := by
  rw [rho_tInv3, Module.End.mul_apply, Module.End.mul_apply]
  apply cfm_ext3
  intro m hm hc
  rcases exists_mask3 hm hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [cfm_rho_X01, cfm_rho_X23, cfm_rho_X45, cfm_add,
      cfm_ub_mask, CharTwo.add_self_eq_zero, -Representation.exteriorPower_apply]

theorem model3_beta_ne : ∃ p₁ p₂ : Cube K, IsPure K p₁ ∧ IsPure K p₂ ∧
    p₁ + p₂ ∈ LinearMap.range (rho K (tInv3 K) - 1) ∧ beta K p₁ p₂ ≠ 0 := by
  have hpure : IsPure K (ub K 1 3 5) := isPure_cubeBasis _
  refine ⟨rho K (tInv3 K) (ub K 1 3 5), ub K 1 3 5, hpure.rho _, hpure, ⟨ub K 1 3 5, ?_⟩, ?_⟩
  · rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_add_neg, model3_neg_eq_self]
  · have z1 : beta K (ub K 1 3 5) (ub K 1 3 5) = 0 :=
      model3_beta_ub_zero (by decide) (by decide) (by decide) (by decide) (by decide)
    have z2 : beta K (ub K 0 2 5) (ub K 1 3 5) = 0 :=
      model3_beta_ub_zero (by decide) (by decide) (by decide) (by decide) (by decide)
    have z3 : beta K (ub K 0 3 4) (ub K 1 3 5) = 0 :=
      model3_beta_ub_zero (by decide) (by decide) (by decide) (by decide) (by decide)
    have z4 : beta K (ub K 0 3 5) (ub K 1 3 5) = 0 :=
      model3_beta_ub_zero (by decide) (by decide) (by decide) (by decide) (by decide)
    have z5 : beta K (ub K 1 2 4) (ub K 1 3 5) = 0 :=
      model3_beta_ub_zero (by decide) (by decide) (by decide) (by decide) (by decide)
    have z6 : beta K (ub K 1 2 5) (ub K 1 3 5) = 0 :=
      model3_beta_ub_zero (by decide) (by decide) (by decide) (by decide) (by decide)
    have z7 : beta K (ub K 1 3 4) (ub K 1 3 5) = 0 :=
      model3_beta_ub_zero (by decide) (by decide) (by decide) (by decide) (by decide)
    have hne : beta K (ub K 0 2 4) (ub K 1 3 5) ≠ 0 :=
      model3_beta_ub_ne_zero (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [model3_rho_ub135]
    simp only [map_add, LinearMap.add_apply, z1, z2, z3, z4, z5, z6, z7, zero_add, add_zero]
    exact hne

theorem involModel3_t3 : InvolModel3 K (tInv3 K) where
  CR := model3_CR
  beta_ne := model3_beta_ne

end Model3

end CFSG.RankThree.GF2n.Smith81.A5Cube
