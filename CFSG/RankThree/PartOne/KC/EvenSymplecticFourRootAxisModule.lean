module

public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisNormalizer
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.RankThree.PartOne

namespace KCRootAxis

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b

variable {K : Type} [Field K] [CharP K 2]

theorem sl2_center_eq_bot : Subgroup.center (SL₂ K) = ⊥ := by
  refine eq_bot_iff.mpr fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h5 : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
  have hr1 : r = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h5)
  subst hr1
  rw [Subgroup.mem_bot]
  ext i j
  have := congrFun (congrFun hrA i) j
  simpa [Matrix.scalar_apply, Matrix.one_apply] using this.symm

theorem sl2_isSimpleGroup (h4 : 4 ≤ Nat.card K) : IsSimpleGroup (SL₂ K) := by
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have e : SL₂ K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq sl2_center_eq_bot.symm)
  exact e.isSimpleGroup

omit [CharP K 2] in
theorem sl2_isPerfect (h4 : 4 ≤ Nat.card K) : Group.IsPerfect (SL₂ K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  refine CFSG.LinearGroups.special_linear_dimension_two_perfect ?_
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
  exact ⟨s, hs⟩

theorem sl2_pCore_eq_bot [Finite K] (h4 : 4 ≤ Nat.card K) : CFSG.pCore 2 (SL₂ K) = ⊥ := by
  have := sl2_isSimpleGroup h4
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 (SL₂ K)) with h | h
  · exact h
  · exfalso
    have hp : IsPGroup 2 (SL₂ K) := by
      have := CFSG.pCore_isPGroup (p := 2) (G := SL₂ K)
      rw [h] at this
      exact this.of_equiv Subgroup.topEquiv
    have hnil : Group.IsNilpotent (SL₂ K) := hp.isNilpotent
    have hsolv : Group.IsSolvable (SL₂ K) := inferInstance
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (SL₂ K)
    rw [(sl2_isPerfect h4).commutator_eq_top] at hlt
    exact lt_irrefl _ hlt

omit [CharP K 2] in
theorem exists_sl2_mulVec_eq {v w : Fin 2 → K} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ M : SL₂ K, (M : Matrix (Fin 2) (Fin 2) K) *ᵥ v = w := by
  have key : ∀ u : Fin 2 → K, u ≠ 0 →
      ∃ M : SL₂ K, (M : Matrix (Fin 2) (Fin 2) K) *ᵥ ![1, 0] = u := by
    intro u hu
    by_cases h0 : u 0 = 0
    · have h1 : u 1 ≠ 0 := by
        intro h1
        exact hu (funext fun i => by fin_cases i <;> simp [h0, h1])
      refine ⟨⟨!![0, -(u 1)⁻¹; u 1, 0], by
        rw [Matrix.det_fin_two]; simp [h1]⟩, ?_⟩
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, h0]
    · refine ⟨⟨!![u 0, 0; u 1, (u 0)⁻¹], by
        rw [Matrix.det_fin_two]; simp [h0]⟩, ?_⟩
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct]
  obtain ⟨M, hM⟩ := key v hv
  obtain ⟨N, hN⟩ := key w hw
  refine ⟨N * M⁻¹, ?_⟩
  have h1 : ((M⁻¹ : SL₂ K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![1, 0] := by
    rw [← hM, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, h1, hN]

@[expose] def vecOf₂ (z : antiSp K) : Fin 2 → K :=
  ![mat z 0 2, mat z 0 1]

theorem vecOf₂_aElt (v : Fin 2 → K) (c : K) : vecOf₂ (aElt v c) = v := by
  ext i
  fin_cases i <;> simp [vecOf₂, mat, glMat_aElt, uMat]

theorem vecOf₂_mul {z w : antiSp K} (hz : z ∈ radA2 K) (hw : w ∈ radA2 K) :
    vecOf₂ (z * w) = vecOf₂ z + vecOf₂ w := by
  obtain ⟨v, c, rfl⟩ := mem_radA2_iff.mp hz
  obtain ⟨v', c', rfl⟩ := mem_radA2_iff.mp hw
  rw [aElt_mul, vecOf₂_aElt, vecOf₂_aElt, vecOf₂_aElt]

theorem vecOf₂_eq_zero_iff {z : antiSp K} (hz : z ∈ radA2 K) : vecOf₂ z = 0 ↔ z ∈ rootU₂ K := by
  obtain ⟨v, c, rfl⟩ := mem_radA2_iff.mp hz
  rw [vecOf₂_aElt]
  constructor
  · rintro rfl
    exact aElt_zero_mem_rootU₂ c
  · rintro ⟨c', hc'⟩
    have h := uElt_inj hc'
    ext i
    fin_cases i
    · exact h.2.1
    · exact h.1

theorem exists_vecOf₂_eq (v : Fin 2 → K) : ∃ z ∈ radA2 K, vecOf₂ z = v :=
  ⟨aElt v 0, aElt_mem_radA2 v 0, vecOf₂_aElt v 0⟩

theorem vecOf₂_conj (M : SL₂ K) {z : antiSp K} (hz : z ∈ radA2 K) :
    vecOf₂ (sElt M * z * (sElt M)⁻¹) = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ vecOf₂ z := by
  obtain ⟨v, c, rfl⟩ := mem_radA2_iff.mp hz
  rw [sElt_mul_aElt, mul_inv_cancel_right, vecOf₂_aElt, vecOf₂_aElt]

end KCRootAxis

end CFSG.RankThree.PartOne
