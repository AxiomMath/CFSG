module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2NatA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2LinC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

variable {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)} {t : MulAut W}

theorem w135c2_nat_ineq (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (hW : ∀ w : W, w ^ 2 = 1) {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} (hreal : (FFModel.nat Γ).Realizes L ⊤ ⊥)
    {a : ℕ} (ha : Nat.card K = 2 ^ a) : a ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  classical
  have hirr : IsIrrOn L ⊤ ⊥ := hctx.2.2.2.2.2
  have hQ : IsQuasisimple ↥L := hctx.2.2.2.2.1
  have hnab : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a := by
    obtain ⟨-, -, x, y, hxy⟩ := hQ
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨x', x'.2, y', y'.2, fun h => hxy ?_⟩
    have hL : (x' * y' : ↥L) = y' * x' := Subtype.ext h
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hL]
  have htN : ∀ g ∈ L, t * g * t⁻¹ ∈ L := by
    intro g hg
    have hLY : L ≤ Y := hctx.2.2.1
    have hmem := (w135_normal_of_ctx hctx).conj_mem
      (⟨g, hLY hg⟩ : ↥Y) (Subgroup.mem_subgroupOf.mpr hg) (⟨t, htY⟩ : ↥Y)
    simpa using (Subgroup.mem_subgroupOf.mp hmem)
  obtain ⟨k, d, hk1, hk, hrk, hcase⟩ := w135c2_dichotomy hW hirr htN ht2
  obtain ⟨hKE, hcardW⟩ := w135c2_natural_data hirr hreal
  have hk2 : a ≤ k := by
    have h : 2 ^ a ≤ 2 ^ k := by
      rw [← ha, ← hk]
      exact hKE
    exact (Nat.pow_le_pow_iff_right (show 1 < 2 by norm_num)).mp h
  have hc : 2 ≤ Fintype.card ι := w135c2_two_le_card_index hreal hnab
  have hrkW : rk W = a * Fintype.card ι := by
    refine Nat.pow_right_injective (show 2 ≤ 2 by norm_num) ?_
    change 2 ^ rk W = 2 ^ (a * Fintype.card ι)
    rw [← w135_card_eq_two_pow_rk hW, hcardW, ha, ← pow_mul]
  rcases hcase with ⟨r, hr1, hr⟩ | ⟨-, hsem⟩
  ·
    have hkm : k ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
      rw [hr]
      calc k = k * 1 := (mul_one k).symm
        _ ≤ k * r := Nat.mul_le_mul_left k hr1
    exact hk2.trans hkm
  ·
    have heq : a * Fintype.card ι = 2 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
      rw [← hrkW, hsem]
    have h2 : a * 2 ≤ 2 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
      calc a * 2 ≤ a * Fintype.card ι := Nat.mul_le_mul_left a hc
        _ = 2 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := heq
    have h3 : 2 * a ≤ 2 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
      simpa [mul_comm] using h2
    exact Nat.le_of_mul_le_mul_left h3 Nat.two_pos

theorem w135c2_natural (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (hW : ∀ w : W, w ^ 2 = 1) (hnat : Chev2Natural W L) : W4Lem13_5Concl W Y L t := by
  classical
  unfold Chev2Natural at hnat
  unfold W4Lem13_5Concl
  rcases hnat with ⟨n, a, hcase⟩ | ⟨n, hSU, hNatSU⟩
  · rcases hcase with hSL | hSp | hOP | hOM
    ·
      obtain ⟨hIs, K, hKfield, hKfin, hKa, hreal⟩ := hSL
      exact Or.inl ⟨n, a, w135c2_nat_ineq hctx htY ht2 hW hreal hKa,
        Or.inl ⟨hIs, K, hKfield, hKfin, hKa, hreal⟩⟩
    ·
      obtain ⟨hIs, hEven, K, hKfield, hKfin, hKa, hreal⟩ := hSp
      exact Or.inl ⟨n, a, w135c2_nat_ineq hctx htY ht2 hW hreal hKa,
        Or.inr (Or.inl ⟨hIs, hEven, K, hKfield, hKfin, hKa, hreal⟩)⟩
    ·
      obtain ⟨hIs, hEven, K, hKfield, hKfin, hKa, hreal⟩ := hOP
      exact Or.inl ⟨n, a, w135c2_nat_ineq hctx htY ht2 hW hreal hKa,
        Or.inr (Or.inr (Or.inl ⟨hIs, hEven, K, hKfield, hKfin, hKa, hreal⟩))⟩
    ·
      obtain ⟨hIs, hEven, K, hKfield, hKfin, b, c, hKa, hquad, hreal⟩ := hOM
      exact Or.inl ⟨n, a, w135c2_nat_ineq hctx htY ht2 hW hreal hKa,
        Or.inr (Or.inr (Or.inr
          ⟨hIs, hEven, K, hKfield, hKfin, b, c, hKa, hquad, hreal⟩))⟩
  ·
    exact Or.inr (Or.inl ⟨n, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hSU, hNatSU⟩))))⟩)

end CFSG.LocalAnalysis.WeakClosure81
