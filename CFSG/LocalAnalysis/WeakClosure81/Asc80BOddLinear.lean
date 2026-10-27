module

import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddL2Gen
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
import CFSG.Quasithin.Vol2.Ch10SecKGA318
import CFSG.Quasithin.Vol2.Ch11SecOE5B

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix Subgroup CFSG.Open

namespace LinSeitz

section Field

variable {F : Type} [Field F] {n : ℕ}

theorem eigen_step {M : Matrix (Fin n) (Fin n) F} {s : F} (hM : M * M = (s * s) • 1)
    (hM1 : M ≠ s • 1) (hM2 : M ≠ (-s) • 1) :
    ∃ W : Submodule F (Fin n → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ N : Matrix (Fin n) (Fin n) F, N * M = M * N → ∀ w ∈ W, N *ᵥ w ∈ W := by
  refine ⟨LinearMap.ker (toLin' (M - s • 1)), ?_, ?_, ?_⟩
  · intro hbot
    apply hM2
    have hinj : Function.Injective (toLin' (M - s • 1)) := LinearMap.ker_eq_bot.mp hbot
    have hprod : (M - s • 1) * (M + s • 1) = 0 := by
      rw [sub_mul, mul_add, mul_add, hM, smul_mul_assoc, one_mul, mul_smul_comm, mul_one,
        smul_mul_assoc, one_mul, smul_smul]
      abel
    have : M + s • 1 = 0 := by
      ext i j
      have h := congrArg (fun A => A *ᵥ Pi.single j 1) hprod
      simp only [← mulVec_mulVec, zero_mulVec] at h
      have h2 := hinj (h.trans (map_zero (toLin' (M - s • 1))).symm)
      have := congrFun h2 i
      simpa [mulVec_single] using this
    rw [show (-s) • (1 : Matrix (Fin n) (Fin n) F) = -(s • 1) by rw [neg_smul]]
    exact eq_neg_of_add_eq_zero_left this
  · intro htop
    apply hM1
    have : M - s • 1 = 0 := by
      ext i j
      have h : Pi.single j 1 ∈ LinearMap.ker (toLin' (M - s • 1)) := htop ▸ Submodule.mem_top
      rw [LinearMap.mem_ker, toLin'_apply] at h
      have := congrFun h i
      simpa [mulVec_single] using this
    exact sub_eq_zero.mp this
  · intro N hN w hw
    rw [LinearMap.mem_ker, toLin'_apply] at hw ⊢
    have h1 : (M - s • 1) * N = N * (M - s • 1) := by
      rw [sub_mul, mul_sub, ← hN, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
    rw [mulVec_mulVec, h1, ← mulVec_mulVec, hw, mulVec_zero]

theorem isSquare_or_of_ne_zero [Fintype F] {a b : F} (ha : a ≠ 0)
    (hb : b ≠ 0) : IsSquare a ∨ IsSquare b ∨ IsSquare (a * b) := by
  classical
  by_cases hA : IsSquare a
  · exact Or.inl hA
  by_cases hB : IsSquare b
  · exact Or.inr (Or.inl hB)
  right; right
  have h1 := quadraticChar_neg_one_iff_not_isSquare.mpr hA
  have h2 := quadraticChar_neg_one_iff_not_isSquare.mpr hB
  have h3 : quadraticChar F (a * b) = 1 := by rw [map_mul, h1, h2]; norm_num
  exact (quadraticChar_one_iff_isSquare (mul_ne_zero ha hb)).mp h3

theorem exists_invariant_of_pair [Fintype F] (hF : ringChar F ≠ 2) (hn : 3 ≤ n)
    {X Y : Matrix (Fin n) (Fin n) F} {a b c : F} (hXX : X * X = a • 1) (hYY : Y * Y = b • 1)
    (hXY : X * Y = c • (Y * X)) (hc : c = 1 ∨ c = -1) (ha : a ≠ 0) (hb : b ≠ 0)
    (hXs : ∀ r : F, X ≠ r • 1) (hYs : ∀ r : F, Y ≠ r • 1) (hXYs : ∀ r : F, X * Y ≠ r • 1) :
    ∃ W : Submodule F (Fin n → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      (∀ w ∈ W, X *ᵥ w ∈ W) ∧ (∀ w ∈ W, Y *ᵥ w ∈ W) := by
  rcases hc with rfl | rfl
  ·
    rw [one_smul] at hXY
    rcases isSquare_or_of_ne_zero ha hb with ⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, hs⟩
    · obtain ⟨W, h0, ht, hN⟩ := eigen_step hXX (hXs s) (hXs (-s))
      exact ⟨W, h0, ht, hN X rfl, hN Y hXY.symm⟩
    · obtain ⟨W, h0, ht, hN⟩ := eigen_step hYY (hYs s) (hYs (-s))
      exact ⟨W, h0, ht, hN X hXY, hN Y rfl⟩
    · have hM : (X * Y) * (X * Y) = (s * s) • 1 := by
        rw [← hs, show X * Y * (X * Y) = (X * X) * (Y * Y) by
          rw [mul_assoc, ← mul_assoc Y X Y, ← hXY, mul_assoc, mul_assoc], hXX, hYY,
          smul_mul_assoc, one_mul, smul_smul]
      obtain ⟨W, h0, ht, hN⟩ := eigen_step hM (hXYs s) (hXYs (-s))
      refine ⟨W, h0, ht, hN X ?_, hN Y ?_⟩
      · rw [mul_assoc X Y X, ← hXY]
      · rw [← mul_assoc, ← hXY]
  ·
    have hXY' : X * Y + Y * X = 0 := by rw [hXY, neg_smul, one_smul, neg_add_cancel]
    obtain ⟨l, m, hlm⟩ := FiniteField.exists_root_sum_quadratic
      (f := Polynomial.C a * Polynomial.X ^ 2)
      (g := Polynomial.C b * Polynomial.X ^ 2 + Polynomial.C (-1))
      (by rw [Polynomial.degree_C_mul_X_pow 2 ha]; rfl)
      (by
        rw [Polynomial.degree_add_C (by rw [Polynomial.degree_C_mul_X_pow 2 hb]; decide),
          Polynomial.degree_C_mul_X_pow 2 hb]; rfl)
      (FiniteField.odd_card_of_char_ne_two hF)
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_add] at hlm
    have hlm' : a * l ^ 2 + b * m ^ 2 = 1 := by linear_combination hlm
    have hYX : Y * X = -(X * Y) := eq_neg_of_add_eq_zero_right hXY'
    have comb : ∀ (p q r t : F), (p • X + q • Y) * (r • X + t • Y) =
        (p * r * a + q * t * b) • 1 + (p * t - q * r) • (X * Y) := by
      intro p q r t
      simp only [add_mul, mul_add, smul_mul_smul_comm, hXX, hYY, hYX, smul_neg, smul_smul,
        sub_smul, add_smul]
      abel
    set U := l • X + m • Y with hU
    set V := (m * b) • X + (-(l * a)) • Y with hV
    have hUU : U * U = 1 := by
      rw [hU, comb]
      have : l * l * a + m * m * b = 1 := by linear_combination hlm'
      rw [this, show l * m - m * l = 0 by ring, zero_smul, add_zero, one_smul]
    have hUV : U * V = -(X * Y) := by
      rw [hU, hV, comb]
      have h1 : l * (m * b) * a + m * -(l * a) * b = 0 := by ring
      have h2 : l * -(l * a) - m * (m * b) = -1 := by linear_combination -hlm'
      rw [h1, h2, zero_smul, zero_add, neg_one_smul]
    have hVU : V * U = X * Y := by
      rw [hU, hV, comb]
      have h1 : m * b * l * a + -(l * a) * m * b = 0 := by ring
      have h2 : m * b * m - -(l * a) * l = 1 := by linear_combination hlm'
      rw [h1, h2, zero_smul, zero_add, one_smul]
    have hVV : V * V = (a * b) • 1 := by
      rw [hV, comb]
      have h1 : m * b * (m * b) * a + -(l * a) * -(l * a) * b = a * b := by
        linear_combination (a * b) * hlm'
      rw [h1, show m * b * -(l * a) - -(l * a) * (m * b) = 0 by ring, zero_smul, add_zero]
    have hU1 : U ≠ -1 := by
      intro h
      have : U * V = V * U := by rw [h, neg_one_mul, mul_neg_one]
      rw [hUV, hVU] at this
      have h2 : (2 : F) • (X * Y) = 0 := by
        rw [two_smul]
        nth_rw 1 [← this]
        exact neg_add_cancel _
      have h20 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
      apply hXYs 0
      rw [zero_smul]
      exact (smul_eq_zero.mp h2).resolve_left h20
    obtain ⟨v, hv0, hUv⟩ : ∃ v : Fin n → F, v ≠ 0 ∧ U *ᵥ v = v := by
      have hN : U + 1 ≠ 0 := fun h => hU1 (eq_neg_of_add_eq_zero_left h)
      obtain ⟨j, hj⟩ : ∃ j, (U + 1) *ᵥ Pi.single j 1 ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hN
        ext i j
        have := congrFun (hall j) i
        simpa [mulVec_single] using this
      refine ⟨(U + 1) *ᵥ Pi.single j 1, hj, ?_⟩
      rw [mulVec_mulVec, mul_add, hUU, mul_one, add_comm]
    set W := Submodule.span F ({v, V *ᵥ v} : Set (Fin n → F))
    have hWU : ∀ w ∈ W, U *ᵥ w ∈ W := by
      intro w hw
      obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hw
      rw [mulVec_add, mulVec_smul, mulVec_smul, hUv, mulVec_mulVec, hUV, ← hVU, neg_mulVec,
        ← mulVec_mulVec, hUv, smul_neg]
      exact W.add_mem (W.smul_mem _ (Submodule.subset_span (by simp)))
        (W.neg_mem (W.smul_mem _ (Submodule.subset_span (by simp))))
    have hWV : ∀ w ∈ W, V *ᵥ w ∈ W := by
      intro w hw
      obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hw
      rw [mulVec_add, mulVec_smul, mulVec_smul, mulVec_mulVec, hVV, smul_mulVec,
        one_mulVec]
      exact W.add_mem (W.smul_mem _ (Submodule.subset_span (by simp)))
        (W.smul_mem _ (W.smul_mem _ (Submodule.subset_span (by simp))))
    have hXUV : X = (l * a) • U + m • V := by
      rw [hU, hV, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
      have : (l * a * l + m * (m * b)) = 1 := by linear_combination hlm'
      rw [show (l * a * l) • X + (l * a * m) • Y + ((m * (m * b)) • X + (m * -(l * a)) • Y) =
        (l * a * l + m * (m * b)) • X + (l * a * m + m * -(l * a)) • Y by
          rw [add_smul, add_smul]; abel, this, show l * a * m + m * -(l * a) = 0 by ring,
        zero_smul, add_zero, one_smul]
    have hYUV : Y = (m * b) • U + (-l) • V := by
      rw [hU, hV, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
      have : m * b * m + -l * -(l * a) = 1 := by linear_combination hlm'
      rw [show (m * b * l) • X + (m * b * m) • Y + ((-l * (m * b)) • X + (-l * -(l * a)) • Y) =
        (m * b * l + -l * (m * b)) • X + (m * b * m + -l * -(l * a)) • Y by
          rw [add_smul, add_smul]; abel, this, show m * b * l + -l * (m * b) = 0 by ring,
        zero_smul, zero_add, one_smul]
    have hcomb : ∀ (r t : F), ∀ w ∈ W, (r • U + t • V) *ᵥ w ∈ W := by
      intro r t w hw
      rw [add_mulVec, smul_mulVec, smul_mulVec]
      exact W.add_mem (W.smul_mem _ (hWU w hw)) (W.smul_mem _ (hWV w hw))
    refine ⟨W, ?_, ?_, ?_, ?_⟩
    · intro h
      apply hv0
      have : v ∈ W := Submodule.subset_span (by simp)
      rw [h] at this
      exact (Submodule.mem_bot F).mp this
    · intro h
      have h1 : Module.finrank F W ≤ 2 := by
        classical
        have := finrank_span_finset_le_card (R := F) ({v, V *ᵥ v} : Finset (Fin n → F))
        rw [Finset.coe_insert, Finset.coe_singleton] at this
        exact this.trans (Finset.card_insert_le _ _)
      rw [h, finrank_top, Module.finrank_fin_fun] at h1
      omega
    · intro w hw; rw [hXUV]; exact hcomb _ _ w hw
    · intro w hw; rw [hYUV]; exact hcomb _ _ w hw

end Field

variable {F : Type} [Field F] [Finite F] {n : ℕ}

end LinSeitz

end CFSG.LocalAnalysis.WeakClosure81
