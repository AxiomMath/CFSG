module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveWeylFiveProj
import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinates
import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Matrix CFSG.Open
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.PartOne.KCOrthogonalAut
open CFSG.ClassicalGroups.Orthogonal

private theorem scalar_mulVec {K : Type} [Field K] {d : ℕ} (c : Kˣ) (v : Fin d → K) :
    (GeneralLinearGroup.scalar (Fin d) c : Matrix (Fin d) (Fin d) K) *ᵥ v = (c : K) • v := by
  funext i
  rw [Matrix.mulVec, dotProduct, Pi.smul_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · intro hi
    simp at hi

private theorem polarBilin_isometry {K : Type} [Field K] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {A : GL (Fin d) K}
    (hA : ∀ v, Q (matrixLinearEquiv A v) = Q v) :
    ∀ v w, Q.polarBilin (matrixLinearEquiv A v) (matrixLinearEquiv A w) = Q.polarBilin v w := by
  intro v w
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  rw [← map_add (matrixLinearEquiv A) v w, hA, hA, hA]

private theorem transpose_mul_toMatrix'_mul {K : Type} [Field K] {d : ℕ}
    {B : LinearMap.BilinForm K (Fin d → K)} {A : GL (Fin d) K}
    (hA : ∀ v w, B (matrixLinearEquiv A v) (matrixLinearEquiv A w) = B v w) :
    (A : Matrix (Fin d) (Fin d) K)ᵀ * B.toMatrix' * A = B.toMatrix' := by
  have hcol : ∀ i : Fin d, matrixLinearEquiv A (Pi.single i 1) = fun p => A p i := by
    intro i
    funext p
    rw [matrixLinearEquiv_apply, Matrix.mulVec_single_one, Matrix.col_apply]
  ext i j
  calc ((A : Matrix (Fin d) (Fin d) K)ᵀ * B.toMatrix' * (A : Matrix (Fin d) (Fin d) K)) i j
      = ∑ l, ∑ k, (A : Matrix (Fin d) (Fin d) K) l i * B.toMatrix' l k *
          (A : Matrix (Fin d) (Fin d) K) k j := by
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, mul_assoc]
        rw [Finset.sum_comm]
    _ = B (matrixLinearEquiv A (Pi.single i 1)) (matrixLinearEquiv A (Pi.single j 1)) := by
        conv_rhs => rw [← Matrix.toBilin'_toMatrix' B]
        rw [Matrix.toBilin'_apply]
        simp only [hcol]
    _ = B (Pi.single i 1) (Pi.single j 1) := hA _ _
    _ = B.toMatrix' i j := by rw [LinearMap.BilinForm.toMatrix'_apply]

private theorem scalar_isometry_eq_one {K : Type} [Field K] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {v : Fin d → K} (hv : Q v ≠ 0) {c : Kˣ}
    (hc : GeneralLinearGroup.scalar (Fin d) c ∈ matrixIsometries Q) (hc31 : c ^ 31 = 1) :
    c = 1 := by
  have h := (mem_matrixIsometries_iff Q _).mp hc v
  rw [matrixLinearEquiv_apply, scalar_mulVec, QuadraticMap.map_smul] at h
  have h' : (c : K) * (c : K) * Q v = Q v := by
    simpa [smul_eq_mul, mul_assoc] using h
  have hcc : (c : K) * (c : K) = 1 := by
    apply mul_right_cancel₀ hv
    rw [h']
    ring
  have hc2 : c ^ 2 = 1 := by
    rw [pow_two]
    apply Units.ext
    simp [hcc]
  have hgcd : orderOf c ∣ Nat.gcd 2 31 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc2) (orderOf_dvd_of_pow_eq_one hc31)
  have h1 : orderOf c = 1 := by
    rw [Nat.coprime_iff_gcd_eq_one.mp (by norm_num : Nat.Coprime 2 31)] at hgcd
    exact Nat.dvd_one.mp hgcd
  exact orderOf_eq_one_iff.mp h1

private theorem weylFivePower_coordinateQuadOdd {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn3 : 3 ≤ n) (hn : n ≤ 4) (h2 : ringChar K ≠ 2) (h31 : ringChar K ≠ 31) :
    WeylFivePower (matrixProjectiveDerived (coordinateQuadOdd n K)) := by
  have hprime : (ringChar K).Prime := CharP.char_is_prime K _
  have h2' : (2 : K) ≠ 0 := by
    rw [Ne, two_eq_zero_iff_ringChar_eq_two hprime]
    exact h2
  have hQ : (coordinateQuadOdd n K).polarBilin.Nondegenerate :=
    (regular_coordinateQuadOdd n K h2' hn3).1
  have hv : coordinateQuadOdd n K
      (Pi.single (oddIndexEquiv n (.inr (.inr ()))) 1) ≠ 0 := by
    have h1 : coordinateQuadOdd n K
        (Pi.single (oddIndexEquiv n (.inr (.inr ()))) 1) = 1 := by
      rw [coordinateQuadOdd_apply]
      simp [Pi.single_eq_same, Pi.single_eq_of_ne]
    rw [h1]
    exact one_ne_zero
  have hZ : ∀ c : Kˣ,
      GeneralLinearGroup.scalar (Fin (2 * n + 1)) c ∈ matrixDerived (coordinateQuadOdd n K) →
        c ^ 31 = 1 → c = 1 := by
    intro c hc hc31
    exact scalar_isometry_eq_one hv (matrixDerived_le_isometries _ hc) hc31
  have hdim : Fintype.card (Fin (2 * n + 1)) ≤ 4 ∨
      (Fintype.card (Fin (2 * n + 1)) ≤ 9 ∧ ∃ J : Matrix (Fin (2 * n + 1)) (Fin (2 * n + 1)) K,
        IsUnit J.det ∧ ∀ x ∈ matrixDerived (coordinateQuadOdd n K),
          (x : Matrix (Fin (2 * n + 1)) (Fin (2 * n + 1)) K)ᵀ * J * x = J) := by
    refine Or.inr ⟨by simp only [Fintype.card_fin]; omega,
      LinearMap.BilinForm.toMatrix' (coordinateQuadOdd n K).polarBilin, ?_, ?_⟩
    · have hJnd : (LinearMap.BilinForm.toMatrix'
          (coordinateQuadOdd n K).polarBilin).Nondegenerate := by
        apply (Matrix.nondegenerate_toBilin'_iff).mp
        simpa only [Matrix.toBilin'_toMatrix'] using hQ
      exact isUnit_iff_ne_zero.mpr (Matrix.nondegenerate_iff_det_ne_zero.mp hJnd)
    · intro x hx
      have hxiso : x ∈ matrixIsometries (coordinateQuadOdd n K) :=
        matrixDerived_le_isometries _ hx
      exact transpose_mul_toMatrix'_mul
        (polarBilin_isometry ((mem_matrixIsometries_iff _ x).mp hxiso))
  have hnf : ∀ α : MulAut (StatedProj (matrixDerived (coordinateQuadOdd n K))), α ^ 5 = 1 →
      ∃ (m : ℕ) (A : GL (Fin (2 * n + 1)) K) (σ : K ≃+* K), ¬ 5 ∣ m ∧
        ∃ θ : matrixDerived (coordinateQuadOdd n K) →*
            matrixDerived (coordinateQuadOdd n K),
          (∀ x : matrixDerived (coordinateQuadOdd n K),
            (θ x : GL (Fin (2 * n + 1)) K) = semilinConjGL A σ x) ∧
          ∀ x : matrixDerived (coordinateQuadOdd n K),
            (α ^ m) (QuotientGroup.mk x : StatedProj (matrixDerived (coordinateQuadOdd n K))) =
              QuotientGroup.mk (θ x) := by
    intro α _
    have htop : matrixProjectiveImage (coordinateQuadOdd n K) = ⊤ :=
      matrixProjectiveImage_eq_top_odd K n hn3 h2
    have hmem : α ∈ matrixProjectiveImage (coordinateQuadOdd n K) := by
      rw [htop]
      exact Subgroup.mem_top α
    obtain ⟨g, hg⟩ := (mem_matrixProjectiveImage_iff _ α).mp hmem
    refine ⟨1, g.val.left, g.val.right, by norm_num,
      (matrixDerivedConjugation _ g).toMonoidHom, ?_, ?_⟩
    · intro x
      exact matrixDerivedConjugation_val _ g x
    · intro x
      rw [pow_one, ← hg]
      exact matrixProjectiveConjugation_mk _ g x
  exact weylFivePower_statedProj (ι := Fin (2 * n + 1)) (K := K) h31
    (matrixDerived (coordinateQuadOdd n K)) hZ hdim hnf

private theorem weylFivePower_coordinateQuadMinus {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn4 : 4 ≤ n) (hn : n ≤ 4) (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (h31 : ringChar K ≠ 31) :
    WeylFivePower (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) := by
  have hn1 : 1 ≤ n := by omega
  have hQ : (coordinateQuadMinus n K hn1 b c).polarBilin.Nondegenerate :=
    (regular_coordinateQuadMinus n K b c hn4 hirr).1
  have hv : coordinateQuadMinus n K hn1 b c
      (Pi.single (minusIndexEquiv n hn1 (.inr (.inr 0))) 1) ≠ 0 := by
    have h1 : coordinateQuadMinus n K hn1 b c
        (Pi.single (minusIndexEquiv n hn1 (.inr (.inr 0))) 1) = 1 := by
      rw [coordinateQuadMinus_apply]
      simp [Pi.single_eq_same, Pi.single_eq_of_ne]
    rw [h1]
    exact one_ne_zero
  have hZ : ∀ c' : Kˣ,
      GeneralLinearGroup.scalar (Fin (2 * n)) c' ∈
          matrixDerived (coordinateQuadMinus n K hn1 b c) →
        c' ^ 31 = 1 → c' = 1 := by
    intro c' hc hc31
    exact scalar_isometry_eq_one hv (matrixDerived_le_isometries _ hc) hc31
  have hdim : Fintype.card (Fin (2 * n)) ≤ 4 ∨
      (Fintype.card (Fin (2 * n)) ≤ 9 ∧ ∃ J : Matrix (Fin (2 * n)) (Fin (2 * n)) K,
        IsUnit J.det ∧ ∀ x ∈ matrixDerived (coordinateQuadMinus n K hn1 b c),
          (x : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * J * x = J) := by
    refine Or.inr ⟨by simp only [Fintype.card_fin]; omega,
      LinearMap.BilinForm.toMatrix' (coordinateQuadMinus n K hn1 b c).polarBilin,
      ?_, ?_⟩
    · have hJnd : (LinearMap.BilinForm.toMatrix'
          (coordinateQuadMinus n K hn1 b c).polarBilin).Nondegenerate := by
        apply (Matrix.nondegenerate_toBilin'_iff).mp
        simpa only [Matrix.toBilin'_toMatrix'] using hQ
      exact isUnit_iff_ne_zero.mpr (Matrix.nondegenerate_iff_det_ne_zero.mp hJnd)
    · intro x hx
      have hxiso : x ∈ matrixIsometries (coordinateQuadMinus n K hn1 b c) :=
        matrixDerived_le_isometries _ hx
      exact transpose_mul_toMatrix'_mul
        (polarBilin_isometry ((mem_matrixIsometries_iff _ x).mp hxiso))
  have hnf : ∀ α : MulAut (StatedProj (matrixDerived
      (coordinateQuadMinus n K hn1 b c))), α ^ 5 = 1 →
      ∃ (m : ℕ) (A : GL (Fin (2 * n)) K) (σ : K ≃+* K), ¬ 5 ∣ m ∧
        ∃ θ : matrixDerived (coordinateQuadMinus n K hn1 b c) →*
            matrixDerived (coordinateQuadMinus n K hn1 b c),
          (∀ x : matrixDerived (coordinateQuadMinus n K hn1 b c),
            (θ x : GL (Fin (2 * n)) K) = semilinConjGL A σ x) ∧
          ∀ x : matrixDerived (coordinateQuadMinus n K hn1 b c),
            (α ^ m) (QuotientGroup.mk x :
              StatedProj (matrixDerived (coordinateQuadMinus n K hn1 b c))) =
              QuotientGroup.mk (θ x) := by
    intro α _
    have htop : matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) = ⊤ :=
      matrixProjectiveImage_eq_top_minus K n hn4 b c hirr
    have hmem : α ∈ matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) := by
      rw [htop]
      exact Subgroup.mem_top α
    obtain ⟨g, hg⟩ := (mem_matrixProjectiveImage_iff _ α).mp hmem
    refine ⟨1, g.val.left, g.val.right, by norm_num,
      (matrixDerivedConjugation _ g).toMonoidHom, ?_, ?_⟩
    · intro x
      exact matrixDerivedConjugation_val _ g x
    · intro x
      rw [pow_one, ← hg]
      exact matrixProjectiveConjugation_mk _ g x
  exact weylFivePower_statedProj (ι := Fin (2 * n)) (K := K) h31
    (matrixDerived (coordinateQuadMinus n K hn1 b c)) hZ hdim hnf

theorem weylFivePower_of_model_POmegaOdd {X : Type} [Group X] {n p f : ℕ}
    (h : StatedClassicalModel X .POmegaOdd n p f) (hn : n ≤ 4) (hp2 : p ≠ 2) (hp31 : p ≠ 31) :
    WeylFivePower X := by
  classical
  unfold StatedClassicalModel at h
  obtain ⟨hAdm, K, hField, hFinite, hcard, ⟨e⟩⟩ := h
  let := hField
  let := hFinite
  have := Fintype.ofFinite K
  unfold StatedLieAdmissible at hAdm
  obtain ⟨hp, hf, hn3, _⟩ := hAdm
  have hchar : ringChar K = p := ringChar_eq_of_card_eq hp hf hcard
  have h2 : ringChar K ≠ 2 := by rw [hchar]; exact hp2
  have h31 : ringChar K ≠ 31 := by rw [hchar]; exact hp31
  exact WeylFivePower.of_mulEquiv (coordinateOddWitnessEquiv K e).symm
    (weylFivePower_coordinateQuadOdd hn3 hn h2 h31)

theorem weylFivePower_of_model_POmegaMinus {X : Type} [Group X] {n p f : ℕ}
    (h : StatedClassicalModel X .POmegaMinus n p f) (hn : n ≤ 4) (hp2 : p ≠ 2) (hp31 : p ≠ 31) :
    WeylFivePower X := by
  classical
  unfold StatedClassicalModel at h
  obtain ⟨hAdm, K, hField, hFinite, hcard, b, c, hirr, ⟨e⟩⟩ := h
  let := hField
  let := hFinite
  have := Fintype.ofFinite K
  unfold StatedLieAdmissible at hAdm
  obtain ⟨hp, hf, hn4⟩ := hAdm
  have hchar : ringChar K = p := ringChar_eq_of_card_eq hp hf hcard
  have h31 : ringChar K ≠ 31 := by rw [hchar]; exact hp31
  have _hp2 : p ≠ 2 := hp2
  exact WeylFivePower.of_mulEquiv (coordinateMinusWitnessEquiv K (by omega) b c e).symm
    (weylFivePower_coordinateQuadMinus hn4 hn b c hirr h31)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
