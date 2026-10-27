module

public import CFSG.RankThree.PartOne.KC.UnitaryDefiningGramChange

public section

namespace CFSG.RankThree.PartOne.KCUnitaryDefining

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.GroupTheory

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem gramForm_one_apply (x y : Fin n → K) :
    gramForm h (1 : Matrix (Fin n) (Fin n) K) x y = ∑ i, h.bar (x i) * y i := by
  simp [gramForm_apply, dotProduct]

theorem gramForm_one_isSymm : (gramForm h (1 : Matrix (Fin n) (Fin n) K)).IsSymm :=
  gramForm_isSymm h (by rw [Matrix.map_one _ (map_zero h.bar) (map_one h.bar),
    Matrix.transpose_one])

theorem gramForm_one_separatingLeft :
    (gramForm h (1 : Matrix (Fin n) (Fin n) K)).SeparatingLeft :=
  gramForm_separatingLeft h (by simp)

theorem gramForm_mulVec_left (G M : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    gramForm h G (M *ᵥ x) y = gramForm h ((M.map h.bar)ᵀ * G) x y := by
  rw [gramForm_apply, gramForm_apply]
  have hx : (fun a => h.bar ((M *ᵥ x) a)) = M.map h.bar *ᵥ fun a => h.bar (x a) := by
    funext a
    simp [mulVec, dotProduct, map_sum]
  rw [hx, ← vecMul_transpose (M.map h.bar), ← dotProduct_mulVec, mulVec_mulVec]

theorem gramForm_mulVec_right (G M : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    gramForm h G x (M *ᵥ y) = gramForm h (G * M) x y := by
  rw [gramForm_apply, gramForm_apply, mulVec_mulVec]

theorem gramForm_one_mulVec_skew {N : Matrix (Fin n) (Fin n) K} (hs : (N.map h.bar)ᵀ = -N)
    (x y : Fin n → K) :
    gramForm h (1 : Matrix (Fin n) (Fin n) K) (N *ᵥ x) y =
      -gramForm h (1 : Matrix (Fin n) (Fin n) K) x (N *ᵥ y) := by
  rw [gramForm_mulVec_left, gramForm_mulVec_right, hs, Matrix.mul_one, Matrix.one_mul,
    gramForm_apply, gramForm_apply, Matrix.neg_mulVec, dotProduct_neg]

theorem unitaryAdjoint_one (N : Matrix (Fin n) (Fin n) K) :
    unitaryAdjoint h (1 : GL (Fin n) K) N = (N.map h.bar)ᵀ := by
  simp [unitaryAdjoint]

theorem exists_gl_of_family {C' N N' : Matrix (Fin n) (Fin n) K} (hdet : C'.det ≠ 0)
    (b : Fin n → Fin n → K)
    (hb : ∀ i j, gramForm h (1 : Matrix (Fin n) (Fin n) K) (b i) (b j) = C' i j)
    (hNb : ∀ j, N *ᵥ b j = ∑ i, N' i j • b i) :
    ∃ Q : GL (Fin n) K,
      ((Q : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (Q : Matrix (Fin n) (Fin n) K) = C' ∧
      N * (Q : Matrix (Fin n) (Fin n) K) = (Q : Matrix (Fin n) (Fin n) K) * N' := by
  set Qm : Matrix (Fin n) (Fin n) K := Matrix.of fun r c => b c r with hQm
  have hgram : (Qm.map h.bar)ᵀ * Qm = C' := by
    ext i j
    rw [← hb i j, gramForm_one_apply, Matrix.mul_apply]
    simp [hQm]
  have hdetQ : Qm.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hgram
    rw [Matrix.det_mul, h0, mul_zero] at this
    exact hdet this.symm
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero Qm hdetQ, ?_, ?_⟩
  · rw [Units.val_one, Matrix.mul_one]
    exact hgram
  · ext r j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    have := congrFun (hNb j) r
    simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hQm, Matrix.of_apply]
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem normalPrimeComplementsTrivial_of_family (hn : 3 ≤ n) (hnp : n ≤ p) {C' : GL (Fin n) K}
    {N N' : Matrix (Fin n) (Fin n) K} (hN : N ^ n = 0)
    (hskew : unitaryAdjoint h (1 : GL (Fin n) K) N = -N)
    (u' : gramSU h (C' : Matrix (Fin n) (Fin n) K))
    (hu' : ((u' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = truncExp n N')
    (b : Fin n → Fin n → K)
    (hb : ∀ i j, gramForm h (1 : Matrix (Fin n) (Fin n) K) (b i) (b j) =
      (C' : Matrix (Fin n) (Fin n) K) i j)
    (hNb : ∀ j, N *ᵥ b j = ∑ i, N' i j • b i)
    (H : NormalPrimeComplementsTrivial p
      (MulAut.conj (u' : primeFormP h (C' : Matrix (Fin n) (Fin n) K)))) :
    NormalPrimeComplementsTrivial p
      (MulAut.conj (unitaryExp h hn hnp hN hskew :
        primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) := by
  have hdet : (C' : Matrix (Fin n) (Fin n) K).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp C'.isUnit)
  obtain ⟨Q, hQ, hNQ⟩ := exists_gl_of_family h hdet b hb hNb
  exact normalPrimeComplementsTrivial_of_gram_change h hn hnp Q hQ hN hskew hNQ u' hu' H

theorem truncExp_of_mul_self_eq_zero (hd : 2 ≤ n) {N : Matrix (Fin n) (Fin n) K}
    (hN : N * N = 0) : truncExp n N = 1 + N := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 2 := ⟨n - 2, by omega⟩
  have hpow : ∀ j : ℕ, N ^ (j + 2) = 0 := fun j => by
    rw [pow_add, pow_two, hN, mul_zero]
  simp [truncExp, Finset.sum_range_succ', hpow]
  abel

end CFSG.RankThree.PartOne.KCUnitaryDefining
