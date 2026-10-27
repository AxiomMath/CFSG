module

public import CFSG.HardMathSupport.U4FF.Wedge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18ModU4OuterClsDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.McClurg

open CFSG.HardMathSupport.U4FF CFSG.RankThree.PartOne.CTP.SU4Even
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
open scoped Matrix

@[expose] def f0 {R : Type*} [Add R] (Y : Matrix (Fin 6) (Fin 6) R) : R := Y 0 5 + Y 1 4 + Y 2 3

theorem alt_conj {R : Type*} [CommRing R] [CharP R 2] {ι : Type*} [Fintype ι]
    (T X : Matrix ι ι R) (hXs : Xᵀ = X) (hXd : ∀ i, X i i = 0) :
    (T * X * Tᵀ)ᵀ = T * X * Tᵀ ∧ ∀ i, (T * X * Tᵀ) i i = 0 := by
  have hX : ∀ i j, X i j = X j i := by
    intro i j
    rw [← Matrix.transpose_apply X i j, hXs]
  refine ⟨?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hXs,
      Matrix.mul_assoc]
  · intro i
    have hsum : (T * X * Tᵀ) i i =
        ∑ p : ι × ι, T i p.1 * X p.1 p.2 * T i p.2 := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
      rw [Fintype.sum_prod_type]
      exact Finset.sum_comm
    rw [hsum]
    refine Finset.sum_ninvolution (s := Finset.univ) (fun p : ι × ι => Prod.swap p) ?_ ?_ ?_ ?_
    · intro p
      have hswap : T i (Prod.swap p).1 * X (Prod.swap p).1 (Prod.swap p).2 *
          T i (Prod.swap p).2 = T i p.1 * X p.1 p.2 * T i p.2 := by
        simp only [Prod.swap]
        rw [hX p.2 p.1]
        ring
      rw [hswap, CharTwo.add_self_eq_zero]
    · intro p hp hswap
      apply hp
      obtain ⟨r, s⟩ := p
      simp only [Prod.swap, Prod.mk.injEq] at hswap
      obtain ⟨hsr, -⟩ := hswap
      change T i r * X r s * T i s = 0
      rw [hsr]
      simp [hXd r]
    · intro p
      exact Finset.mem_univ _
    · intro p
      rfl

theorem f0_tm_conj {E K : Type} [Field E] [Field K] [CharP K 2] [Algebra E K] {σ₀ : K ≃+* K}
    {b c : E} (D : KleinDataEven E K σ₀ b c) {k : Type*} [Field k] (lam : K →+* k)
    (X : Matrix (Fin 6) (Fin 6) k) (hXs : Xᵀ = X) (hXd : ∀ i, X i i = 0) :
    f0 ((Tm D).map lam * X * ((Tm D).map lam)ᵀ) =
      X 0 5 + X 1 4 + lam (algebraMap E K b) * X 2 3 := by
  have hδε : lam D.δ * lam D.ε = 1 := by
    rw [← map_mul, D.δ_mul_ε, map_one]
  have hk2 : (2 : k) = 0 := by
    have h : ((2 : ℕ) : k) = 0 := by
      calc ((2 : ℕ) : k) = lam ((2 : ℕ) : K) := (map_natCast lam 2).symm
        _ = lam 0 := by rw [CharP.cast_eq_zero K 2]
        _ = 0 := map_zero lam
    exact h
  have hneg : ∀ x : k, -x = x := by
    intro x
    exact neg_eq_of_add_eq_zero_left (by rw [← two_mul, hk2, zero_mul])
  have h32 : X 3 2 = X 2 3 := by
    rw [← Matrix.transpose_apply X 2 3, hXs]
  have h05 : ((Tm D).map lam * X * ((Tm D).map lam)ᵀ) 0 5 = X 0 5 := by
    simp [Tm, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_six, hXd]
  have h14 : ((Tm D).map lam * X * ((Tm D).map lam)ᵀ) 1 4 =
      -(lam D.δ * X 1 4 * lam D.ε) := by
    simp [Tm, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_six, hXd]
  have h23 : ((Tm D).map lam * X * ((Tm D).map lam)ᵀ) 2 3 =
      -(lam D.ω * X 2 3) + X 2 3 * (lam (algebraMap E K b) + lam D.ω) := by
    simp [Tm, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_six, hXd, h32]
  rw [f0, h05, h14, h23]
  simp only [hneg]
  have h1 : lam D.δ * X 1 4 * lam D.ε = X 1 4 := by
    rw [mul_assoc, mul_comm (X 1 4) (lam D.ε), ← mul_assoc, hδε, one_mul]
  rw [h1]
  linear_combination (lam D.ω * X 2 3) * hk2

theorem mem_adjOmega6_tmInv_conj {E K : Type} [Field E] [Field K] [CharP K 2] [Algebra E K]
    {σ₀ : K ≃+* K} {b c : E} (D : KleinDataEven E K σ₀ b c) {k : Type} [Field k] [CharP k 2]
    (lam : K →+* k) (Y : Matrix (Fin 6) (Fin 6) k) (hYs : Yᵀ = Y) (hYd : ∀ i, Y i i = 0)
    (hf : f0 Y = 0) :
    ((TmInv D).map lam * Y * ((TmInv D).map lam)ᵀ).submatrix colEquiv.symm colEquiv.symm ∈
      adjOmega6 k (lam (algebraMap E K b)) := by
  set Tl : Matrix (Fin 6) (Fin 6) k := (Tm D).map lam with hTl
  set Tli : Matrix (Fin 6) (Fin 6) k := (TmInv D).map lam with hTli
  set Z : Matrix (Fin 6) (Fin 6) k := Tli * Y * Tliᵀ with hZ
  have hTlTli : Tl * Tli = 1 := by
    rw [hTl, hTli, ← Matrix.map_mul, tm_mul_tmInv]
    exact Matrix.map_one _ (map_zero lam) (map_one lam)
  have htrans : Tliᵀ * Tlᵀ = 1 := by
    rw [← Matrix.transpose_mul, hTlTli, Matrix.transpose_one]
  have hYeq : Tl * Z * Tlᵀ = Y := by
    rw [hZ]
    calc Tl * (Tli * Y * Tliᵀ) * Tlᵀ
        = (Tl * Tli) * Y * (Tliᵀ * Tlᵀ) := by noncomm_ring
      _ = Y := by rw [hTlTli, htrans, Matrix.one_mul, Matrix.mul_one]
  have hZs : Zᵀ = Z := by
    rw [hZ]
    exact (alt_conj Tli Y hYs hYd).1
  have hZd : ∀ i, Z i i = 0 := by
    rw [hZ]
    exact (alt_conj Tli Y hYs hYd).2
  have hfZ : Z 0 5 + Z 1 4 + lam (algebraMap E K b) * Z 2 3 = 0 := by
    have h := f0_tm_conj D lam Z hZs hZd
    rw [hYeq] at h
    rw [hf] at h
    exact h.symm
  have hZsym : ∀ i j, Z j i = Z i j := by
    intro i j
    rw [← Matrix.transpose_apply Z i j, hZs]
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    simp [Matrix.submatrix, Matrix.transpose_apply, hZsym]
  · intro i
    exact hZd (colEquiv.symm i)
  · rw [Fin.sum_univ_two]
    simpa [colEquiv] using hfZ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.McClurg
