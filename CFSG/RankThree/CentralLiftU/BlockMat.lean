module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import CFSG.LieType.Universal.SpecialLinearRoots.SignedPerm

public section

namespace CFSG.RankThree.CentralLiftU

open Matrix

variable {ι κ κ' : Type*} [DecidableEq ι] {R : Type*} [CommRing R]

@[expose] def embMat (e : κ → ι) : Matrix ι κ R := Matrix.of fun x a => if e a = x then 1 else 0

theorem embMat_apply (e : κ → ι) (x : ι) (a : κ) :
    (embMat e : Matrix ι κ R) x a = if e a = x then 1 else 0 :=
  rfl

variable [Fintype ι] [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

omit [Fintype κ] [Fintype κ'] [DecidableEq κ'] in
theorem transpose_embMat_mul_embMat {e : κ → ι} (he : Function.Injective e) :
    (embMat e : Matrix ι κ R)ᵀ * (embMat e : Matrix ι κ R) = 1 := by
  ext a b
  rw [mul_apply, one_apply]
  simp only [transpose_apply, embMat_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab, he.ne hab]

omit [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] in
theorem transpose_embMat_mul_embMat_of_disjoint {e : κ → ι} {e' : κ' → ι}
    (hdisj : ∀ a b, e a ≠ e' b) :
    (embMat e : Matrix ι κ R)ᵀ * (embMat e' : Matrix ι κ' R) = 0 := by
  ext a b
  rw [mul_apply, Matrix.zero_apply]
  simp only [transpose_apply, embMat_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _), ite_eq_right (hdisj a b)]

@[expose] def blockMat (e : κ → ι) (M : Matrix κ κ R) : Matrix ι ι R :=
  1 + embMat e * (M - 1) * (embMat e)ᵀ

omit [Fintype ι] [Fintype κ'] [DecidableEq κ'] in
theorem blockMat_one (e : κ → ι) : blockMat e (1 : Matrix κ κ R) = 1 := by
  simp [blockMat]

omit [Fintype κ'] [DecidableEq κ'] in
theorem blockMat_mul {e : κ → ι} (he : Function.Injective e) (M N : Matrix κ κ R) :
    blockMat e (M * N) = blockMat e M * blockMat e N := by
  have hPP := transpose_embMat_mul_embMat (R := R) he
  simp only [blockMat]
  set P : Matrix ι κ R := embMat e
  have key : P * (M - 1) * Pᵀ * (P * (N - 1) * Pᵀ) = P * ((M - 1) * (N - 1)) * Pᵀ := by
    calc P * (M - 1) * Pᵀ * (P * (N - 1) * Pᵀ) = P * (M - 1) * (Pᵀ * P) * (N - 1) * Pᵀ := by
          simp only [Matrix.mul_assoc]
      _ = P * ((M - 1) * (N - 1)) * Pᵀ := by rw [hPP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.one_mul,
    Matrix.mul_one, key]
  have hMN : M * N - 1 = (M - 1) + (N - 1) + (M - 1) * (N - 1) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    abel
  rw [hMN, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  abel

omit [Fintype ι] [Fintype κ'] [DecidableEq κ'] in
theorem blockMat_apply_e {e : κ → ι} (he : Function.Injective e) (M : Matrix κ κ R) (a b : κ) :
    blockMat e M (e a) (e b) = M a b := by
  have h1 : (embMat e * (M - 1) * (embMat e)ᵀ : Matrix ι ι R) (e a) (e b) = (M - 1) a b := by
    rw [mul_apply]
    simp only [transpose_apply, embMat_apply, mul_apply]
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul]
    rw [Finset.sum_eq_single b (fun c _ hc => by rw [ite_eq_right (fun h => hc (he h))])
      (fun h => absurd (Finset.mem_univ b) h), ite_eq_left rfl,
      Finset.sum_eq_single a (fun c _ hc => by rw [ite_eq_right (fun h => hc (he h))])
      (fun h => absurd (Finset.mem_univ a) h), ite_eq_left rfl]
  rw [blockMat, Matrix.add_apply, h1, Matrix.sub_apply, one_apply, one_apply]
  by_cases hab : a = b
  · subst hab; simp
  · rw [ite_eq_right (fun h => hab (he h)), ite_eq_right hab]
    ring

omit [Fintype ι] [Fintype κ'] [DecidableEq κ'] in
theorem blockMat_apply_of_notMem_left {e : κ → ι} (M : Matrix κ κ R) {x : ι}
    (hx : ∀ a, e a ≠ x) (y : ι) : blockMat e M x y = (1 : Matrix ι ι R) x y := by
  rw [blockMat, Matrix.add_apply, mul_apply]
  simp only [mul_apply, embMat_apply, ite_eq_right (hx _), zero_mul, Finset.sum_const_zero,
    add_zero]

omit [Fintype ι] [Fintype κ'] [DecidableEq κ'] in
theorem blockMat_apply_of_notMem_right {e : κ → ι} (M : Matrix κ κ R) {y : ι}
    (hy : ∀ a, e a ≠ y) (x : ι) : blockMat e M x y = (1 : Matrix ι ι R) x y := by
  rw [blockMat, Matrix.add_apply, mul_apply]
  simp only [transpose_apply, embMat_apply, ite_eq_right (hy _), mul_zero, Finset.sum_const_zero,
    add_zero]

omit [Fintype κ'] [DecidableEq κ'] in
theorem det_blockMat {e : κ → ι} (he : Function.Injective e) (M : Matrix κ κ R) :
    (blockMat e M).det = M.det := by
  rw [blockMat, Matrix.mul_assoc, det_one_add_mul_comm, Matrix.mul_assoc,
    transpose_embMat_mul_embMat he, Matrix.mul_one, add_sub_cancel]

theorem commute_blockMat {e : κ → ι} {e' : κ' → ι} (hdisj : ∀ a b, e a ≠ e' b)
    (M : Matrix κ κ R) (N : Matrix κ' κ' R) : Commute (blockMat e M) (blockMat e' N) := by
  have h0 := transpose_embMat_mul_embMat_of_disjoint (R := R) hdisj
  have h0' := transpose_embMat_mul_embMat_of_disjoint (R := R) (fun b a => (hdisj a b).symm)
  simp only [Commute, SemiconjBy, blockMat]
  set P : Matrix ι κ R := embMat e
  set Q : Matrix ι κ' R := embMat e'
  have k1 : P * (M - 1) * Pᵀ * (Q * (N - 1) * Qᵀ) = 0 := by
    calc P * (M - 1) * Pᵀ * (Q * (N - 1) * Qᵀ) = P * (M - 1) * (Pᵀ * Q) * (N - 1) * Qᵀ := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h0]; simp
  have k2 : Q * (N - 1) * Qᵀ * (P * (M - 1) * Pᵀ) = 0 := by
    calc Q * (N - 1) * Qᵀ * (P * (M - 1) * Pᵀ) = Q * (N - 1) * (Qᵀ * P) * (M - 1) * Pᵀ := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h0']; simp
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_add, k1, k2]
  simp only [Matrix.one_mul, Matrix.mul_one, add_zero]
  abel

omit [Fintype ι] [Fintype κ'] [DecidableEq κ'] in
theorem embMat_comp (e : κ → ι) (e' : κ' → κ) :
    (embMat e : Matrix ι κ R) * (embMat e' : Matrix κ κ' R) = embMat (e ∘ e') := by
  ext x b
  rw [mul_apply]
  simp only [embMat_apply, mul_ite, mul_one, mul_zero, Function.comp_apply]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]

omit [Fintype ι] in
theorem blockMat_blockMat (e : κ → ι) (e' : κ' → κ) (M : Matrix κ' κ' R) :
    blockMat e (blockMat e' M) = blockMat (e ∘ e') M := by
  simp only [blockMat, add_sub_cancel_left]
  rw [← embMat_comp e e', Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

omit [Fintype κ'] [DecidableEq κ'] in
theorem conj_blockMat {e e' : κ → ι} {Q Q' : Matrix ι ι R} {D D' : Matrix κ κ R}
    (hQ : Q * (embMat e : Matrix ι κ R) = embMat e' * D)
    (hQ' : (embMat e : Matrix ι κ R)ᵀ * Q' = D' * (embMat e')ᵀ)
    (hQQ' : Q * Q' = 1) (hDD' : D * D' = 1) (M : Matrix κ κ R) :
    Q * blockMat e M * Q' = blockMat e' (D * M * D') := by
  simp only [blockMat]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hQQ']
  congr 1
  calc Q * ((embMat e : Matrix ι κ R) * (M - 1) * (embMat e : Matrix ι κ R)ᵀ) * Q'
      = (Q * (embMat e : Matrix ι κ R)) * (M - 1) * ((embMat e : Matrix ι κ R)ᵀ * Q') := by
        simp only [Matrix.mul_assoc]
    _ = (embMat e' : Matrix ι κ R) * (D * (M - 1) * D') * (embMat e' : Matrix ι κ R)ᵀ := by
        rw [hQ, hQ']; simp only [Matrix.mul_assoc]
    _ = (embMat e' : Matrix ι κ R) * (D * M * D' - 1) * (embMat e' : Matrix ι κ R)ᵀ := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hDD']

omit [Fintype κ'] [DecidableEq κ'] in
theorem diagonal_mul_embMat (e : κ → ι) (q : ι → R) :
    diagonal q * (embMat e : Matrix ι κ R) = embMat e * diagonal (q ∘ e) := by
  ext x a
  rw [diagonal_mul, mul_diagonal, embMat_apply, Function.comp_apply]
  split_ifs with h
  · rw [h, mul_one, one_mul]
  · simp

omit [Fintype κ'] [DecidableEq κ'] in
theorem transpose_embMat_mul_diagonal (e : κ → ι) (q : ι → R) :
    (embMat e : Matrix ι κ R)ᵀ * diagonal q = diagonal (q ∘ e) * (embMat e)ᵀ := by
  ext a x
  rw [mul_diagonal, diagonal_mul]
  simp only [transpose_apply, embMat_apply, Function.comp_apply]
  split_ifs with h
  · rw [h, mul_one, one_mul]
  · simp

omit [Fintype κ'] [DecidableEq κ'] in
theorem signedPerm_mul_embMat (e : κ → ι) (σ : Equiv.Perm ι) (s : ι → R) :
    CFSG.LieType.Universal.SpecialLinear.signedPerm σ s * (embMat e : Matrix ι κ R) =
      embMat (σ ∘ e) * diagonal (s ∘ e) := by
  ext x a
  rw [mul_apply, mul_diagonal]
  simp only [embMat_apply, mul_ite, mul_one, mul_zero, Function.comp_apply]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
  simp only [CFSG.LieType.Universal.SpecialLinear.signedPerm, of_apply]
  split_ifs with h1 h2 h2
  · rw [one_mul]
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

omit [Fintype κ'] [DecidableEq κ'] in
theorem transpose_embMat_mul_signedPerm_symm (e : κ → ι) (σ : Equiv.Perm ι) (t : ι → R) :
    (embMat e : Matrix ι κ R)ᵀ * CFSG.LieType.Universal.SpecialLinear.signedPerm σ.symm t =
      diagonal (fun a => t (σ (e a))) * (embMat (σ ∘ e) : Matrix ι κ R)ᵀ := by
  ext a x
  rw [mul_apply, diagonal_mul]
  simp only [transpose_apply, embMat_apply, ite_mul, one_mul, zero_mul, Function.comp_apply]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
  simp only [CFSG.LieType.Universal.SpecialLinear.signedPerm, of_apply]
  by_cases hx : σ (e a) = x
  · subst hx
    simp
  · rw [ite_eq_right (fun h => hx (by rw [h]; simp)), ite_eq_right hx, mul_zero]

omit [Fintype κ'] [DecidableEq κ'] in
theorem conj_signedPerm_blockMat (e : κ → ι) {σ : Equiv.Perm ι} {s t : ι → R}
    (hst : ∀ x, s x * t (σ x) = 1) (M : Matrix κ κ R) :
    CFSG.LieType.Universal.SpecialLinear.signedPerm σ s * blockMat e M *
        CFSG.LieType.Universal.SpecialLinear.signedPerm σ.symm t =
      blockMat (σ ∘ e) (diagonal (s ∘ e) * M * diagonal (fun a => t (σ (e a)))) := by
  refine conj_blockMat (signedPerm_mul_embMat e σ s) (transpose_embMat_mul_signedPerm_symm e σ t)
    ?_ ?_ M
  · rw [CFSG.LieType.Universal.SpecialLinear.signedPerm_mul_signedPerm,
      show σ * σ.symm = 1 from mul_inv_cancel σ,
      CFSG.LieType.Universal.SpecialLinear.signedPerm_one, ← diagonal_one]
    congr 1
    funext y
    have := hst (σ.symm y)
    rwa [Equiv.apply_symm_apply] at this
  · rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    exact hst (e a)

omit [Fintype ι] [Fintype κ'] [DecidableEq κ'] in
theorem blockMat_signedPerm {e : κ → ι} (he : Function.Injective e) {σ' : Equiv.Perm κ}
    {s' : κ → R} {σ : Equiv.Perm ι} {s : ι → R} (hσ : ∀ a, σ (e a) = e (σ' a))
    (hσ' : ∀ x, (∀ a, e a ≠ x) → σ x = x) (hs : ∀ a, s (e a) = s' a)
    (hs' : ∀ x, (∀ a, e a ≠ x) → s x = 1) :
    blockMat e (CFSG.LieType.Universal.SpecialLinear.signedPerm σ' s') =
      CFSG.LieType.Universal.SpecialLinear.signedPerm σ s := by
  ext x y
  simp only [CFSG.LieType.Universal.SpecialLinear.signedPerm_apply]
  by_cases hy : ∃ b, e b = y
  · obtain ⟨b, rfl⟩ := hy
    rw [hσ, hs]
    by_cases hx : ∃ a, e a = x
    · obtain ⟨a, rfl⟩ := hx
      rw [blockMat_apply_e he, CFSG.LieType.Universal.SpecialLinear.signedPerm_apply]
      by_cases hab : a = σ' b
      · rw [ite_eq_left hab, ite_eq_left (by rw [hab])]
      · rw [ite_eq_right hab, ite_eq_right (fun h => hab (he h))]
    · push Not at hx
      rw [blockMat_apply_of_notMem_left _ hx, one_apply_ne (fun h => hx b h.symm),
        ite_eq_right (fun h => hx _ h.symm)]
  · push Not at hy
    rw [blockMat_apply_of_notMem_right _ hy, hσ' y hy, hs' y hy, one_apply]

end CFSG.RankThree.CentralLiftU
