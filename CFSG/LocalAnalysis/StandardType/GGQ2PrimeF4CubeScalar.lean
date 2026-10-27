module

public import CFSG.Fischer.F4
public import Mathlib.RingTheory.Artinian.Instances
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.GGQ2Prime

open CFSG.Fischer Polynomial

private theorem charpoly_dvd_pow_of_pow_three_eq_scalar {R : Type*} [CommRing R] {n : Type*}
    [Fintype n] [DecidableEq n] (s : Matrix n n R) (c : R) (h : s ^ 3 = Matrix.scalar n c) :
    s.charpoly ∣ (X ^ 3 - C c) ^ Fintype.card n := by
  have hcomm : Commute (Matrix.scalar n (X : R[X])) ((C : R →+* R[X]).mapMatrix s) :=
    Matrix.scalar_commute _ (fun r => Commute.all _ _) _
  obtain ⟨B, hB⟩ := hcomm.sub_dvd_pow_sub_pow 3
  have hmap : (C : R →+* R[X]).mapMatrix (Matrix.scalar n c) = Matrix.scalar n (C c) := by
    rw [RingHom.mapMatrix_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _),
      Matrix.scalar_apply]
  have h1 : Matrix.scalar n (X : R[X]) ^ 3 - ((C : R →+* R[X]).mapMatrix s) ^ 3 =
      Matrix.scalar n (X ^ 3 - C c) := by
    rw [← map_pow, ← map_pow, h, hmap, map_sub]
  have h2 := congrArg Matrix.det hB
  rw [h1, Matrix.det_mul, Matrix.scalar_apply, Matrix.det_diagonal] at h2
  refine ⟨B.det, ?_⟩
  simpa [Matrix.charpoly, Matrix.charmatrix] using h2

private theorem F4_pow_three_eq_one_of_ne_zero {a : F4} (ha : a ≠ 0) : a ^ 3 = 1 := by
  have := FiniteField.pow_card_sub_one_eq_one a ha
  rwa [F4.card] at this

private theorem F4_ne_pow_three_of_ne_zero_of_ne_one {b c : F4} (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    b ^ 3 ≠ c := by
  intro hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hc0 (by simpa using hb.symm)
  exact hc1 (hb.symm.trans (F4_pow_three_eq_one_of_ne_zero hb0))

theorem eq_one_of_det_eq_one_of_pow_three_eq_scalar {s : Matrix (Fin 6) (Fin 6) F4}
    (hs : s.det = 1) {c : F4} (h : s ^ 3 = Matrix.scalar (Fin 6) c) : c = 1 := by
  by_contra hc1
  have hc0 : c ≠ 0 := by
    rintro rfl
    have := congrArg Matrix.det h
    rw [Matrix.det_pow, hs, one_pow, Matrix.scalar_apply, Matrix.det_diagonal] at this
    simp at this
  have hirr : Irreducible (X ^ 3 - C c : F4[X]) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_three
      (fun b hb => F4_ne_pow_three_of_ne_zero_of_ne_one hc0 hc1 hb)
  have hdvd := charpoly_dvd_pow_of_pow_three_eq_scalar s c h
  rw [Fintype.card_fin] at hdvd
  obtain ⟨i, -, hassoc⟩ := (dvd_prime_pow hirr.prime 6).1 hdvd
  have hmonic : (X ^ 3 - C c : F4[X]).Monic := monic_X_pow_sub_C c (by norm_num)
  have heq : s.charpoly = (X ^ 3 - C c) ^ i :=
    eq_of_monic_of_associated (Matrix.charpoly_monic s) (hmonic.pow i) hassoc
  have hi : i = 2 := by
    have := congrArg natDegree heq
    rw [Matrix.charpoly_natDegree_eq_dim, hmonic.natDegree_pow, natDegree_X_pow_sub_C,
      Fintype.card_fin] at this
    omega
  subst hi
  have hdet := Matrix.det_eq_sign_charpoly_coeff s
  rw [heq, coeff_zero_eq_eval_zero, hs] at hdet
  simp only [Fintype.card_fin, eval_pow, eval_sub, eval_X, eval_C] at hdet
  have hc2 : c ^ 2 = 1 := by linear_combination -hdet
  exact hc1 (by linear_combination (-c) * hc2 + F4_pow_three_eq_one_of_ne_zero hc0)

end CFSG.GGQ2Prime
