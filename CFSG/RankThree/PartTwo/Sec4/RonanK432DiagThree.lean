module

public import CFSG.RankThree.PartOne.KC.CommonEigenbasis
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open Matrix

theorem isPrimitiveRoot_three_of_sq_add_add_one {F : Type} [Field F] {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) : IsPrimitiveRoot ω 3 := by
  have h1 : ω ≠ 1 := fun h => h3 (by linear_combination hω - (ω + 2) * h)
  have h2 : ω ^ 2 ≠ 1 := fun h => h3 (by linear_combination (ω - 1) * h - (ω - 2) * hω)
  refine IsPrimitiveRoot.mk_of_lt ω (by norm_num) (by linear_combination (ω - 1) * hω) ?_
  intro l hl0 hl3
  interval_cases l
  · simpa using h1
  · simpa using h2

theorem exists_zmod_three_pow_eq {F : Type} [Field F] {ω μ : F} (hω : ω ^ 2 + ω + 1 = 0)
    (hμ : μ ^ 3 = 1) : ∃ k : ZMod 3, ω ^ k.val = μ := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hfac : (μ - 1) * (μ - ω) * (μ - ω ^ 2) = 0 := by
    linear_combination hμ + (μ - μ ^ 2) * hω + (μ - 1) * hω3
  rcases mul_eq_zero.mp hfac with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact ⟨0, by rw [show (0 : ZMod 3).val = 0 from rfl, pow_zero]; linear_combination -h'⟩
    · exact ⟨1, by rw [show (1 : ZMod 3).val = 1 from rfl, pow_one]; linear_combination -h'⟩
  · exact ⟨2, by rw [show (2 : ZMod 3).val = 2 from rfl]; linear_combination -h⟩

theorem exists_basis_eigenvectors_of_pow_three {F : Type} [Field F] {n : ℕ} {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) {x : Matrix (Fin n) (Fin n) F}
    (hx : x ^ 3 = 1) :
    ∃ (b : Module.Basis (Fin n) F (Fin n → F)) (a : Fin n → ZMod 3),
      ∀ i, x *ᵥ b i = (ω ^ (a i).val) • b i := by
  have hpow : Matrix.toLin' x ^ 3 = 1 := by
    rw [← Matrix.toLin'_pow, hx, Matrix.toLin'_one, Module.End.one_eq_id]
  have hcubeId : ∀ w : Fin n → F, Matrix.toLin' x (Matrix.toLin' x (Matrix.toLin' x w)) = w := by
    intro w
    have hx' : x * (x * x) = 1 := by rw [← pow_three, hx]
    have hx'' : x * x * x = 1 := by rw [← pow_three', hx]
    simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hx', hx'', Matrix.one_mulVec]
  obtain ⟨b, μ, hb⟩ := CFSG.RankThree.PartOne.exists_basis_common_eigenvectors_of_pow_eq_one
    (isPrimitiveRoot_three_of_sq_add_add_one hω h3) (fun _ : Unit => Matrix.toLin' x)
    (fun _ _ => Commute.refl _) (fun _ => hpow)
  have hcube : ∀ j, μ () j ^ 3 = 1 := by
    intro j
    have hj : Matrix.toLin' x (b j) = μ () j • b j := hb () j
    have hj3 : Matrix.toLin' x (Matrix.toLin' x (Matrix.toLin' x (b j)))
        = (μ () j * μ () j * μ () j) • b j := by
      simp only [hj, map_smul, smul_smul]
    have key := hcubeId (b j)
    rw [hj3] at key
    have hz : (μ () j * μ () j * μ () j - 1) • b j = 0 := by
      rw [sub_smul, one_smul, key, sub_self]
    have hz' := (smul_eq_zero.mp hz).resolve_right (b.ne_zero j)
    linear_combination hz'
  choose a ha using fun j => exists_zmod_three_pow_eq hω (hcube j)
  let e : Fin (Module.finrank F (Fin n → F)) ≃ Fin n := finCongr (Module.finrank_fin_fun F)
  refine ⟨b.reindex e, fun i => a (e.symm i), fun i => ?_⟩
  have hj : Matrix.toLin' x (b (e.symm i)) = μ () (e.symm i) • b (e.symm i) :=
    hb () (e.symm i)
  rw [Module.Basis.reindex_apply, ← Matrix.toLin'_apply, hj, ← ha (e.symm i)]

theorem exists_diagonal_of_pow_three {F : Type} [Field F] {n : ℕ} {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) {x : Matrix (Fin n) (Fin n) F}
    (hx : x ^ 3 = 1) :
    ∃ (g : Matrix.GeneralLinearGroup (Fin n) F) (a : Fin n → ZMod 3),
      (g : Matrix (Fin n) (Fin n) F) * x *
        ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)
        = Matrix.diagonal (fun i => ω ^ (a i).val) := by
  obtain ⟨b, a, hb⟩ := exists_basis_eigenvectors_of_pow_three hω h3 hx
  let P : Matrix (Fin n) (Fin n) F := (Pi.basisFun F (Fin n)).toMatrix b
  have hPij : ∀ i j, P i j = b j i := fun i j => by
    simp [P, Module.Basis.toMatrix_apply]
  haveI : Invertible P := (Pi.basisFun F (Fin n)).invertibleToMatrix b
  have hdet : IsUnit P.det := Matrix.isUnit_det_of_invertible P
  have hxP : x * P = P * Matrix.diagonal (fun i => ω ^ (a i).val) := by
    ext i j
    have h := congrFun (hb j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_apply, Matrix.mul_diagonal]
    simp only [hPij]
    rw [h, mul_comm]
  refine ⟨Units.mk P⁻¹ P (Matrix.nonsing_inv_mul P hdet) (Matrix.mul_nonsing_inv P hdet), a, ?_⟩
  show P⁻¹ * x * P = Matrix.diagonal (fun i => ω ^ (a i).val)
  rw [Matrix.mul_assoc, hxP, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hdet, Matrix.one_mul]

theorem exists_conj_diagonal_of_pow_three {F : Type} [Field F] {n : ℕ} {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) {x : Matrix.GeneralLinearGroup (Fin n) F}
    (hx : x ^ 3 = 1) :
    ∃ (g : Matrix.GeneralLinearGroup (Fin n) F) (a : Fin n → ZMod 3),
      ((g * x * g⁻¹ : Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)
        = Matrix.diagonal (fun i => ω ^ (a i).val) := by
  have hx' : (x : Matrix (Fin n) (Fin n) F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]
  obtain ⟨g, a, h⟩ := exists_diagonal_of_pow_three hω h3 hx'
  exact ⟨g, a, by rw [Units.val_mul, Units.val_mul]; exact h⟩

theorem exists_swap_of_ne_zero (a : Fin 4 → ZMod 3) (ha : a ≠ 0) (hs : ∑ i, a i = 0) :
    ∃ i j : Fin 4, i ≠ j ∧ ∀ k : ZMod 3, ∃ l l' : Fin 4,
      a (Equiv.swap i j l) - k * a l ≠ a (Equiv.swap i j l') - k * a l' := by
  revert a
  decide +kernel

end CFSG.RankThree.PartTwo.Sec4.RonanK432

end
