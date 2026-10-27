module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

public section

namespace CFSG.Walter.Ree.Bombieri

open MvPolynomial

theorem degreeOf_zsmul_units_le {σ R : Type*} [CommRing R] (v : σ) (u : ℤˣ)
    (p : MvPolynomial σ R) : (u • p).degreeOf v ≤ p.degreeOf v := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · simp [Units.neg_smul, degreeOf_neg]

theorem degreeOf_det_le {σ R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (v : σ) (M : Matrix n n (MvPolynomial σ R)) (ρ κ : n → ℕ)
    (h : ∀ i j, (M i j).degreeOf v ≤ ρ i + κ j) :
    M.det.degreeOf v ≤ ∑ i, ρ i + ∑ j, κ j := by
  rw [Matrix.det_apply]
  refine (degreeOf_sum_le v _ _).trans (Finset.sup_le fun π _ => ?_)
  calc (Equiv.Perm.sign π • ∏ i, M (π i) i).degreeOf v
      ≤ (∏ i, M (π i) i).degreeOf v := degreeOf_zsmul_units_le v _ _
    _ ≤ ∑ i, (M (π i) i).degreeOf v := degreeOf_prod_le v _ _
    _ ≤ ∑ i, (ρ (π i) + κ i) := Finset.sum_le_sum fun i _ => h (π i) i
    _ = ∑ i, ρ i + ∑ j, κ j := by
      rw [Finset.sum_add_distrib, Equiv.sum_comp π ρ]

end CFSG.Walter.Ree.Bombieri
