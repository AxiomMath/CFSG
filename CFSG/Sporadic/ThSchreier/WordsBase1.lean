
module

public import CFSG.Sporadic.ThSchreier.WordsBase

public import CFSG.Sporadic.Th.Max3.Data

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3

theorem isRows_signedRows {letter : ℤ → Array V4} {gens : ℤ → J}
    (h : ∀ l, IsRows (letter l) (gens l)) (w : List ℤ) :
    IsRows (signedRows letter w) (wordG gens w) := by
  refine IsRows.prod ?_
  induction w with
  | nil => exact List.Forall₂.nil
  | cons l w ih => exact List.Forall₂.cons (h l) ih

theorem isRows_inv_of_check
    {R Rinv : Array V4} {g : J} (hR : IsRows R g)
    (hsize : Rinv.size = 248) (hwf : ∀ r ∈ Rinv, r.wf = true)
    (h : eqRows (mulRows R Rinv) idRows = true) : IsRows Rinv g⁻¹ := by
  refine ⟨hsize, hwf, ?_⟩
  have h1 := rowsMatrix_eq_of_eqRows h
  rw [rowsMatrix_mulRows, rowsMatrix_idRows, hR.eq] at h1
  have h2 : toMat g⁻¹ * toMat g = 1 := by rw [← toMat_mul, inv_mul_cancel, toMat_one]
  calc rowsMatrix Rinv = (toMat g⁻¹ * toMat g) * rowsMatrix Rinv := by rw [h2, Matrix.one_mul]
    _ = toMat g⁻¹ := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]

theorem isRows_inv_of_mul_self
    {R : Array V4} {g : J} (hR : IsRows R g) (hg : g * g = 1) :
    IsRows R g⁻¹ := by
  have e : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  exact ⟨hR.size, hR.wf, by rw [hR.eq, e]⟩

theorem isRows_inv_of_cube
    {R : Array V4} {g : J} (hR : IsRows R g) (hg : g * g * g = 1) :
    IsRows (mulRows R R) g⁻¹ := by
  have e : g⁻¹ = g * g :=
    inv_eq_of_mul_eq_one_right (show g * (g * g) = 1 by rw [← mul_assoc]; exact hg)
  have h2 := hR.mul hR
  exact ⟨h2.size, h2.wf, by rw [h2.eq, e]⟩

theorem eq_one_of_isRows {R : Array V4} {g : J} (hR : IsRows R g)
    (h : eqRows R idRows = true) : g = 1 :=
  hR.eq_of_eqRows IsRows.one h

theorem ne_one_of_isRows {R : Array V4} {g : J} (hR : IsRows R g)
    (h : eqRows R idRows = false) : g ≠ 1 :=
  hR.ne_of_eqRows IsRows.one h

end CFSG.Sporadic.ThSchreier
