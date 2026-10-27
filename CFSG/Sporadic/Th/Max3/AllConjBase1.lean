
module


public import CFSG.Sporadic.Th.Max3.Data

@[expose] public section

namespace CFSG.Sporadic.Th.Max3

open CFSG.Sporadic.Th.Native

namespace AllConj

theorem b_mul_b_mul_b : b * b * b = 1 :=
  toMat_injective (by
    rw [toMat_mul, toMat_mul, toMat_one]
    exact matB_cube)

theorem b_inv : b⁻¹ = b * b :=
  inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact b_mul_b_mul_b)

noncomputable def abLetter (i : ℕ) : J :=
  if i = 1 then a else b

noncomputable def abProd (w : List ℕ) : J :=
  (w.map abLetter).prod

theorem abProd_nil : abProd [] = 1 := by
  simp only [abProd, List.map_nil, List.prod_nil]

theorem abProd_cons
    (i : ℕ) (w : List ℕ) : abProd (i :: w) = abLetter i * abProd w := by
  simp only [abProd, List.map_cons, List.prod_cons]

theorem abProd_append
    (w w' : List ℕ) : abProd (w ++ w') = abProd w * abProd w' := by
  simp only [abProd, List.map_append, List.prod_append]

theorem abLetter_one : abLetter 1 = a :=
  ite_eq_left rfl

theorem abLetter_of_ne {i : ℕ} (h : i ≠ 1) : abLetter i = b :=
  ite_eq_right h

end AllConj

noncomputable def fusionConj (g r : J) : J :=
  (g⁻¹ * r * g * a) ^ 9 * g⁻¹

noncomputable def fusionConjQ0 :
    J := fusionConj (AllConj.abProd fusionWordQ0) (q 0)

noncomputable def fusionConjX :
    J := fusionConj (AllConj.abProd fusionWordX) x

namespace AllConj

theorem isRows_abLetter
    (i : ℕ) : IsRows (abLetterRows i) (abLetter i) := by
  unfold abLetterRows abLetter
  split_ifs
  · exact isRows_a
  · exact isRows_b

theorem isRows_abProd
    (w : List ℕ) : IsRows (abRows w) (abProd w) := by
  refine IsRows.prod ?_
  induction w with
  | nil => exact List.Forall₂.nil
  | cons i w ih => exact List.Forall₂.cons (isRows_abLetter i) ih

theorem isRows_fusionConj
    {g r : J} {rg rgi rr : Array V4} (hg : IsRows rg g)
    (hgi : IsRows rgi g⁻¹) (hr : IsRows rr r) :
    IsRows (fusionRows rg rgi rr) (fusionConj g r) :=
  ((((hgi.mul hr).mul hg).mul isRows_a).pow 9).mul hgi

end AllConj

end CFSG.Sporadic.Th.Max3
