
module

public import Mathlib
public import CFSG.GH74.GLS.Stage4.Q9.ModelBaseInputs
import CFSG.Certificates.Kernel.Q9LgSound
import Certificates.Kernel.Q9Lg.Checks

public section

open CFSG.GH74.GLS.Stage4.Q9 CFSG.KC.Q9Lg

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.Stage4 in
open CFSG.GH74.GLS.Stage4.Q9 in
theorem certificate5100 : (∀ l : Lg, ordL l ≠ 0)
    ∧ ((Finset.univ.filter fun l : Lg => ordL l = 1).card = 1)
    ∧ ((Finset.univ.filter fun l : Lg => ordL l = 2).card = 73)
    ∧ ((Finset.univ.filter fun l : Lg => ordL l = 3).card = 80)
    ∧ ((Finset.univ.filter fun l : Lg => ordL l = 4).card = 90)
    ∧ ((Finset.univ.filter fun l : Lg => ordL l = 5).card = 144)
    ∧ ((Finset.univ.filter fun l : Lg => ordL l = 6).card = 80)
    ∧ ((Finset.univ.filter fun l : Lg => ordL l = 8).card = 180)
    ∧ ((Finset.univ.filter fun l : Lg => ordL l = 10).card = 432)
    ∧ ((Finset.univ.filter fun l : Lg => ordL l = 16).card = 360)
    ∧ (∀ l : Lg, ordL l ∈ ({1, 2, 3, 4, 5, 6, 8, 10, 16} : Finset ℕ))
    ∧ ((Finset.univ.filter fun l : Lg => parityL l ≠ 1 ∧ l ^ 2 = 1).card = 72)
    ∧ (∀ l : Lg, parityL l ≠ 1 → l ^ 2 ≠ innerL minusOne) := by
  have hI := chkHistIK_true
  have hO := chkHistOK_true
  have hmem := ordL_mem_of hI hO
  have hc := card_ordL_eq hI hO
  refine ⟨fun l h => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmem, card_outer_inv_of hO,
    no_outer_sq_of hO⟩
  · have := hmem l
    rw [h] at this
    exact absurd this (by decide)
  · rw [hc 1 (by norm_num)]; rfl
  · rw [hc 2 (by norm_num)]; rfl
  · rw [hc 3 (by norm_num)]; rfl
  · rw [hc 4 (by norm_num)]; rfl
  · rw [hc 5 (by norm_num)]; rfl
  · rw [hc 6 (by norm_num)]; rfl
  · rw [hc 8 (by norm_num)]; rfl
  · rw [hc 10 (by norm_num)]; rfl
  · rw [hc 16 (by norm_num)]; rfl

end Certificates
