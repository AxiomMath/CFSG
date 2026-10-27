module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import Certificates.Data.GGWitExcModel

public section

namespace CFSG.StandardType.ZS

open Certificates.ExcModel

abbrev owEm_GL (n : ℕ) := Matrix.GeneralLinearGroup (Fin n) (ZMod 13)

theorem owEm_strict {n : ℕ} (A : Mat n) : (strict A).val = A := by
  ext i j
  simp [strict, tabMat, List.getD_eq_getElem?_getD]

theorem owEm_foldl_inv {α β : Type*} (P : β → Prop) (f : β → α → β) (l : List α) (b : β) (hb : P b)
    (hf : ∀ b a, a ∈ l → P b → P (f b a)) : P (l.foldl f b) := by
  induction l generalizing b with
  | nil => exact hb
  | cons a l ih => exact ih _ (hf b a (by simp) hb) (fun b' a' ha' => hf b' a' (by simp [ha']))

@[expose] def owEm_unit {n : ℕ} (s : Mat n) (h : s * s = 1) : owEm_GL n :=
  ⟨s, s, h, h⟩

theorem owEm_unit_inv {n : ℕ} (s : Mat n) (h : s * s = 1) : (owEm_unit s h)⁻¹ = owEm_unit s h := rfl

end CFSG.StandardType.ZS

end
