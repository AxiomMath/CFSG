module

public import Mathlib.Data.Finset.Image
public import CFSG.Sporadic.J4.QTMask

public section

namespace CFSG.Quasithin.J4Loc

open CFSG.Sporadic.J4.QT

@[expose] def V0F : Finset ℕ := {0, 422, 553, 911, 1131, 1485, 1602, 2020}

@[expose] def wordImgF : List ℤ → Finset ℕ → Finset ℕ
  | [], W => W
  | ℓ :: w, W => wordImgF w (W.image (act ℓ))

@[expose] def TrioOct : Set (Finset ℕ) :=
  {W | ∃ w : List ℤ, (∀ ℓ ∈ w, ℓ ∈ letters) ∧ W = wordImgF w V0F}

theorem wordImgF_append (w : List ℤ) (ℓ : ℤ) : ∀ W : Finset ℕ,
    wordImgF (w ++ [ℓ]) W = (wordImgF w W).image (act ℓ) := by
  induction w with
  | nil => intro W; rfl
  | cons a w ih => intro W; exact ih _

theorem V0F_mem_TrioOct : V0F ∈ TrioOct := ⟨[], by simp, rfl⟩

theorem image_mem_TrioOct {W : Finset ℕ} (hW : W ∈ TrioOct) {ℓ : ℤ} (hℓ : ℓ ∈ letters) :
    W.image (act ℓ) ∈ TrioOct := by
  obtain ⟨w, hw, rfl⟩ := hW
  refine ⟨w ++ [ℓ], fun a ha => ?_, (wordImgF_append w ℓ V0F).symm⟩
  rcases List.mem_append.1 ha with ha | ha
  · exact hw a ha
  · rw [List.mem_singleton.1 ha]
    exact hℓ

end CFSG.Quasithin.J4Loc

end
