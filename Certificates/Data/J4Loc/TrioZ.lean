module

public import Certificates.Data.J4Loc.TrioOct

public section

namespace CFSG.Quasithin.J4Loc

open CFSG.Sporadic.J4.QT

@[expose] def TrioZ : Set (Finset ℕ) := {W | W ∈ TrioOct ∧ 1131 ∈ W}

@[expose] def wordZA : List ℤ := [1, 2, -3, -1, 3, 3, -2]

@[expose] def wordZB : List ℤ := [-2, 1, -2, -1, 2, 1, 2, -3]

theorem wordZA_letters : ∀ ℓ ∈ wordZA, ℓ ∈ letters := by decide

theorem wordZB_letters : ∀ ℓ ∈ wordZB, ℓ ∈ letters := by decide

theorem wordImgF_wordZA_z : wordImgF wordZA {1131} = {1131} := by decide

theorem wordImgF_wordZB_z : wordImgF wordZB {1131} = {1131} := by decide

theorem wordImgF_mono (w : List ℤ) : ∀ {V W : Finset ℕ}, V ⊆ W → wordImgF w V ⊆ wordImgF w W := by
  induction w with
  | nil => exact fun h => h
  | cons ℓ w ih => exact fun h => ih (Finset.image_subset_image h)

theorem wordImgF_mem_TrioOct {w : List ℤ} (hw : ∀ ℓ ∈ w, ℓ ∈ letters) :
    ∀ {W : Finset ℕ}, W ∈ TrioOct → wordImgF w W ∈ TrioOct := by
  induction w with
  | nil => exact fun h => h
  | cons ℓ w ih =>
    intro W hW
    exact ih (fun a ha => hw a (List.mem_cons_of_mem _ ha))
      (image_mem_TrioOct hW (hw ℓ List.mem_cons_self))

theorem wordImgF_mem_TrioZ {w : List ℤ} (hw : ∀ ℓ ∈ w, ℓ ∈ letters)
    (hz : wordImgF w {1131} = {1131}) {W : Finset ℕ} (hW : W ∈ TrioZ) : wordImgF w W ∈ TrioZ := by
  refine ⟨wordImgF_mem_TrioOct hw hW.1, ?_⟩
  have h := wordImgF_mono w (Finset.singleton_subset_iff.2 hW.2)
  rw [hz] at h
  exact Finset.singleton_subset_iff.1 h

end CFSG.Quasithin.J4Loc

end
