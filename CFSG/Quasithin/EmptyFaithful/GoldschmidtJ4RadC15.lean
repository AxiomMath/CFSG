module

public import Certificates.Certificate4179
public import Certificates.Data.J4Rad.C15Native
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheckB

public section

namespace CFSG.Quasithin.J4Rad

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc

@[expose] def w15L : Set (List ℕ) := {W | W ∈ trioL ∧ 1131 ∈ W}

structure C15Spec : Prop where
  letA : ∀ ℓ ∈ wordA, ℓ ∈ letters
  letB : ∀ ℓ ∈ wordB, ℓ ∈ letters
  fixA : actW wordA 1131 = 1131
  fixB : actW wordB 1131 = 1131
  memAB : ∀ W ∈ w15L, imgW wordA W ∈ w15L ∧ imgW wordB W ∈ w15L
  comm : ∀ W ∈ w15L, imgW wordA (imgW wordB W) = imgW wordB (imgW wordA W)
  ordA : ∀ W ∈ w15L, imgW wordA (imgW wordA (imgW wordA W)) = W
  ordB : ∀ W ∈ w15L, imgW wordB (imgW wordB (imgW wordB W)) = W
  neA : ∃ W ∈ w15L, (imgW wordA W).toFinset ≠ W.toFinset
  neB0 : ∃ W ∈ w15L, (imgW wordB W).toFinset ≠ W.toFinset
  neB1 : ∃ W ∈ w15L, (imgW wordB W).toFinset ≠ (imgW wordA W).toFinset
  neB2 : ∃ W ∈ w15L, (imgW wordB W).toFinset ≠ (imgW wordA (imgW wordA W)).toFinset

theorem w15_subset_trio : ∀ W ∈ w15L, W ∈ trioL := fun _ hW => hW.1

theorem one_mem_of_mem_w15 {W : List ℕ} (hW : W ∈ w15L) : 1131 ∈ W := hW.2

theorem wordImgF_eq_image (w : List ℤ) : ∀ F : Finset ℕ, wordImgF w F = F.image (actW w) := by
  induction w with
  | nil =>
    intro F
    ext x
    simp [wordImgF, actW]
  | cons ℓ w ih =>
    intro F
    rw [wordImgF, ih, Finset.image_image]
    rfl

theorem imgW_toFinset (w : List ℤ) (W : List ℕ) :
    (imgW w W).toFinset = wordImgF w W.toFinset := by
  rw [wordImgF_eq_image]
  unfold imgW
  rw [toFinset_srt]
  ext x
  simp

theorem mem_TrioZ_of_w15 {W : List ℕ} (hW : W ∈ w15L) : W.toFinset ∈ TrioZ :=
  ⟨hW.1.2, List.mem_toFinset.2 hW.2⟩

theorem imgW_mem_w15 {w : List ℤ} (hw : ∀ ℓ ∈ w, ℓ ∈ letters)
    (hz : wordImgF w {1131} = {1131}) {W : List ℕ} (hW : W ∈ w15L) : imgW w W ∈ w15L := by
  have hZ := wordImgF_mem_TrioZ hw hz (mem_TrioZ_of_w15 hW)
  rw [← imgW_toFinset] at hZ
  have h8 := (trioL_props hW.1).1
  have hL : (W.map (actW w)).toFinset ∈ TrioOct := by
    have e := imgW_toFinset w W
    unfold imgW at e
    rw [toFinset_srt] at e
    rw [e, ← imgW_toFinset]
    exact hZ.1
  exact ⟨srt_mem_trioL (by rw [List.length_map, h8]) hL, List.mem_toFinset.1 hZ.2⟩

theorem c15_spec : C15Spec := by
  obtain ⟨-, hrel, W, hW, hne⟩ := Certificates.certificate4179
  have hA : ∀ ℓ ∈ wordA, ℓ ∈ letters := wordZA_letters
  have hB : ∀ ℓ ∈ wordB, ℓ ∈ letters := wordZB_letters
  have hzA : wordImgF wordA {1131} = {1131} := wordImgF_wordZA_z
  have hzB : wordImgF wordB {1131} = {1131} := wordImgF_wordZB_z
  have mA : ∀ {V}, V ∈ w15L → imgW wordA V ∈ w15L := fun h => imgW_mem_w15 hA hzA h
  have mB : ∀ {V}, V ∈ w15L → imgW wordB V ∈ w15L := fun h => imgW_mem_w15 hB hzB h
  have ext : ∀ {U V}, U ∈ w15L → V ∈ w15L → U.toFinset = V.toFinset → U = V :=
    fun hU hV h => trioL_ext hU.1 hV.1 h
  have fixA : actW wordA 1131 = 1131 := by decide
  have fixB : actW wordB 1131 = 1131 := by decide
  have hWs : (W.sort (· ≤ ·)).toFinset = W := Finset.sort_toFinset _ _
  have hWl : W.sort (· ≤ ·) ∈ w15L := by
    have hnd := Finset.sort_nodup W (· ≤ ·)
    refine ⟨⟨((Finset.pairwise_sort W (· ≤ ·)).and hnd).imp fun h => lt_of_le_of_ne h.1 h.2, ?_⟩,
      ?_⟩
    · rw [hWs]
      exact hW.1
    · rw [← List.mem_toFinset, hWs]
      exact hW.2
  refine ⟨hA, hB, fixA, fixB, fun V hV => ⟨mA hV, mB hV⟩, fun V hV => ?_, fun V hV => ?_,
    fun V hV => ?_, ⟨_, hWl, ?_⟩, ⟨_, hWl, ?_⟩, ⟨_, hWl, ?_⟩, ⟨_, hWl, ?_⟩⟩
  · refine ext (mA (mB hV)) (mB (mA hV)) ?_
    rw [imgW_toFinset, imgW_toFinset, imgW_toFinset, imgW_toFinset]
    exact (hrel _ (mem_TrioZ_of_w15 hV)).1
  · refine ext (mA (mA (mA hV))) hV ?_
    rw [imgW_toFinset, imgW_toFinset, imgW_toFinset]
    exact (hrel _ (mem_TrioZ_of_w15 hV)).2.1
  · refine ext (mB (mB (mB hV))) hV ?_
    rw [imgW_toFinset, imgW_toFinset, imgW_toFinset]
    exact (hrel _ (mem_TrioZ_of_w15 hV)).2.2
  · rw [imgW_toFinset, hWs]
    exact hne.1
  · rw [imgW_toFinset, hWs]
    exact hne.2.1
  · rw [imgW_toFinset, imgW_toFinset, hWs]
    exact hne.2.2.1
  · rw [imgW_toFinset, imgW_toFinset, imgW_toFinset, hWs]
    exact hne.2.2.2

theorem w15_enum :
    ∃ f : Fin 15 → List ℕ, (∀ j, f j ∈ w15L) ∧
      ∀ i j, (f i).toFinset = (f j).toFinset → i = j := by
  have h15 := Certificates.certificate4179.1
  have hfin : TrioZ.Finite := Set.finite_of_ncard_ne_zero (by rw [h15]; decide)
  have : Finite TrioZ := hfin.to_subtype
  have hcard : Nat.card TrioZ = 15 := by rw [Nat.card_coe_set_eq, h15]
  let e := (Finite.equivFinOfCardEq hcard).symm
  refine ⟨fun j => (e j : Finset ℕ).sort (· ≤ ·), fun j => ?_, fun i j h => ?_⟩
  · have hs : ((e j : Finset ℕ).sort (· ≤ ·)).toFinset = e j := Finset.sort_toFinset _ _
    have hnd := Finset.sort_nodup (e j : Finset ℕ) (· ≤ ·)
    refine ⟨⟨((Finset.pairwise_sort _ (· ≤ ·)).and hnd).imp fun h => lt_of_le_of_ne h.1 h.2,
      ?_⟩, ?_⟩
    · rw [hs]
      exact (e j).2.1
    · rw [← List.mem_toFinset, hs]
      exact (e j).2.2
  · rw [Finset.sort_toFinset, Finset.sort_toFinset] at h
    exact e.injective (Subtype.ext h)

@[expose] noncomputable def wordElt : List Int → J
  | [] => 1
  | ℓ :: w => wordElt w * XJ ℓ

theorem wordElt_mem {w : List Int} (hw : ∀ ℓ ∈ w, ℓ ∈ letters) : wordElt w ∈ Hj := by
  induction w with
  | nil => exact Hj.one_mem
  | cons ℓ w ih =>
    exact Hj.mul_mem (ih fun l hl => hw l (List.mem_cons_of_mem _ hl))
      (XJ_mem (hw ℓ List.mem_cons_self))

theorem wordElt_conj (hM : MatFacts) {w : List Int}
    (hw : ∀ ℓ ∈ w, ℓ ∈ letters) (c : ℕ) :
    wordElt w * eta uJ 11 c * (wordElt w)⁻¹ = eta uJ 11 (actW w c) := by
  induction w generalizing c with
  | nil => simp [wordElt, actW]
  | cons ℓ w ih =>
    have e : wordElt (ℓ :: w) * eta uJ 11 c * (wordElt (ℓ :: w))⁻¹ =
        wordElt w * (XJ ℓ * eta uJ 11 c * (XJ ℓ)⁻¹) * (wordElt w)⁻¹ := by
      simp only [wordElt]
      group
    rw [e, hX_all hM (hw ℓ List.mem_cons_self) c,
      ih (fun l hl => hw l (List.mem_cons_of_mem _ hl))]
    rfl

end CFSG.Quasithin.J4Rad
