module

public import CFSG.LocalAnalysis.StandardType.PhanEDMRel

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.DM

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem

variable {I C : Type*}

@[expose] def levelSet (lev : C → ℕ) (m : ℕ) : Set C := {x | lev x ≤ m}

@[expose] def aff (lev : C → ℕ) (S : Set C) : Set C := {x | x ∈ S ∧ ∀ y ∈ S, lev x ≤ lev y}

@[expose] def Descends (X : ChamberSystem I C) (lev : C → ℕ) (J : Set I) (A : Set C) : Prop :=
  ∀ m : ℕ, (∃ x ∈ A, lev x ≤ m) →
    ∃ j ∈ J, ∀ x ∈ A, lev x ≤ m + 1 → ∃ x' ∈ A, lev x' ≤ m ∧ X.adj j x x'

@[expose] def IsResidual (X : ChamberSystem I C) (lev : C → ℕ) : Prop :=
  ∀ (J : Set I) (c : C), J.Nonempty → Descends X lev J (X.residue J c)

@[expose] def Lco (X : ChamberSystem I C) (lev : C → ℕ) : Prop :=
  ∀ (J : Set I) (c : C), J.encard = 2 → ConnectedIn X J (aff lev (X.residue J c))

@[expose] def Lsco (X : ChamberSystem I C) (lev : C → ℕ) : Prop :=
  ∀ (J : Set I) (c : C), J.encard = 3 → SimplyConnectedIn X J (aff lev (X.residue J c)) 2

variable {X : ChamberSystem I C} {lev : C → ℕ} {J : Set I} {A S : Set C} {m : ℕ}

theorem mem_levelSet {x : C} : x ∈ levelSet lev m ↔ lev x ≤ m := Iff.rfl

theorem aff_subset : aff lev S ⊆ S := fun _ h => h.1

theorem levelSet_mono {m m' : ℕ} (h : m ≤ m') : levelSet lev m ⊆ levelSet lev m' :=
  fun _ hx => le_trans hx h

theorem lev_le_of_mem_aff {x y : C} (hx : x ∈ aff lev S) (hy : y ∈ S) : lev x ≤ lev y := hx.2 y hy

theorem aff_subset_levelSet {x : C} (hx : x ∈ S) (hxm : lev x ≤ m) :
    aff lev S ⊆ levelSet lev m := by
  intro y hy
  exact le_trans (lev_le_of_mem_aff hy hx) hxm

theorem inter_levelSet_eq_aff {R : Set C} (h : ∀ x ∈ R, m ≤ lev x)
    (hne : (R ∩ levelSet lev m).Nonempty) : R ∩ levelSet lev m = aff lev R := by
  obtain ⟨x₀, hx₀R, hx₀m⟩ := hne
  have hx₀ : lev x₀ = m := le_antisymm hx₀m (h x₀ hx₀R)
  ext y
  refine ⟨fun hy => ⟨hy.1, fun z hz => ?_⟩, fun hy => ⟨hy.1, ?_⟩⟩
  · exact le_trans hy.2 (h z hz)
  · exact le_trans (hy.2 x₀ hx₀R) (le_of_eq hx₀)

theorem exists_descending_gallery (hD : Descends X lev J A) {x : C} (hx : x ∈ A) :
    ∃ (y : C) (γ : List (I × C)), y ∈ aff lev A ∧
      GalleryIn X J (A ∩ levelSet lev (lev x)) x γ ∧ galleryEnd x γ = y := by
  suffices H : ∀ n : ℕ, ∀ x ∈ A, lev x = n →
      ∃ (y : C) (γ : List (I × C)), y ∈ aff lev A ∧
        GalleryIn X J (A ∩ levelSet lev (lev x)) x γ ∧ galleryEnd x γ = y by
    exact H (lev x) x hx rfl
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih x hx hxn
  by_cases hmin : ∀ z ∈ A, lev x ≤ lev z
  · refine ⟨x, [], ⟨hx, hmin⟩, ?_, rfl⟩
    rw [galleryIn_nil]
    exact ⟨hx, mem_levelSet.mpr le_rfl⟩
  · obtain ⟨z, hznot⟩ := not_forall.1 hmin
    obtain ⟨hzA, hznot'⟩ := not_imp.1 hznot
    have hzlt : lev z < lev x := not_le.1 hznot'
    have hxpos : 0 < lev x := lt_of_le_of_lt (Nat.zero_le _) hzlt
    have hxm_eq : (lev x - 1) + 1 = lev x := Nat.sub_add_cancel hxpos
    obtain ⟨j, hjJ, hstep⟩ := hD (lev x - 1) ⟨z, hzA, by omega⟩
    obtain ⟨x', hx'A, hx'm, hadj⟩ := hstep x hx hxm_eq.ge
    have hx'lt : lev x' < lev x := by omega
    have hx'n : lev x' < n := by omega
    obtain ⟨y, γ', hyaff, hgal, hend⟩ := ih (lev x') hx'n x' hx'A rfl
    have hx'le : lev x' ≤ lev x := le_of_lt hx'lt
    refine ⟨y, (j, x') :: γ', hyaff, ?_, ?_⟩
    · rw [galleryIn_cons]
      exact ⟨⟨hx, mem_levelSet.mpr le_rfl⟩, hadj, hjJ, ⟨hx'A, hx'le⟩,
        GalleryIn.mono (Set.Subset.refl J)
          (fun w hw => ⟨hw.1, levelSet_mono hx'le hw.2⟩) hgal⟩
    · rw [galleryEnd_cons]
      exact hend

theorem connectedIn_levelSet_inter (hD : Descends X lev J A) (hc : ConnectedIn X J (aff lev A))
    (m : ℕ) : ConnectedIn X J (A ∩ levelSet lev m) := by
  intro a ha b hb
  obtain ⟨ya, γa, hya, hgala, henda⟩ := exists_descending_gallery hD ha.1
  obtain ⟨yb, γb, hyb, hgalb, hendb⟩ := exists_descending_gallery hD hb.1
  obtain ⟨γ, hgalγ, hendγ⟩ := hc ya hya yb hyb
  have hsubA : A ∩ levelSet lev (lev a) ⊆ A ∩ levelSet lev m :=
    fun z hz => ⟨hz.1, levelSet_mono ha.2 hz.2⟩
  have hsubB : A ∩ levelSet lev (lev b) ⊆ A ∩ levelSet lev m :=
    fun z hz => ⟨hz.1, levelSet_mono hb.2 hz.2⟩
  have hsubaff : aff lev A ⊆ A ∩ levelSet lev m :=
    fun z hz => ⟨aff_subset hz, aff_subset_levelSet ha.1 ha.2 hz⟩
  have hγa : GalleryIn X J (A ∩ levelSet lev m) a γa :=
    GalleryIn.mono (Set.Subset.refl J) hsubA hgala
  have hγ : GalleryIn X J (A ∩ levelSet lev m) ya γ :=
    GalleryIn.mono (Set.Subset.refl J) hsubaff hgalγ
  have hγb : GalleryIn X J (A ∩ levelSet lev m) yb (galleryReverse b γb) := by
    have hrev := GalleryIn.reverse hgalb
    rw [hendb] at hrev
    exact GalleryIn.mono (Set.Subset.refl J) hsubB hrev
  refine ⟨γa ++ γ ++ galleryReverse b γb, ?_, ?_⟩
  · rw [galleryIn_append]
    refine ⟨?_, ?_⟩
    · rw [galleryIn_append]
      exact ⟨hγa, by rw [henda]; exact hγ⟩
    · rw [galleryEnd_append, henda, hendγ]
      exact hγb
  · rw [galleryEnd_append, galleryEnd_append, henda, hendγ, ← hendb, galleryEnd_galleryReverse]

end CFSG.ClassicalInvolution.Phan.PhanE.DM
