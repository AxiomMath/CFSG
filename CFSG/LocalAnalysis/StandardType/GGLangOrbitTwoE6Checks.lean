module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcDiagramAutomorphisms
public import CFSG.LocalAnalysis.StandardType.GGLatDefs

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem e6_iform_self_check : ∀ α ∈ rootFinset Tag.E6, iform α α = 2 := by
  decide +kernel

private def decEqE6Fast : DecidableEq (Fin Tag.E6.rank → ℤ) := fun u v =>
  decidable_of_iff (((List.finRange Tag.E6.rank).all fun i => decide (u i = v i)) = true) (by
    simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq, true_implies]
    exact funext_iff.symm)

private theorem e6_roots_length : Tag.E6.rootCertificate.roots.length = 72 := by
  decide +kernel

private theorem mem_rootFinset_E6 {α : Fin Tag.E6.rank → ℤ} (h : α ∈ rootFinset Tag.E6) :
    ∃ k < 72, α = Tag.E6.rootCertificate.root k := by
  rw [rootFinset, List.mem_toFinset, List.mem_map] at h
  obtain ⟨k, hk, rfl⟩ := h
  rw [List.mem_range, e6_roots_length] at hk
  exact ⟨k, hk, rfl⟩

private abbrev e6TrichAt (α : Fin Tag.E6.rank → ℤ) : Prop :=
  ∀ β ∈ rootFinset Tag.E6, (β ≠ α ∧ β ≠ -α) → (iform α β = 0 ∨ iform α β = 1 ∨ iform α β = -1)

attribute [local instance high] decEqE6Fast in
private theorem e6_trich_0 :
    ∀ k < 72, k / 18 = 0 → e6TrichAt (Tag.E6.rootCertificate.root k) := by
  decide +kernel

attribute [local instance high] decEqE6Fast in
private theorem e6_trich_1 :
    ∀ k < 72, k / 18 = 1 → e6TrichAt (Tag.E6.rootCertificate.root k) := by
  decide +kernel

attribute [local instance high] decEqE6Fast in
private theorem e6_trich_2 :
    ∀ k < 72, k / 18 = 2 → e6TrichAt (Tag.E6.rootCertificate.root k) := by
  decide +kernel

attribute [local instance high] decEqE6Fast in
private theorem e6_trich_3 :
    ∀ k < 72, k / 18 = 3 → e6TrichAt (Tag.E6.rootCertificate.root k) := by
  decide +kernel

theorem e6_iform_trichotomy_check :
    ∀ α ∈ rootFinset Tag.E6, ∀ β ∈ rootFinset Tag.E6, (β ≠ α ∧ β ≠ -α) →
      (iform α β = 0 ∨ iform α β = 1 ∨ iform α β = -1) := by
  intro α hα
  obtain ⟨k, hk, rfl⟩ := mem_rootFinset_E6 hα
  rcases (by omega : k / 18 = 0 ∨ k / 18 = 1 ∨ k / 18 = 2 ∨ k / 18 = 3) with h | h | h | h
  exacts [e6_trich_0 k hk h, e6_trich_1 k hk h, e6_trich_2 k hk h, e6_trich_3 k hk h]

private abbrev e6SigmaAt (α : Fin Tag.E6.rank → ℤ) : Prop :=
  ∀ β ∈ rootFinset Tag.E6,
    (iform α β = -1 ∧ iform α (latPerm excDiagramSigmaE6 α) = 0 ∧
      iform α (latPerm excDiagramSigmaE6 β) = 0 ∧ iform β (latPerm excDiagramSigmaE6 α) = 0 ∧
      iform β (latPerm excDiagramSigmaE6 β) = 0) →
    ∀ y ∈ rootFinset Tag.E6,
      (y ≠ α ∧ y ≠ β ∧ y ≠ α + β ∧ y ≠ -α ∧ y ≠ -β ∧ y ≠ -(α + β) ∧
        iform α (latPerm excDiagramSigmaE6 y) = 0 ∧ iform β (latPerm excDiagramSigmaE6 y) = 0 ∧
        iform y (latPerm excDiagramSigmaE6 α) = 0 ∧ iform y (latPerm excDiagramSigmaE6 β) = 0 ∧
        iform y (latPerm excDiagramSigmaE6 y) = 0) →
      (iform α y = 0 ∧ iform β y = 0)

private def e6RootSlice (q : ℕ) : Finset (Fin Tag.E6.rank → ℤ) :=
  ((List.range' (9 * q) 9).map Tag.E6.rootCertificate.root).toFinset

private theorem mem_e6RootSlice {k : ℕ} :
    Tag.E6.rootCertificate.root k ∈ e6RootSlice (k / 9) := by
  rw [e6RootSlice, List.mem_toFinset, List.mem_map]
  exact ⟨k, List.mem_range'_1.mpr ⟨by omega, by omega⟩, rfl⟩

attribute [local instance high] decEqE6Fast in
private theorem e6_sigma_0 : ∀ α ∈ e6RootSlice 0, e6SigmaAt α := by
  decide +kernel

attribute [local instance high] decEqE6Fast in
private theorem e6_sigma_1 : ∀ α ∈ e6RootSlice 1, e6SigmaAt α := by
  decide +kernel

attribute [local instance high] decEqE6Fast in
private theorem e6_sigma_2 : ∀ α ∈ e6RootSlice 2, e6SigmaAt α := by
  decide +kernel

attribute [local instance high] decEqE6Fast in
private theorem e6_sigma_3 : ∀ α ∈ e6RootSlice 3, e6SigmaAt α := by
  decide +kernel

attribute [local instance high] decEqE6Fast in
private theorem e6_sigma_4 : ∀ α ∈ e6RootSlice 4, e6SigmaAt α := by
  decide +kernel

attribute [local instance high] decEqE6Fast in
private theorem e6_sigma_5 : ∀ α ∈ e6RootSlice 5, e6SigmaAt α := by
  decide +kernel

attribute [local instance high] decEqE6Fast in
private theorem e6_sigma_6 : ∀ α ∈ e6RootSlice 6, e6SigmaAt α := by
  decide +kernel

attribute [local instance high] decEqE6Fast in
private theorem e6_sigma_7 : ∀ α ∈ e6RootSlice 7, e6SigmaAt α := by
  decide +kernel

theorem e6_sigmaOrth_A2_closed_check :
    ∀ α ∈ rootFinset Tag.E6, ∀ β ∈ rootFinset Tag.E6,
      (iform α β = -1 ∧ iform α (latPerm excDiagramSigmaE6 α) = 0 ∧
        iform α (latPerm excDiagramSigmaE6 β) = 0 ∧ iform β (latPerm excDiagramSigmaE6 α) = 0 ∧
        iform β (latPerm excDiagramSigmaE6 β) = 0) →
      ∀ y ∈ rootFinset Tag.E6,
        (y ≠ α ∧ y ≠ β ∧ y ≠ α + β ∧ y ≠ -α ∧ y ≠ -β ∧ y ≠ -(α + β) ∧
          iform α (latPerm excDiagramSigmaE6 y) = 0 ∧ iform β (latPerm excDiagramSigmaE6 y) = 0 ∧
          iform y (latPerm excDiagramSigmaE6 α) = 0 ∧ iform y (latPerm excDiagramSigmaE6 β) = 0 ∧
          iform y (latPerm excDiagramSigmaE6 y) = 0) →
        (iform α y = 0 ∧ iform β y = 0) := by
  intro α hα
  obtain ⟨k, hk, rfl⟩ := mem_rootFinset_E6 hα
  rcases (by omega : k / 9 = 0 ∨ k / 9 = 1 ∨ k / 9 = 2 ∨ k / 9 = 3 ∨ k / 9 = 4 ∨ k / 9 = 5 ∨
    k / 9 = 6 ∨ k / 9 = 7) with h | h | h | h | h | h | h | h
  · have hm := @mem_e6RootSlice k
    rw [h] at hm
    exact e6_sigma_0 _ hm
  · have hm := @mem_e6RootSlice k
    rw [h] at hm
    exact e6_sigma_1 _ hm
  · have hm := @mem_e6RootSlice k
    rw [h] at hm
    exact e6_sigma_2 _ hm
  · have hm := @mem_e6RootSlice k
    rw [h] at hm
    exact e6_sigma_3 _ hm
  · have hm := @mem_e6RootSlice k
    rw [h] at hm
    exact e6_sigma_4 _ hm
  · have hm := @mem_e6RootSlice k
    rw [h] at hm
    exact e6_sigma_5 _ hm
  · have hm := @mem_e6RootSlice k
    rw [h] at hm
    exact e6_sigma_6 _ hm
  · have hm := @mem_e6RootSlice k
    rw [h] at hm
    exact e6_sigma_7 _ hm

end CFSG.StandardType.LangRat
