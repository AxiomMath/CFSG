module

public import CFSG.RankThree.Lattice.SteinbergBIChecks

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley Matrix

@[expose] def f4W8 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ := wordMat .F4 [0, 1, 2, 1, 2, 3]

@[expose] def f4W12 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ := wordMat .F4 [0, 1, 2, 3]

@[expose] def f4W8List : List (List ℤ) :=
  [[1, -1, 1, -1], [2, -1, 1, -1], [2, 0, 1, -2], [0, 0, 1, -1]]

@[expose] def f4W12List : List (List ℤ) :=
  [[0, 1, 0, -1], [1, 1, 0, -1], [0, 2, 0, -1], [0, 0, 1, -1]]

theorem f4W8_eq : f4W8 = toMat Tag.F4.rank f4W8List :=
  wordMat_eq_toMat .F4 _ (by decide +kernel)

theorem f4W12_eq : f4W12 = toMat Tag.F4.rank f4W12List :=
  wordMat_eq_toMat .F4 _ (by decide +kernel)

theorem toVec_f4V : toVec Tag.F4.rank [-1, -1, -1, -1] = ![-1, -1, -1, -1] := by
  show toVec 4 [-1, -1, -1, -1] = ![-1, -1, -1, -1]
  decide +kernel

theorem F4_eight_twelve_Weyl_cyclic_lattice_and_root_orbit_indices :
    f4W8 = !![1, -1, 1, -1; 2, -1, 1, -1; 2, 0, 1, -2; 0, 0, 1, -1] ∧
    f4W12 = !![0, 1, 0, -1; 1, 1, 0, -1; 0, 2, 0, -1; 0, 0, 1, -1] ∧
    orderOf f4W8 = 8 ∧ orderOf f4W12 = 12 ∧ f4W8 ^ 4 = -1 ∧ f4W12 ^ 4 - f4W12 ^ 2 + 1 = 0 ∧
    (∀ w ∈ [f4W8, f4W12],
      (LinearIndependent ℤ (fun j : Fin Tag.F4.rank => (w ^ (j : ℕ)) *ᵥ ![-1, -1, -1, -1]) ∧
        Submodule.span ℤ (Set.range fun j : Fin Tag.F4.rank =>
          (w ^ (j : ℕ)) *ᵥ ![-1, -1, -1, -1]) = ⊤) ∧
      (orbitMat w ![-1, -1, -1, -1] Tag.F4.rank).det = 1) ∧
    (∀ w ∈ [f4W8, f4W12], ∀ α : Fin Tag.F4.rank → ℤ, IsRoot .F4 α →
      LinearIndependent ℤ (fun j : Fin Tag.F4.rank => (w ^ (j : ℕ)) *ᵥ α) ∧
        ∃ k : ℕ, |(orbitMat w α Tag.F4.rank).det| = 2 ^ k) ∧
    {α | IsRoot .F4 α ∧ |(orbitMat f4W8 α Tag.F4.rank).det| = 1}.ncard = 16 ∧
    {α | IsRoot .F4 α ∧ |(orbitMat f4W8 α Tag.F4.rank).det| = 2}.ncard = 8 ∧
    {α | IsRoot .F4 α ∧ |(orbitMat f4W8 α Tag.F4.rank).det| = 4}.ncard = 16 ∧
    {α | IsRoot .F4 α ∧ |(orbitMat f4W8 α Tag.F4.rank).det| = 8}.ncard = 8 ∧
    {α | IsRoot .F4 α ∧ |(orbitMat f4W12 α Tag.F4.rank).det| = 1}.ncard = 24 ∧
    {α | IsRoot .F4 α ∧ |(orbitMat f4W12 α Tag.F4.rank).det| = 4}.ncard = 24 := by
  have hv : ∀ W : List (List ℤ), lorbitDet Tag.F4.rank W [-1, -1, -1, -1] = 1 →
      (LinearIndependent ℤ (fun j : Fin Tag.F4.rank =>
          (toMat Tag.F4.rank W ^ (j : ℕ)) *ᵥ ![-1, -1, -1, -1]) ∧
        Submodule.span ℤ (Set.range fun j : Fin Tag.F4.rank =>
          (toMat Tag.F4.rank W ^ (j : ℕ)) *ᵥ ![-1, -1, -1, -1]) = ⊤) ∧
      (orbitMat (toMat Tag.F4.rank W) ![-1, -1, -1, -1] Tag.F4.rank).det = 1 := by
    intro W hW
    have hdet : (orbitMat (toMat Tag.F4.rank W) ![-1, -1, -1, -1] Tag.F4.rank).det = 1 := by
      rw [← toVec_f4V, det_orbitMat_toVec, hW]
    exact ⟨(isBasis_iff_isUnit_det _ _).2 (by rw [hdet]; exact isUnit_one), hdet⟩
  have hroots : ∀ W : List (List ℤ),
      (∀ l ∈ Tag.F4.artifactRoots, lorbitDet Tag.F4.rank W l ∈ [1, -1, 2, -2, 4, -4, 8, -8]) →
      ∀ α : Fin Tag.F4.rank → ℤ, IsRoot .F4 α →
        LinearIndependent ℤ (fun j : Fin Tag.F4.rank => (toMat Tag.F4.rank W ^ (j : ℕ)) *ᵥ α) ∧
          ∃ k : ℕ, |(orbitMat (toMat Tag.F4.rank W) α Tag.F4.rank).det| = 2 ^ k := by
    intro W hW α hα
    have h := forall_isRoot_orbitDet W (· ∈ [1, -1, 2, -2, 4, -4, 8, -8]) hW α hα
    have hne : (orbitMat (toMat Tag.F4.rank W) α Tag.F4.rank).det ≠ 0 := by
      intro h0
      rw [h0] at h
      simp at h
    refine ⟨Matrix.linearIndependent_cols_of_det_ne_zero hne, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h <;> rw [h]
    exacts [⟨0, rfl⟩, ⟨0, rfl⟩, ⟨1, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨3, rfl⟩]
  refine ⟨by
      rw [f4W8_eq]
      show toMat 4 f4W8List = !![1, -1, 1, -1; 2, -1, 1, -1; 2, 0, 1, -2; 0, 0, 1, -1]
      decide +kernel, by
      rw [f4W12_eq]
      show toMat 4 f4W12List = !![0, 1, 0, -1; 1, 1, 0, -1; 0, 2, 0, -1; 0, 0, 1, -1]
      decide +kernel,
    by rw [f4W8_eq]; exact orderOf_toMat_eq (by norm_num) (by decide +kernel) (by decide +kernel),
    by rw [f4W12_eq]; exact orderOf_toMat_eq (by norm_num) (by decide +kernel) (by decide +kernel),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [f4W8_eq, ← toMat_lpow]
    have h : lpow Tag.F4.rank f4W8List 4 =
        [[-1, 0, 0, 0], [0, -1, 0, 0], [0, 0, -1, 0], [0, 0, 0, -1]] := by
      decide +kernel
    rw [h]
    decide +kernel
  · rw [f4W12_eq, ← toMat_lpow, ← toMat_lpow]
    have h4 : lpow Tag.F4.rank f4W12List 4 =
        [[0, 1, -1, 0], [1, 1, -1, -1], [2, 2, -2, -1], [0, 2, -1, -1]] := by
      decide +kernel
    have h2 : lpow Tag.F4.rank f4W12List 2 =
        [[1, 1, -1, 0], [1, 2, -1, -1], [2, 2, -1, -1], [0, 2, -1, 0]] := by
      decide +kernel
    rw [h4, h2]
    decide +kernel
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · rw [f4W8_eq]
      exact hv _ (by decide +kernel)
    · rw [f4W12_eq]
      exact hv _ (by decide +kernel)
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · rw [f4W8_eq]
      exact hroots _ (by decide +kernel)
    · rw [f4W12_eq]
      exact hroots _ (by decide +kernel)
  · rw [f4W8_eq, f4W12_eq]
    exact ⟨(ncard_isRoot_orbitDet f4W8List (fun d => |d| = 1)).trans (by decide +kernel),
      (ncard_isRoot_orbitDet f4W8List (fun d => |d| = 2)).trans (by decide +kernel),
      (ncard_isRoot_orbitDet f4W8List (fun d => |d| = 4)).trans (by decide +kernel),
      (ncard_isRoot_orbitDet f4W8List (fun d => |d| = 8)).trans (by decide +kernel),
      (ncard_isRoot_orbitDet f4W12List (fun d => |d| = 1)).trans (by decide +kernel),
      (ncard_isRoot_orbitDet f4W12List (fun d => |d| = 4)).trans (by decide +kernel)⟩

end CFSG.RankThree.Lattice
