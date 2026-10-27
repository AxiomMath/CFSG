module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitDefs
import CFSG.LocalAnalysis.StandardType.GGNTPlaneTableOrbits

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private def e6SplitOrbitList (i : ExcRaw.Root 1) : List (Fin Tag.E6.rank → ℤ) :=
  [e6SplitRoot i, -e6SplitRoot i, permLattice TwistTag.E6.perm (e6SplitRoot i),
    -permLattice TwistTag.E6.perm (e6SplitRoot i)]

private theorem mem_e6SplitCodeRoots_singleton_iff {i : ExcRaw.Root 1}
    {δ : Fin Tag.E6.rank → ℤ} : δ ∈ e6SplitCodeRoots {i} ↔ δ ∈ e6SplitOrbitList i := by
  constructor
  · rintro ⟨k, hk, h⟩
    obtain rfl := Finset.mem_singleton.1 hk
    rcases h with rfl | rfl | rfl | rfl
    · exact List.mem_cons.2 (Or.inl rfl)
    · exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))
    · exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))))
    · exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr
        (List.mem_singleton.2 rfl))))))
  · intro h
    refine ⟨i, Finset.mem_singleton_self i, ?_⟩
    rcases List.mem_cons.1 h with h | h
    · exact Or.inl h
    rcases List.mem_cons.1 h with h | h
    · exact Or.inr (Or.inl h)
    rcases List.mem_cons.1 h with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    exact Or.inr (Or.inr (Or.inr (List.mem_singleton.1 h)))

private theorem e6SplitOrbitList_subset : ∀ i, ∀ δ ∈ e6SplitOrbitList i, δ ∈ NTPlane.e6RootList := by
  decide +kernel

private theorem exists_mem_e6SplitOrbitList :
    ∀ δ ∈ NTPlane.e6RootList, ∃ i, δ ∈ e6SplitOrbitList i := by
  decide +kernel

private theorem eq_of_mem_e6SplitOrbitList :
    ∀ i j, ∀ δ ∈ e6SplitOrbitList i, δ ∈ e6SplitOrbitList j → i = j := by
  decide +kernel

theorem isRoot_of_mem_e6SplitCodeRoots {c : Finset (ExcRaw.Root 1)} {δ : Fin Tag.E6.rank → ℤ}
    (hδ : δ ∈ e6SplitCodeRoots c) : IsRoot .E6 δ := by
  obtain ⟨i, -, hi⟩ := hδ
  have hmem : δ ∈ e6SplitCodeRoots {i} := ⟨i, Finset.mem_singleton_self i, hi⟩
  exact (NTPlane.isRoot_iff_mem_e6RootList δ).2
    (e6SplitOrbitList_subset i δ (mem_e6SplitCodeRoots_singleton_iff.1 hmem))

theorem isRoot_e6SplitRoot (i : ExcRaw.Root 1) : IsRoot .E6 (e6SplitRoot i) :=
  isRoot_of_mem_e6SplitCodeRoots ⟨i, Finset.mem_singleton_self i, Or.inl rfl⟩

theorem permLattice_e6SplitRoot_eq_iff (i : ExcRaw.Root 1) :
    permLattice TwistTag.E6.perm (e6SplitRoot i) = e6SplitRoot i ↔
      ExcRaw.tabFix1.getD i.val false = true :=
  (by decide +kernel : ∀ i : ExcRaw.Root 1, permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i) =
    e6SplitRoot i ↔ ExcRaw.tabFix1.getD i.val false = true) i

theorem pairing_one_eq_e6RelCorootPair (i j : ExcRaw.Root 1) :
    ExcRaw.pairing 1 i j = e6RelCorootPair (e6SplitRoot j) (e6SplitRoot i) := by
  revert i j
  decide +kernel

theorem exists_mem_e6SplitCodeRoots_singleton {δ : Fin Tag.E6.rank → ℤ} (hδ : IsRoot .E6 δ) :
    ∃ i, δ ∈ e6SplitCodeRoots {i} := by
  obtain ⟨i, hi⟩ := exists_mem_e6SplitOrbitList δ ((NTPlane.isRoot_iff_mem_e6RootList δ).1 hδ)
  exact ⟨i, mem_e6SplitCodeRoots_singleton_iff.2 hi⟩

theorem eq_of_mem_e6SplitCodeRoots_singleton {δ : Fin Tag.E6.rank → ℤ} {i j : ExcRaw.Root 1}
    (hi : δ ∈ e6SplitCodeRoots {i}) (hj : δ ∈ e6SplitCodeRoots {j}) : i = j :=
  eq_of_mem_e6SplitOrbitList i j δ (mem_e6SplitCodeRoots_singleton_iff.1 hi)
    (mem_e6SplitCodeRoots_singleton_iff.1 hj)

theorem mem_e6SplitCodeRoots_iff {c : Finset (ExcRaw.Root 1)} {δ : Fin Tag.E6.rank → ℤ}
    {i : ExcRaw.Root 1} (hi : δ ∈ e6SplitCodeRoots {i}) : δ ∈ e6SplitCodeRoots c ↔ i ∈ c := by
  constructor
  · rintro ⟨j, hj, hδj⟩
    rwa [eq_of_mem_e6SplitCodeRoots_singleton hi ⟨j, Finset.mem_singleton_self j, hδj⟩]
  · intro hic
    obtain ⟨k, hk, hδk⟩ := hi
    rw [Finset.mem_singleton.1 hk] at hδk
    exact ⟨i, hic, hδk⟩

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
