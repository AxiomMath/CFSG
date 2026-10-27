module

public import CFSG.LocalAnalysis.StandardType.GGLatRootBridge

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

private lemma fromRel_adj_of_ne {N : ℕ} {r : Fin N → Fin N → Prop} {i j : Fin N}
    (h : r i j) (hij : i ≠ j) : (SimpleGraph.fromRel r).Adj i j :=
  (SimpleGraph.fromRel_adj r i j).mpr ⟨hij, Or.inl h⟩

private theorem connected_cartan_F4 :
    (SimpleGraph.fromRel fun i j : Fin 4 => Tag.cartan .F4 i j ≠ 0).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  have e01 : (SimpleGraph.fromRel fun i j : Fin 4 => Tag.cartan .F4 i j ≠ 0).Adj 0 1 :=
    fromRel_adj_of_ne (by decide) (by decide)
  have e12 : (SimpleGraph.fromRel fun i j : Fin 4 => Tag.cartan .F4 i j ≠ 0).Adj 1 2 :=
    fromRel_adj_of_ne (by decide) (by decide)
  have e23 : (SimpleGraph.fromRel fun i j : Fin 4 => Tag.cartan .F4 i j ≠ 0).Adj 2 3 :=
    fromRel_adj_of_ne (by decide) (by decide)
  intro w
  fin_cases w
  · exact .rfl
  · exact e01.reachable
  · exact e01.reachable.trans e12.reachable
  · exact e01.reachable.trans (e12.reachable.trans e23.reachable)

private theorem connected_cartan_E6 :
    (SimpleGraph.fromRel fun i j : Fin 6 => Tag.cartan .E6 i j ≠ 0).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  have e02 : (SimpleGraph.fromRel fun i j : Fin 6 => Tag.cartan .E6 i j ≠ 0).Adj 0 2 :=
    fromRel_adj_of_ne (by decide) (by decide)
  have e23 : (SimpleGraph.fromRel fun i j : Fin 6 => Tag.cartan .E6 i j ≠ 0).Adj 2 3 :=
    fromRel_adj_of_ne (by decide) (by decide)
  have e34 : (SimpleGraph.fromRel fun i j : Fin 6 => Tag.cartan .E6 i j ≠ 0).Adj 3 4 :=
    fromRel_adj_of_ne (by decide) (by decide)
  have e45 : (SimpleGraph.fromRel fun i j : Fin 6 => Tag.cartan .E6 i j ≠ 0).Adj 4 5 :=
    fromRel_adj_of_ne (by decide) (by decide)
  have e31 : (SimpleGraph.fromRel fun i j : Fin 6 => Tag.cartan .E6 i j ≠ 0).Adj 3 1 :=
    fromRel_adj_of_ne (by decide) (by decide)
  intro w
  fin_cases w
  · exact .rfl
  · exact e02.reachable.trans (e23.reachable.trans e31.reachable)
  · exact e02.reachable
  · exact e02.reachable.trans e23.reachable
  · exact e02.reachable.trans (e23.reachable.trans e34.reachable)
  · exact e02.reachable.trans (e23.reachable.trans (e34.reachable.trans e45.reachable))

private theorem connected_cartan_E7 :
    (SimpleGraph.fromRel fun i j : Fin 7 => Tag.cartan .E7 i j ≠ 0).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  have e02 : (SimpleGraph.fromRel fun i j : Fin 7 => Tag.cartan .E7 i j ≠ 0).Adj 0 2 :=
    fromRel_adj_of_ne (by decide) (by decide)
  have e23 : (SimpleGraph.fromRel fun i j : Fin 7 => Tag.cartan .E7 i j ≠ 0).Adj 2 3 :=
    fromRel_adj_of_ne (by decide) (by decide)
  have e34 : (SimpleGraph.fromRel fun i j : Fin 7 => Tag.cartan .E7 i j ≠ 0).Adj 3 4 :=
    fromRel_adj_of_ne (by decide) (by decide)
  have e45 : (SimpleGraph.fromRel fun i j : Fin 7 => Tag.cartan .E7 i j ≠ 0).Adj 4 5 :=
    fromRel_adj_of_ne (by decide) (by decide)
  have e56 : (SimpleGraph.fromRel fun i j : Fin 7 => Tag.cartan .E7 i j ≠ 0).Adj 5 6 :=
    fromRel_adj_of_ne (by decide) (by decide)
  have e31 : (SimpleGraph.fromRel fun i j : Fin 7 => Tag.cartan .E7 i j ≠ 0).Adj 3 1 :=
    fromRel_adj_of_ne (by decide) (by decide)
  intro w
  fin_cases w
  · exact .rfl
  · exact e02.reachable.trans (e23.reachable.trans e31.reachable)
  · exact e02.reachable
  · exact e02.reachable.trans e23.reachable
  · exact e02.reachable.trans (e23.reachable.trans e34.reachable)
  · exact e02.reachable.trans (e23.reachable.trans (e34.reachable.trans e45.reachable))
  · exact e02.reachable.trans
      (e23.reachable.trans (e34.reachable.trans (e45.reachable.trans e56.reachable)))

private theorem connected_cartan_E8 :
    (SimpleGraph.fromRel fun i j : Fin 8 => Tag.cartan .E8 i j ≠ 0).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  have e02 : (SimpleGraph.fromRel fun i j : Fin 8 => Tag.cartan .E8 i j ≠ 0).Adj 0 2 :=
    fromRel_adj_of_ne (by decide) (by decide)
  have e23 : (SimpleGraph.fromRel fun i j : Fin 8 => Tag.cartan .E8 i j ≠ 0).Adj 2 3 :=
    fromRel_adj_of_ne (by decide) (by decide)
  have e34 : (SimpleGraph.fromRel fun i j : Fin 8 => Tag.cartan .E8 i j ≠ 0).Adj 3 4 :=
    fromRel_adj_of_ne (by decide) (by decide)
  have e45 : (SimpleGraph.fromRel fun i j : Fin 8 => Tag.cartan .E8 i j ≠ 0).Adj 4 5 :=
    fromRel_adj_of_ne (by decide) (by decide)
  have e56 : (SimpleGraph.fromRel fun i j : Fin 8 => Tag.cartan .E8 i j ≠ 0).Adj 5 6 :=
    fromRel_adj_of_ne (by decide) (by decide)
  have e67 : (SimpleGraph.fromRel fun i j : Fin 8 => Tag.cartan .E8 i j ≠ 0).Adj 6 7 :=
    fromRel_adj_of_ne (by decide) (by decide)
  have e31 : (SimpleGraph.fromRel fun i j : Fin 8 => Tag.cartan .E8 i j ≠ 0).Adj 3 1 :=
    fromRel_adj_of_ne (by decide) (by decide)
  intro w
  fin_cases w
  · exact .rfl
  · exact e02.reachable.trans (e23.reachable.trans e31.reachable)
  · exact e02.reachable
  · exact e02.reachable.trans e23.reachable
  · exact e02.reachable.trans (e23.reachable.trans e34.reachable)
  · exact e02.reachable.trans (e23.reachable.trans (e34.reachable.trans e45.reachable))
  · exact e02.reachable.trans
      (e23.reachable.trans (e34.reachable.trans (e45.reachable.trans e56.reachable)))
  · exact e02.reachable.trans
      (e23.reachable.trans (e34.reachable.trans (e45.reachable.trans (e56.reachable.trans
        e67.reachable))))

section Perm

theorem nodesConnected_univ_exc (τ : StatedLieTag) (f : ℕ) (hτ : GGExcFive τ) :
    NodesConnected (ggU (absTag τ) 6 f).D Set.univ := by
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  · unfold NodesConnected
    change ((SimpleGraph.fromRel fun i j : Fin 4 => Tag.cartan .F4 i j ≠ 0).induce
      Set.univ).Connected
    exact (SimpleGraph.Iso.connected_iff (SimpleGraph.induceUnivIso _)).mpr connected_cartan_F4
  · unfold NodesConnected
    change ((SimpleGraph.fromRel fun i j : Fin 6 => Tag.cartan .E6 i j ≠ 0).induce
      Set.univ).Connected
    exact (SimpleGraph.Iso.connected_iff (SimpleGraph.induceUnivIso _)).mpr connected_cartan_E6
  · unfold NodesConnected
    change ((SimpleGraph.fromRel fun i j : Fin 7 => Tag.cartan .E7 i j ≠ 0).induce
      Set.univ).Connected
    exact (SimpleGraph.Iso.connected_iff (SimpleGraph.induceUnivIso _)).mpr connected_cartan_E7
  · unfold NodesConnected
    change ((SimpleGraph.fromRel fun i j : Fin 8 => Tag.cartan .E8 i j ≠ 0).induce
      Set.univ).Connected
    exact (SimpleGraph.Iso.connected_iff (SimpleGraph.induceUnivIso _)).mpr connected_cartan_E8
  · unfold NodesConnected
    change ((SimpleGraph.fromRel fun i j : Fin 6 => Tag.cartan .E6 i j ≠ 0).induce
      Set.univ).Connected
    exact (SimpleGraph.Iso.connected_iff (SimpleGraph.induceUnivIso _)).mpr connected_cartan_E6

theorem latGram_latPerm_exc (τ : StatedLieTag) (f : ℕ) (hτ : GGExcFive τ)
    (S : Matrix (Fin (ggU (absTag τ) 6 f).D.rank) (Fin (ggU (absTag τ) 6 f).D.rank) ℤ)
    (hS : IsRootGram (ggU (absTag τ) 6 f).D S)
    (π : Equiv.Perm (Fin (ggU (absTag τ) 6 f).D.rank))
    (hπ : IsDiagAut (ggU (absTag τ) 6 f).D π) (α β : Fin (ggU (absTag τ) 6 f).D.rank → ℤ) :
    latGram S (latPerm π α) (latPerm π β) = latGram S α β :=
  latGram_latPerm (ggU (absTag τ) 6 f).D S hS π hπ (nodesConnected_univ_exc τ f hτ) α β

private theorem latPerm_mem_roots_F4 (f : ℕ) (π : Equiv.Perm (Fin (ggU .F4 6 f).D.rank))
    (hπ : IsDiagAut (ggU .F4 6 f).D π) {β : Fin (ggU .F4 6 f).D.rank → ℤ}
    (hβ : β ∈ (ggU .F4 6 f).D.roots) : latPerm π β ∈ (ggU .F4 6 f).D.roots := by
  have hπ' : ∀ i j : Fin Tag.F4.rank, Tag.cartan .F4 (π i) (π j) = Tag.cartan .F4 i j := hπ
  have hβ' : IsRoot Tag.F4 β := mem_rootFinset.mp ((mem_roots_F4 6 f β).mp hβ)
  have hres : IsRoot Tag.F4 (latPerm π β) :=
    IsRoot.permLattice (τ := Tag.F4) (π := π) hπ' hβ'
  exact (mem_roots_F4 6 f (latPerm π β)).mpr (mem_rootFinset.mpr hres)

private theorem latPerm_mem_roots_E6 (f : ℕ) (π : Equiv.Perm (Fin (ggU .E6 6 f).D.rank))
    (hπ : IsDiagAut (ggU .E6 6 f).D π) {β : Fin (ggU .E6 6 f).D.rank → ℤ}
    (hβ : β ∈ (ggU .E6 6 f).D.roots) : latPerm π β ∈ (ggU .E6 6 f).D.roots := by
  have hπ' : ∀ i j : Fin Tag.E6.rank, Tag.cartan .E6 (π i) (π j) = Tag.cartan .E6 i j := hπ
  have hβ' : IsRoot Tag.E6 β := mem_rootFinset.mp ((mem_roots_E6 6 f β).mp hβ)
  have hres : IsRoot Tag.E6 (latPerm π β) :=
    IsRoot.permLattice (τ := Tag.E6) (π := π) hπ' hβ'
  exact (mem_roots_E6 6 f (latPerm π β)).mpr (mem_rootFinset.mpr hres)

private theorem latPerm_mem_roots_E7 (f : ℕ) (π : Equiv.Perm (Fin (ggU .E7 6 f).D.rank))
    (hπ : IsDiagAut (ggU .E7 6 f).D π) {β : Fin (ggU .E7 6 f).D.rank → ℤ}
    (hβ : β ∈ (ggU .E7 6 f).D.roots) : latPerm π β ∈ (ggU .E7 6 f).D.roots := by
  have hπ' : ∀ i j : Fin Tag.E7.rank, Tag.cartan .E7 (π i) (π j) = Tag.cartan .E7 i j := hπ
  have hβ' : IsRoot Tag.E7 β := mem_rootFinset.mp ((mem_roots_E7 6 f β).mp hβ)
  have hres : IsRoot Tag.E7 (latPerm π β) :=
    IsRoot.permLattice (τ := Tag.E7) (π := π) hπ' hβ'
  exact (mem_roots_E7 6 f (latPerm π β)).mpr (mem_rootFinset.mpr hres)

private theorem latPerm_mem_roots_E8 (f : ℕ) (π : Equiv.Perm (Fin (ggU .E8 6 f).D.rank))
    (hπ : IsDiagAut (ggU .E8 6 f).D π) {β : Fin (ggU .E8 6 f).D.rank → ℤ}
    (hβ : β ∈ (ggU .E8 6 f).D.roots) : latPerm π β ∈ (ggU .E8 6 f).D.roots := by
  have hπ' : ∀ i j : Fin Tag.E8.rank, Tag.cartan .E8 (π i) (π j) = Tag.cartan .E8 i j := hπ
  have hβ' : IsRoot Tag.E8 β := mem_rootFinset.mp ((mem_roots_E8 6 f β).mp hβ)
  have hres : IsRoot Tag.E8 (latPerm π β) :=
    IsRoot.permLattice (τ := Tag.E8) (π := π) hπ' hβ'
  exact (mem_roots_E8 6 f (latPerm π β)).mpr (mem_rootFinset.mpr hres)

theorem latPerm_mem_roots_exc (τ : StatedLieTag) (f : ℕ) (hτ : GGExcFive τ)
    (π : Equiv.Perm (Fin (ggU (absTag τ) 6 f).D.rank))
    (hπ : IsDiagAut (ggU (absTag τ) 6 f).D π) {β : Fin (ggU (absTag τ) 6 f).D.rank → ℤ}
    (hβ : β ∈ (ggU (absTag τ) 6 f).D.roots) :
    latPerm π β ∈ (ggU (absTag τ) 6 f).D.roots := by
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  · exact latPerm_mem_roots_F4 f π hπ hβ
  · exact latPerm_mem_roots_E6 f π hπ hβ
  · exact latPerm_mem_roots_E7 f π hπ hβ
  · exact latPerm_mem_roots_E8 f π hπ hβ
  · exact latPerm_mem_roots_E6 f π hπ hβ

end Perm

end CFSG.StandardType
