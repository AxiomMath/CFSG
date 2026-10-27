module

public import CFSG.RankThree.Lattice.SteinbergBIE6NineQuot
public import CFSG.RankThree.Lattice.SteinbergBIE7FourteenQuot

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley Matrix Polynomial Module

theorem E6_nine_E7_seven_fourteen_cyclic_lattices_and_root_orbit_quotients :
    (orderOf e6N9W = 9 ∧ e6N9W.charpoly = X ^ 6 + X ^ 3 + 1 ∧
      (∃ v, IsRoot .E6 v ∧
        LinearIndependent ℤ (fun j : Fin Tag.E6.rank => (e6N9W ^ (j : ℕ)) *ᵥ v) ∧
        Submodule.span ℤ (Set.range fun j : Fin Tag.E6.rank => (e6N9W ^ (j : ℕ)) *ᵥ v) = ⊤) ∧
      (∀ α, IsRoot .E6 α →
        LinearIndependent ℤ (fun j : Fin (finrank ℤ (orbitLattice e6N9W α)) =>
          (e6N9W ^ (j : ℕ)) *ᵥ α) ∧
        Submodule.span ℤ (Set.range fun j : Fin (finrank ℤ (orbitLattice e6N9W α)) =>
          (e6N9W ^ (j : ℕ)) *ᵥ α) = orbitLattice e6N9W α) ∧
      (∀ α, IsRoot .E6 α → finrank ℤ (orbitLattice e6N9W α) = Tag.E6.rank ∧
        (orbitLattice e6N9W α).toAddSubgroup.index ∈ [1, 3]) ∧
      {α | IsRoot .E6 α ∧ finrank ℤ (orbitLattice e6N9W α) = 6 ∧
        satIndex (orbitLattice e6N9W α) = 1}.ncard = 54 ∧
      {α | IsRoot .E6 α ∧ finrank ℤ (orbitLattice e6N9W α) = 6 ∧
        satIndex (orbitLattice e6N9W α) = 3}.ncard = 18) ∧
    (orderOf e7S7W = 7 ∧
      e7S7W.charpoly = (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1) * (X - 1) ∧
      (∃ v, IsRoot .E7 v ∧
        LinearIndependent ℤ (fun j : Fin Tag.E7.rank => (e7S7W ^ (j : ℕ)) *ᵥ v) ∧
        Submodule.span ℤ (Set.range fun j : Fin Tag.E7.rank => (e7S7W ^ (j : ℕ)) *ᵥ v) = ⊤) ∧
      (∀ α, IsRoot .E7 α →
        LinearIndependent ℤ (fun j : Fin (finrank ℤ (orbitLattice e7S7W α)) =>
          (e7S7W ^ (j : ℕ)) *ᵥ α) ∧
        Submodule.span ℤ (Set.range fun j : Fin (finrank ℤ (orbitLattice e7S7W α)) =>
          (e7S7W ^ (j : ℕ)) *ᵥ α) = orbitLattice e7S7W α) ∧
      (∀ α, IsRoot .E7 α →
        (finrank ℤ (orbitLattice e7S7W α) = Tag.E7.rank ∧
          (orbitLattice e7S7W α).toAddSubgroup.index ∈ [1, 2, 8]) ∨
        (finrank ℤ (orbitLattice e7S7W α) = 6 ∧
          saturation (orbitLattice e7S7W α) = orbitLattice e7S7W α ∧
          ∃ h : ratSpan (orbitLattice e7S7W α) ≤
              (ratSpan (orbitLattice e7S7W α)).comap (ratEnd e7S7W),
            ((ratEnd e7S7W).restrict h).charpoly = X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1 ∧
            ((ratSpan (orbitLattice e7S7W α)).mapQ _ (ratEnd e7S7W) h).charpoly =
              X - 1)) ∧
      {α | IsRoot .E7 α ∧ finrank ℤ (orbitLattice e7S7W α) = 7 ∧
        satIndex (orbitLattice e7S7W α) = 1}.ncard = 42 ∧
      {α | IsRoot .E7 α ∧ finrank ℤ (orbitLattice e7S7W α) = 7 ∧
        satIndex (orbitLattice e7S7W α) = 2}.ncard = 14 ∧
      {α | IsRoot .E7 α ∧ finrank ℤ (orbitLattice e7S7W α) = 7 ∧
        satIndex (orbitLattice e7S7W α) = 8}.ncard = 28 ∧
      {α | IsRoot .E7 α ∧ finrank ℤ (orbitLattice e7S7W α) = 6 ∧
        satIndex (orbitLattice e7S7W α) = 1}.ncard = 42) ∧
    (e7S14W = e7CxW ^ 9 * e7S7W ∧ e7CxW ^ 9 = -1 ∧ e7S14W = -e7S7W) ∧
    (orderOf e7S14W = 14 ∧
      e7S14W.charpoly = (X ^ 6 - X ^ 5 + X ^ 4 - X ^ 3 + X ^ 2 - X + 1) * (X + 1) ∧
      (∃ v, IsRoot .E7 v ∧
        LinearIndependent ℤ (fun j : Fin Tag.E7.rank => (e7S14W ^ (j : ℕ)) *ᵥ v) ∧
        Submodule.span ℤ (Set.range fun j : Fin Tag.E7.rank => (e7S14W ^ (j : ℕ)) *ᵥ v) = ⊤) ∧
      (∀ α, IsRoot .E7 α →
        LinearIndependent ℤ (fun j : Fin (finrank ℤ (orbitLattice e7S14W α)) =>
          (e7S14W ^ (j : ℕ)) *ᵥ α) ∧
        Submodule.span ℤ (Set.range fun j : Fin (finrank ℤ (orbitLattice e7S14W α)) =>
          (e7S14W ^ (j : ℕ)) *ᵥ α) = orbitLattice e7S14W α) ∧
      (∀ α, IsRoot .E7 α →
        (finrank ℤ (orbitLattice e7S14W α) = Tag.E7.rank ∧
          (orbitLattice e7S14W α).toAddSubgroup.index ∈ [1, 2, 8]) ∨
        (finrank ℤ (orbitLattice e7S14W α) = 6 ∧
          saturation (orbitLattice e7S14W α) = orbitLattice e7S14W α ∧
          ∃ h : ratSpan (orbitLattice e7S14W α) ≤
              (ratSpan (orbitLattice e7S14W α)).comap (ratEnd e7S14W),
            ((ratEnd e7S14W).restrict h).charpoly =
              X ^ 6 - X ^ 5 + X ^ 4 - X ^ 3 + X ^ 2 - X + 1 ∧
            ((ratSpan (orbitLattice e7S14W α)).mapQ _ (ratEnd e7S14W) h).charpoly =
              X + 1)) ∧
      {α | IsRoot .E7 α ∧ finrank ℤ (orbitLattice e7S14W α) = 7 ∧
        satIndex (orbitLattice e7S14W α) = 1}.ncard = 42 ∧
      {α | IsRoot .E7 α ∧ finrank ℤ (orbitLattice e7S14W α) = 7 ∧
        satIndex (orbitLattice e7S14W α) = 2}.ncard = 14 ∧
      {α | IsRoot .E7 α ∧ finrank ℤ (orbitLattice e7S14W α) = 7 ∧
        satIndex (orbitLattice e7S14W α) = 8}.ncard = 28 ∧
      {α | IsRoot .E7 α ∧ finrank ℤ (orbitLattice e7S14W α) = 6 ∧
        satIndex (orbitLattice e7S14W α) = 1}.ncard = 42) :=
  ⟨e6N9_case, e7S7_case, ⟨rfl, e7S14_identities.1, e7S14_identities.2⟩, e7S14_case⟩

end CFSG.RankThree.Lattice
