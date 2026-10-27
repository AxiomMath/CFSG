module

public import CFSG.OddTranspositions.PartThree.Eleven.Plus.Facts
public import CFSG.OddTranspositions.PartThree.Eleven.Plus.Realize

public section

namespace CFSG.OddTranspositions.PartThree


theorem o4PlusFacts_of_isFiveReflectionModel {X : Type} [Group X] {Θ : Set X} {π : Bool}
    (h : IsFiveReflectionModel 3 true π Θ) : O4PlusFacts X Θ := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨e, he⟩ := exists_plusRealize π
  let ψ : X ≃* plusPerm := φ.trans e
  have hφim : φ '' Θ = fiveReflectionImage 3 true π := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (hφ g).mp hg
    · rintro ⟨k, hk, rfl⟩
      refine ⟨φ.symm (QuotientGroup.mk k), (hφ _).mpr ⟨k, hk, ?_⟩, ?_⟩
      · simp
      · simp
  have hψ : ψ '' Θ = plusClass := by
    change (e ∘ φ) '' Θ = plusClass
    rw [Set.image_comp, hφim, he]
  have he' : ψ.symm '' plusClass = Θ := by
    rw [← hψ, Set.image_image]
    simp
  exact O4PlusFacts.of_mulEquiv ψ.symm he' o4PlusFacts_plusPerm

end CFSG.OddTranspositions.PartThree
