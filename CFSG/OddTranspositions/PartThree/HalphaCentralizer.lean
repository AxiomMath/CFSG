module

public import CFSG.OddTranspositions.HypothesisC

public section

namespace CFSG.OddTranspositions

variable {G : Type*} [Group G]

theorem Halpha_le_centralizer (D β : Set G) : Halpha D β ≤ Subgroup.centralizer β := by
  rw [Halpha, Subgroup.closure_le]
  rintro x ⟨γ, hγ, hxγ⟩
  exact Subgroup.mem_centralizer_iff.mpr fun a ha => (hγ.2.2.2 a ha x hxγ).eq

end CFSG.OddTranspositions

namespace CFSG.OddTranspositions.PartThree

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem Halpha_le_centralizer_d (hC : HypothesisC D) :
    Halpha D hC.alpha ≤ Subgroup.centralizer ({hC.d} : Set G) :=
  (Halpha_le_centralizer D hC.alpha).trans
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hC.d_mem_alpha))

end CFSG.OddTranspositions.PartThree
