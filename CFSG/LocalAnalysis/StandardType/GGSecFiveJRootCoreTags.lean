module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJReflOfCore

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

@[expose] def GGJRootCoreAt
    (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs L J : Subgroup G) (n f : ℕ)
    (ψ : (ggU t n f).K →* G) (y : G), GGKGPosLocalHyp p Bs L t n f ψ →
      GGKGPosStdPos (ggU t n f).D ψ Bs → y ∈ Bs →
      CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer ({y} : Set G)) →
      ∃ γ ∈ (ggU t n f).D.roots, (ggRootLevi (ggU t n f).D γ).map ψ ≤ J

theorem ggJRootCoreInput_iff_forall :
    GGJRootCoreInput ↔ ∀ t : StatedLieTag, GGJRootCoreAt t :=
  ⟨fun h t G _ _ p Bs L J n f ψ y => h G p Bs L J t n f ψ y,
    fun h G _ _ p Bs L J t n f ψ y => h t G p Bs L J n f ψ y⟩

theorem ggJRootCoreInput_of_tags
    (hA : GGJRootCoreAt .PSL) (hD : GGJRootCoreAt .POmegaPlus) (h6 : GGJRootCoreAt .E6)
    (h7 : GGJRootCoreAt .E7) (h8 : GGJRootCoreAt .E8) : GGJRootCoreInput := by
  refine ggJRootCoreInput_iff_forall.2 fun t => ?_
  intro G _ _ p Bs L J n f ψ y hloc hstd hy hJ
  have ht := hloc.2.1.2.2.1
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact hA G p Bs L J n f ψ y hloc hstd hy hJ
  · exact hD G p Bs L J n f ψ y hloc hstd hy hJ
  · exact h6 G p Bs L J n f ψ y hloc hstd hy hJ
  · exact h7 G p Bs L J n f ψ y hloc hstd hy hJ
  · exact h8 G p Bs L J n f ψ y hloc hstd hy hJ

end CFSG.StandardType

end
