module

public import CFSG.LocalAnalysis.WeakClosure81.W183Free

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

@[expose] def Tail1812FourFreeKStar (G : Type) [Group G] [Finite G] : Prop :=
  W3Thm162Gt2 G → W3Thm172Weak G → Asch5_4 → Asch5_11AS → Asch5_12 → Asch5_13AS →
    ∀ {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}, MinCex183 D V₀ V H i →
      ¬ Concl182 D V₀ V H i →
      ¬ kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G) →
      ∀ {g : G}, vInH V H g ≤ D.T → ¬ vInH V H g ≤ kerMV V H →
        E3.mQuot (conjSubgroup V g) (vInH V H g) ≤ i →
        3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g) → False

theorem tail1812FourFree_AS_of_split (h1 : Tail1812Four_AS G) (h2 : Tail1812FourFreeKStar G) :
    Tail1812FourFree_AS G := by
  intro h162 h172 h5_4 h5_11 h5_12 h5_13 D V₀ V H i c hc g hgT hgK hgi hA
  by_cases hK : kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G)
  · exact h1 h162 h172 h5_4 h5_11 h5_12 h5_13 c hc hK hgT hgK hgi hA
  · exact h2 h162 h172 h5_4 h5_11 h5_12 h5_13 c hc hK hgT hgK hgi hA

end CFSG.LocalAnalysis.WeakClosure81

end
