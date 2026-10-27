module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def R16_24c (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    (Case167_3 D V₀ V hV L ∨ Case167_4 D V₀ V hV L ∨ Case167_7 D V₀ V hV L ∨
      Case167_8 D V₀ V hV L) →
      ¬ normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M ∨
        ¬ centralizer (E3.cClos V D.k D.T : Set G) ≤ D.M ∨ (calO2 D.k D.M V₀ V).Nonempty

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
