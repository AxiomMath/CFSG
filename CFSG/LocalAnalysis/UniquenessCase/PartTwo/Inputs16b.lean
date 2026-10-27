module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def R16_4_hyp154 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Setting16 D V₀ V L →
    Conc4_136 D V₀ V hV L → 1 < s15 D.M V₀ V hV L → ¬ Concl164 D V₀ V hV L →
      Hyp154 D V₀ V L

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
