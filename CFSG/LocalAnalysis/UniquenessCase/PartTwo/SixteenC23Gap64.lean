module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResultsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs15
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21p
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def C23Gap64 (D : Data G) : Prop :=
  UC6S846.SigmaStd D → DataExt D → UC6.R6_1 D → R127 D → R129_1 D → R1217 D → R119W D →
    Thm145 D → R16_63 D →
    ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
      Case167_2 D V₀ V hV L → Hyp154 D V₀ V L → v1Sub D.M V₀ V hV L ≠ ⊥ → False

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
