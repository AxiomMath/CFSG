module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R920OddS225
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9 (R920odd)

variable {G : Type} [Group G] [Finite G]

theorem s22_5_1K1_of_inputsK1_r920odd (D : Data G) (Ch : Choice2011 G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (he : 3 < evenRank G) (h33 : S22_3_3 D Ch) (h119 : R119W D)
    (h17 : S21_17 D Ch) (h211 : S21_1 D Ch) (hn3 : ∀ c : Ctx21 D Ch, 3 ≤ c.n)
    (h847 : F08.R847 D) (h920 : R920odd D) (h923 : F09.R923K1 D) (h2112 : S21_12 D Ch) :
    S22_5_1K1 D Ch := fun hk =>
  s22_5_1K1_of_inputs_r920odd D Ch hx h61 he h33 h119 h17 h211 hn3 h847 h920
    (fun L hL hLM hLN hA5 hUM _ => h923 hk L hL hLM hLN hA5 hUM) h2112 hk

end CFSG.LocalAnalysis.UniquenessCase.UC22
