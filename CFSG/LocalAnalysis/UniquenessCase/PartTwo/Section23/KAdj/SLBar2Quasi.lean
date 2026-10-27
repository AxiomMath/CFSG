module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLModel
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.StabSL
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniBlocks

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open

variable {k : ℕ} {K : Type} [Field K]

theorem isQuasisimple_bar2_hinf_slQZero [NeZero k] [Finite K] [CharP K 2] (hk : 3 ≤ k)
    (hK : 4 ≤ Nat.card K) : CFSG.Open.IsQuasisimple (Bar2 (Hinf (slQZero k K))) := by
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 1 := ⟨k - 1, by omega⟩
  have hd : 2 ≤ d := by omega
  obtain ⟨e⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD.nonempty_bar2_hinf_lineStab_statedSL
      K hK d hd
  have hq : CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin d) K) :=
    CFSG.AGLEmbedding.LeviBlock.isQuasisimple_SL_of_four_le (K := K) hK hd
  exact CFSG.AGLEmbedding.LeviBlock.isQuasisimple_of_mulEquiv
    (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL d K).symm).symm hq

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
