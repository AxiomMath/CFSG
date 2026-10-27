module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcRankP
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcRankE8Datum

public section

namespace Certificates

theorem certificate13750 : ∀ q : ℕ, orderOf ((q : ℕ) : ZMod 5) = 4 →
    CFSG.LocalAnalysis.RankFourTheoremC.ExcRank.TypeCoverP
      CFSG.Blueprint.Chevalley.Tag.E8 5 3 q :=
  CFSG.LocalAnalysis.RankFourTheoremC.ExcRank.typeCoverP_E8_of_datum

end Certificates
