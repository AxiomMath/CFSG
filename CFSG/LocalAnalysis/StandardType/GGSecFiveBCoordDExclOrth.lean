module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclReal
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordSgnReal
import CFSG.LocalAnalysis.StandardType.GGRealSgnOrthRow

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggSecFiveBCoordDExclRestOn_orthNs
    (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) : GGSecFiveBCoordDExclRestOn GGOrthNsSgnLabel := by
  intro G _ _ p B Bs x L D J 𝒦 hR _ n eta i0 hn4 hK y K hK𝒦 hnb r hr hrefl ⟨i, hri⟩ hM
  exact GGSecFiveRouteCfg.ne_dCoordinateBlock_of_realized hLB hP hR hn4 eta i0 hK hrefl hri
    (GGSecFiveRouteCfg.realized_of_sgnAut_of_realSgnOn ggRealSgnOn_orthNs hR eta hK hK𝒦 hnb hM hr
      hrefl hri)

theorem ggSecFiveBCoordDExclRestOn_of_orthNs
    (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGSecFiveBCoordDExclRestOn fun p lab => S p lab ∧ ¬ GGOrthNsSgnLabel p lab) :
    GGSecFiveBCoordDExclRestOn S :=
  ggSecFiveBCoordDExclRestOn_of_split
    (fun p lab hs => (em (GGOrthNsSgnLabel p lab)).elim Or.inr fun ho => Or.inl ⟨hs, ho⟩) h
    (ggSecFiveBCoordDExclRestOn_orthNs hLB hP)

end CFSG.StandardType

end
