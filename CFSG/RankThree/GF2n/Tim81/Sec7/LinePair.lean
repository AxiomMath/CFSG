module

public import CFSG.RankThree.GF2n.Tim81.Cited.Sec7
import CFSG.RankThree.GF2n.Tim81.Sec7.LinePairPerp
import CFSG.RankThree.GF2n.Tim81.Sec7.LinePairFour

public section

namespace CFSG.RankThree.GF2n.Tim81

theorem unitaryLinePair : UnitaryLinePair := by
  intro K _ _ X₀ Δ f n hf hn hf2 hX A hA B hB hAB
  refine ⟨fun h hh hord C hC hhC =>
      hX.commutator_eq_bot_of_mem_normalizer hf2 hA hB hAB hh hord hC hhC,
    fun h5 => hX.isSUImage_perpRoots hf2 h5 hA hB hAB, fun h4 => ?_⟩
  subst h4
  exact hX.exists_linePair_four hA hB hAB

end CFSG.RankThree.GF2n.Tim81
