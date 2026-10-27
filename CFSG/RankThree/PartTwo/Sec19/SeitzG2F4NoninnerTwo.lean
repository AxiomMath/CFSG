module

public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeNarrow
public import CFSG.RankThree.PartTwo.Sec19.SeitzG2F4G2
public import CFSG.RankThree.PartTwo.Sec19.SeitzG2F4ReeF4
public import CFSG.RankThree.PartTwo.Sec19.SeitzG2F4A3
public import CFSG.LieType.SeitzGeneration.OuterSpCat
public import CFSG.LieType.SeitzGeneration.OuterSUCat
public import CFSG.LieType.SeitzGeneration.SpF2.Main
public import CFSG.HardMathSupport.Malle.Coordinator.SubfieldPairs.SUOddTwoBig

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2 CFSG.RankThree.PartOne

theorem seitzThreeSec441NoninnerTwo_holds_of_certs :
    SeitzThreeSec441NoninnerTwo := by
  have hSp := subfieldPairSpOdd subfieldPairSpF2_holds
  have hSU := subfieldPairSUOdd
    CFSG.HardMathSupport.Malle.Coordinator.SubfieldPairs.subfieldPairSUOddTwo_holds
  rintro d p hp hp2 hpd hex E hE hc ⟨hout, hp3, hd, hc2⟩
  rcases hd with ⟨q, hA | hU | hB⟩ | hG | hR
  · exact seitzA3NoninnerTwo d p hp hp2 hpd hex E hE hc ⟨hout, hp3, ⟨q, hA⟩, hc2⟩
  · subst hp3
    have hlift : CentralPrimeFree 3 d.1 := by
      rw [hU]
      show ¬ (3 ∣ q.card + 1 ∧ 3 ∣ 3 + 1)
      intro h
      exact absurd h.2 (by norm_num)
    exact seitzOuter_unitary_centralPrimeFree hSU d 3 hp hp2 hpd hex E hE hc
      ⟨hout, ⟨3, q, hU⟩, hlift⟩
  · exact seitzOuter_symplectic hSp d p hp hp2 hpd hex E hE hc ⟨hout, Or.inl ⟨q, hB⟩⟩
  · exact seitzG2NoninnerTwo d p hp hp2 hpd hex E hE hc ⟨hout, hp3, hG, hc2⟩
  · exact seitzReeF4NoninnerTwo d p hp hp2 hpd hex E hE hc ⟨hout, hp3, hR⟩

theorem seitzThreeSec441NoninnerTwo_holds :
    SeitzThreeSec441NoninnerTwo := by
  exact seitzThreeSec441NoninnerTwo_holds_of_certs

end CFSG.RankThree.PartTwo.Sec19
