module

public import CFSG.RankThree.PartTwo.Sec11.Item116R1A
public import CFSG.RankThree.PartTwo.Sec11.Item116R1PCore
public import CFSG.RankThree.PartTwo.Sec11.Item116E2
public import CFSG.RankThree.PartTwo.Sec11.Item116H3Main
public import CFSG.RankThree.PartTwo.Sec11.Item116R2NoHoles
public import CFSG.RankThree.PartTwo.Sec11.LSSolvableProof

public section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG.Assembly.RankThreeEven (projSL)

section Certified

theorem residueTR1_of_pieces
    (hB : KFacts.BlackburnRankTwo) (hLin : KFacts.NoDoubleComponentGL)
    (hFC : FactFieldCentralizerL2Odd) (hFC3 : FactFieldCentralizerL3)
    (h45 : Sec4.Item4_5) (h113 : Item113) (hcore : Item116P2bCore) (hP2c : Item116P2c)
    (hPC : ResidueR1PCore) (hA : ResidueR1TwoStarA) (hCD : ResidueR1TwoStarCD)
    (hC38 : ResidueR1TwoStarCL38) (hCodd : ResidueR1TwoStarCOdd) : ResidueTR1 := by
  intro G _ _ A c L a R Y d h hR1
  by_contra hT
  have hs := h.toSec11Std hT
  have hP2b := item116P2b_of_core h45 hcore
  have hKF : KFAt L a :=
    kfAt_of_pCore_ne_bot hB hLin hP2b h hT hR1 (hPC G A c L a R Y d h hT hR1)
  have hC2 := twoStarAtC_of h45 landazuriSeitzL2EvenSolvable
  rcases isList1016_cases hs.isList1016 with ⟨p, e, hp, hp3, he, hL⟩ | hev
  · by_cases he1 : e = 1
    · subst he1
      have hsurv : IsSurvivingCase L := Or.inr (Or.inr ⟨p, hp, hp3, hL⟩)
      exact hT (mem_partTwoT_of_R1 hP2b hP2c h45 h hT hR1
        (hCodd G A c L a R Y d h hT hR1 ⟨p, hp, hp3, hL⟩)
        (hCD G A c L a R Y d h hT hR1 hsurv hKF)
        (hA G A c L a R Y d h hT hR1 hsurv hKF) hKF)
    · exact theorem85 hB hFC h45 h113 hcore h hT hp3 (by omega) hL
  · rcases hev with ⟨m, hm, hL2⟩ | ⟨m, hm1, hL3⟩
    · have hsurv : IsSurvivingCase L := Or.inl ⟨m, hm, hL2⟩
      exact hT (mem_partTwoT_of_R1 hP2b hP2c h45 h hT hR1
        (hC2 G A c L a R Y d h hT m hm hL2)
        (hCD G A c L a R Y d h hT hR1 hsurv hKF)
        (hA G A c L a R Y d h hT hR1 hsurv hKF) hKF)
    · by_cases hm2 : 2 ≤ m
      · exact false_of_R1_l3 hB hFC3 h45 hcore h hT hm2 hL3 hR1
      · have hm1' : m = 1 := by omega
        subst hm1'
        have hL38 : IsL3Eight L := hL3
        have hsurv : IsSurvivingCase L := Or.inr (Or.inl hL38)
        exact hT (mem_partTwoT_of_R1 hP2b hP2c h45 h hT hR1
          (hC38 G A c L a R Y d h hT hR1 hL38)
          (hCD G A c L a R Y d h hT hR1 hsurv hKF)
          (hA G A c L a R Y d h hT hR1 hsurv hKF) hKF)

theorem residueTR1_of_remaining
    (hB : KFacts.BlackburnRankTwo) (hLin : KFacts.NoDoubleComponentGL)
    (hFC : FactFieldCentralizerL2Odd) (hFC3 : FactFieldCentralizerL3)
    (h45 : Sec4.Item4_5) (h113 : Item113) (hcore : Item116P2bCore) (hP2c : Item116P2c)
    (h5 : FiveCaseCore) (hCD : ResidueR1TwoStarCD) (hC38 : ResidueR1TwoStarCL38)
    (hCodd : ResidueR1TwoStarCOdd) : ResidueTR1 :=
  residueTR1_of_pieces hB hLin hFC hFC3 h45 h113 hcore hP2c
    (residueR1PCore_of_five (item116P2b_of_core h45 hcore) hP2c h45 h5)
    (twoStarAtA_of (item116P2b_of_core h45 hcore) hP2c h45) hCD hC38 hCodd

end Certified

end CFSG.RankThree.PartTwo.Sec11
