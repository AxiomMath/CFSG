module

public import CFSG.RankThree.PartTwo.KFacts.KSL3PiOrder3TypeC
import CFSG.RankThree.PartTwo.Sec15.NoModNine
public import CFSG.RankThree.PartTwo.Sec13.Item138N
public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem step169U38_of (h138 : Item138N) (hK : KFacts.KSL3PiOrder3TypeC) (h1616 : Step1616) :
    Step169U38 := by
  intro G _ _ A c L hc
  refine ⟨fun φ => ?_⟩
  obtain ⟨n, -, -, hprod⟩ := h1616 G A c L hc
  have hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 3 :=
    Or.inr ⟨by norm_num, ⟨φ⟩⟩
  exact Sec15.not_modNine_of_inner hc.toSec15R h138 hK (by norm_num) hiso hprod (by norm_num)

theorem step169U38_of_item138N (h138 : Item138N) (h1616 : Step1616) : Step169U38 :=
  step169U38_of h138 KFacts.kSL3PiOrder3TypeC h1616

end CFSG.RankThree.PartTwo.Sec16
