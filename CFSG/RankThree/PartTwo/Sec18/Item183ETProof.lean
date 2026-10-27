module

public import CFSG.RankThree.PartTwo.Sec18.Item183KT
public import CFSG.RankThree.PartTwo.Sec12.Item128Bar
public import CFSG.RankThree.PartTwo.Sec17.Item17Statements
public import CFSG.RankThree.PartTwo.Sec18.Item183KStatements

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

theorem item183ET_of (h1210 : Sec12.Item1210BarS) (h1730 : Sec17.Item1730) : Item183ET := by
  intro G _ _ A M c K E hD
  obtain ⟨e⟩ := hD.quotient_iso
  rcases h1210 G E c K hD.sec12StdBar hD.E_mem_partTwoE hD.partTwoS_eq
      (Or.inl (isSLThreePi_of_SL34 e)) with hET | ⟨-, -, -, -, a, -, -, I, -, hHJ, ha, hI⟩
  · exact hET
  by_contra hET
  obtain ⟨-, hempty⟩ :=
    h1730 G hD.toPartTwoStanding hD.partTwoS_eq E hD.E_mem_partTwoE hET a ha I hI
  obtain ⟨φ⟩ := hHJ
  exact hempty.false φ

end CFSG.RankThree.PartTwo.Sec18
