module

public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusResidual
public import CFSG.RankThree.PartTwo.Sec6.HeringB3D4
public import CFSG.RankThree.PartTwo.Sec6.HeringB3F4
public import CFSG.RankThree.PartTwo.Sec6.HeringB3U4Even
public import CFSG.RankThree.PartTwo.Sec6.HeringB3U4Odd

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.Blueprint CFSG.Assembly.RankThreeEven
open BThreeCensus

section Certs


theorem threePrimeB3OddChar46Rest_holds : ThreePrimeB3OddChar46Rest := by
  intro X _ _ _ hX
  obtain ⟨p, hpf, hp3, hmodel⟩ := hX
  rcases hmodel with hG2 | ⟨hp1, ⟨e⟩⟩
  · exact threePrimeB3_of_chevalleyG2_odd hp3 hG2
  · exact threePrimeB3_of_projSU_four_prime hp3 hp1 e

theorem threePrimeB3EvenChar46Rest_holds : ThreePrimeB3EvenChar46Rest := by
  intro X _ _ _ hX
  rcases hX with ⟨n, hn, ⟨e⟩⟩ | ⟨f, hG2 | hD4 | hF4⟩
  · exact threePrimeB3_of_projSU_four_charTwo hn e
  · exact threePrimeB3_of_chevalleyG2_even hG2
  · exact threePrimeB3_of_chevalleyTriality hD4
  · exact threePrimeB3_of_reeTitsModel hF4

theorem threePrimeB3Residual46Rest_holds : ThreePrimeB3Residual46Rest :=
  ⟨threePrimeB3OddChar46Rest_holds, threePrimeB3EvenChar46Rest_holds⟩

end Certs

end CFSG.RankThree.PartTwo.Sec6
