module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Card
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three
import CFSG.LocalAnalysis.UniquenessCase.UC7P3Good
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F07

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (Sec7Core4 StronglyEmbeddedFive StronglyEmbeddedThree)

variable {G : Type} [Group G] [Finite G]

theorem r74Card_dataOfSetup (hSE : StronglyEmbeddedFive) (hK3 : StronglyEmbeddedThree)
    (hS : RankThreeUC.Standing G) (hUC : CFSG.Open.rankThreeUC G)
    (hC : RankThreeUC.AGL81TheoremC G) (S : RankThreeUC.Setup G) :
    R74Card (PartTwo.Three.dataOfSetup hS S) := by
  intro p H hH
  obtain ⟨hpp, hp2, hsp, htop, hHM, hrank⟩ := hH
  let k : Sec7Core4 G := Sec7Core4.ofThree hS S.M S.witness.maxLocal p hpp hp2 hsp
    (PartTwo.Three.normalizer_le_of_agl81TheoremC hUC hC S hpp hp2 hsp)
  have hk : k.Config H := ⟨htop, hHM, hrank⟩
  by_cases hp3 : p = 3
  · exact k.step74w_of_stronglyEmbeddedThree hp3 hK3 H hk
  have h5 : 5 ≤ k.p := Nat.Prime.five_le_of_ne_two_of_ne_three hpp hp2 hp3
  exact (k.step74_of_kIDExcluded h5 (k.kIDExcluded_of_evenRank_le_three (le_of_eq hS.rank))
    hSE).toWeak H hk

end CFSG.LocalAnalysis.UniquenessCase.UC22.F07
