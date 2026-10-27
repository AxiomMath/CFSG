module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res3ProofAsc93
import CFSG.RankThree.PartTwo.Sec19.Step1910Proof
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
public import CFSG.RankThree.PartTwo.Sec20.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec20
open CFSG.AGLEmbedding (Asc81bEightFour Asc81bNineThree)

theorem three_dvd_card_of_wide
    {Y : Type} [Group Y]
    (hY : IsList194 Y ∨ IsSmall194 Y ∨ IsTripleA6 Y) : 3 ∣ Nat.card Y := by
  rcases hY with hl | hsm | ht
  · exact Step1910Proof.three_dvd_card_of_isList194 hl
  · exact Step1910Proof.three_dvd_card_of_isSmall194 hsm
  · rw [← ht.1]
    exact Subgroup.card_subgroup_dvd_card _

end CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof
