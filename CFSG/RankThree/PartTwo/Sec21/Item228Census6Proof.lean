module

public import CFSG.RankThree.PartTwo.Sec21.Item228Census4ProofExc
public import CFSG.RankThree.PartTwo.Sec21.Item228Census6ProofD4
public import CFSG.RankThree.PartTwo.Sec21.Item228Census6ProofG2
import CFSG.RankThree.PartTwo.Sec21.Item228Census6ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree.PartTwo

theorem census228ExcTwoEvenAut_holds :
    Census228ExcTwoEvenAut := by
  intro Y _ _ hY B y N Kb m hBe hB9 hyB _ _ hnorm hKN hKb hm0 hme hor
  obtain ⟨f, hf, hG | hD⟩ := hY
  · obtain ⟨e⟩ := Item228Census6Proof.nonempty_autIn_g2 hf hG hBe hB9
    exact Item228Census6Proof.exists_of_autIn_mulEquiv_dihedral e
  · obtain ⟨T, hT2, hT1, hBT⟩ :=
      Item228Census6Proof.exists_two_subgroup_normalized hBe hyB hnorm hKN hKb hm0 hme hor
    obtain ⟨e⟩ := Item228Census6Proof.nonempty_autIn_d4 hf hD hBe hB9 hT2 hT1 hBT
    exact Item228Census6Proof.exists_of_autIn_mulEquiv_dihedral e

end CFSG.RankThree.PartTwo.Sec21
