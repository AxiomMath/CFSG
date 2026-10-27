module

public import CFSG.RankThree.GF2n.Stroth80.QuadraticPlusTypeEight
import CFSG.RankThree.GF2n.Smith81.Orth28Omega

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

theorem dicksonOmegaPlusFour_holds : DicksonOmegaPlusFourStatement := by
  intro K _ _ _ hQ
  rw [commutator_orthogonalGroup_quadPlus (by norm_num : 3 ≤ 4)]
  exact Smith81.omegaGroup_le_elementaryGroup_of_four_le hQ (by simp)

end CFSG.RankThree.GF2n.Stroth80
