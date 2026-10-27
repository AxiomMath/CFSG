module

public import CFSG.RankThree.PartTwo.Sec6.Item611Res3ProofE81Lift
public import CFSG.RankThree.PartTwo.Sec6.Item611Res4ProofE81McL
public import CFSG.RankThree.PartTwo.Sec6.Item611Res4ProofE81L43
public import CFSG.RankThree.PartTwo.Sec6.Item611Res4ProofE81U43

public section

namespace CFSG.RankThree.PartTwo.Sec6

theorem kS611E81Inv_holds :
    KS611E81Inv := by
  intro X _ _ hX B hB h81
  rcases hX with hX | hX | hX
  · obtain ⟨φ⟩ := hX
    exact Res611Res4.e81InvAt_of_mulEquiv_mcl φ B hB h81
  · obtain ⟨φ⟩ := hX
    exact Res611Res4.e81InvAt_of_mulEquiv_l43 φ B hB h81
  · obtain ⟨φ⟩ := hX
    exact Res611Res4.U43.e81InvAt_of_mulEquiv_u43 φ B hB h81

end CFSG.RankThree.PartTwo.Sec6
