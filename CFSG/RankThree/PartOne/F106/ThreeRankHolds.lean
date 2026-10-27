module

public import CFSG.RankThree.PartOne.F106.FiveRank
public import CFSG.RankThree.PartOne.F106.F4Three
public import CFSG.RankThree.PartOne.F106.U6Three

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.F106

section F4

theorem f4ThreeRank_holds : F4ThreeRank := fun T _ hT D hD hcard => by
  have := hD
  exact f4_no_elemAbelian_five hT D
    (fun a ha b hb => congrArg Subtype.val
      (hD.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
    (fun a ha => CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) a ha) hcard

end F4

theorem u6ThreeRank_holds : U6ThreeRank :=
  fun T _ hmod D hD hcard => by
  have := hD
  exact u6_no_elemAbelian_five hmod D
    (fun a ha b hb => congrArg Subtype.val
      (hD.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
    (fun a ha => CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) a ha) hcard

end CFSG.RankThree.PartOne.F106
