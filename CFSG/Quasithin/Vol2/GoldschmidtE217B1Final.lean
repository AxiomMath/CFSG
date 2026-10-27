module

public import CFSG.Quasithin.Vol2.GoldschmidtE217B1A6Main
public import CFSG.Quasithin.Vol2.GoldschmidtE217B1L32
public import CFSG.Quasithin.Vol2.GoldschmidtE217E4Final
public import CFSG.Quasithin.Vol2.GoldschmidtE217L33Main

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique E217R1 E217R3

namespace E217R4

theorem r3Pkg2bOne
    (p7 : R3Pkg2c7) :
    R3Pkg2bOne := by
  intro G _ _ H T M V K hS hlt hC2 hshape hdiag hB
  rcases hshape with hL32 | hA6
  · exact r3Pkg2bOne_L32 p7 hS hlt hC2 hL32 hdiag hB
  · exact r3Pkg2bOne_A6 hS hC2 hA6 hdiag

theorem e217NonsolvableNarrow_of_leaf
    (hL : R1Leaves) (h22 : E2.E22StatementNoN) (hNot : KFactL3U3NotOddCube) (p2c : R3Pkg2c7) :
    E2.E217NonsolvableNarrow :=
  e217NonsolvableNarrow_of_three_leaves hL h22 hNot (r3Pkg2bOne p2c) p2c r3Pkg2d3

end E217R4

end CFSG.Quasithin
