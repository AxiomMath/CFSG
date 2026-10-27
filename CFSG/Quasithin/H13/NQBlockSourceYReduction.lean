module

public import CFSG.Quasithin.H13.NQBlockNonquasisimpleConfine
public import CFSG.Quasithin.H13.NQBlockSourceCommutator

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open

theorem originalKEscapingSourceY_of_complementary
    (h1323 : Stmt13_1_2_three) (hB : ComplementaryEscapeSimpleSourceY) :
    OriginalKEscapingSourceY :=
  originalKEscapingSourceY_of_sourceY
    (originalKContainingConfinement_of_confinement originalKNonquasisimpleConfinement_holds h1323)
    allComponentsContainedSourceY_holds hB

end CFSG.Quasithin.H13.NQBlock
