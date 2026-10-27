module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2Reps417Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsNoO2Normal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LargeReeParabolicHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem w4Lem4_17TwoF4N_holds
    (h43c : W3Lem45_2Chief) : W4Lem4_17TwoF4N := by
  intro W _ _ hW Y L T n hLY hTY hLT hcomp hsyl hfix hodd hTN hshape
  refine bParam_le_of_noO2_of_normal (P := fun X _ => Is2F4 n X)
    (hP := fun {X X'} _ _ e hh => Is2F4.of_mulEquiv e hh) (B := 2 * n) ?_
    hW hLY hTY hLT hcomp hsyl hfix hodd hTN hshape
  intro U _ _ hw Y L T hLT hcomp hsyl hO2 hfix hTN hPL
  exact bParam_le_two_mul_of_is2F4 h43c k_2F4ParabolicGen_holds hw hLT hcomp hsyl hO2 hfix hPL

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
