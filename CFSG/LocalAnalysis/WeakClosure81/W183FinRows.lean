module

public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Rows
public import CFSG.LocalAnalysis.WeakClosure81.W183FinL32
public import CFSG.LocalAnalysis.WeakClosure81.W183FinG1Syl
public import CFSG.LocalAnalysis.WeakClosure81.W183FinG3
public import CFSG.LocalAnalysis.WeakClosure81.W183FinG4L34
public import CFSG.LocalAnalysis.WeakClosure81.W183FinG4A6Main
public import CFSG.LocalAnalysis.WeakClosure81.W183FinG11
public import CFSG.LocalAnalysis.WeakClosure81.W183FinGraphOdd
public import CFSG.LocalAnalysis.WeakClosure81.W183FinPairGenL28
public import CFSG.LocalAnalysis.WeakClosure81.W183FinPairGenSz8
public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44Noncyc5
public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44G2Y
public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44G45

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem w183FinBr1Rows
    (h65f : Asch6_5Four) : Br1Rows where
  a5 := finA5_holds
  u34 := finU34_holds
  l32 := finL32_holds
  a6 := finA6_holds
  sp := finG2Y_holds
  g1 := finG1_holds
  g3 := finG3_holds
  h65f := h65f
  rk2 := finRk2_holds
  rkU := finRkU34_holds
  g4l34 := finG4L34_holds
  g4a6 := finG4A6_holds
  g45 := finG45Sp44_holds
  sp5 := finSp44Noncyclic5_holds
  g11 := finG11Models_holds

theorem w183FinRows
    (h65f : Asch6_5Four) :
    Br1Rows ∧ FinPairGenL28 ∧ FinPairGenSz8 ∧ FinGraphOdd ∧ FinG1Syl ∧ FinG11Cov :=
  ⟨w183FinBr1Rows h65f, finPairGenL28_holds, finPairGenSz8_holds, finGraphOdd_holds,
    finG1Syl_holds, finG11Cov_holds⟩

end CFSG.LocalAnalysis.WeakClosure81

end
