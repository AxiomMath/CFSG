module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL28
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4Two14Outer
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4Two20Twist
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4Four16
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL6Two15
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL7Two21
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinU4Two14
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinE6

public section

namespace CFSG.LocalAnalysis.WeakClosure81


theorem chev135Rows_holds : Chev135Rows :=
  ⟨finL28Steinberg_holds, finRowStmt_psl_four_two_of_ranks 14 innerRankFour_fourteen
      outerRankFour_fourteen, finRowStmt_psl_four_two_of_ranks 20 innerRankFour_twenty
          outerRankFour_twenty, finL4Four16_holds, finL6Two15_holds,
    finL7Two21_holds, finU4Two14_holds, finE6Two27_holds⟩

end CFSG.LocalAnalysis.WeakClosure81
