module

public import CFSG.CGT.PushingUpLit.BHS6.ThreeEightGaps
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearCentralCover

public section

namespace CFSG.RankThree.PartOne.KEXC

theorem sl2EvenMultiplierTrivial_holds : CFSG.CGT.PushingUpLit.BHS6.SL2EvenMultiplierTrivial :=
  fun n hn _ _ _ π hπ hker hp hperf => by
    have := hperf
    exact CFSG.ShultStronglyClosedTI.large_even_linear_central_two_cover_kernel_eq_bot n hn
      (GaloisField.card 2 n (by omega)) π hπ hker hp

end CFSG.RankThree.PartOne.KEXC
