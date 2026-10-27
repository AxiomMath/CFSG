module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCFoote
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.GF2n

open CFSG CFSG.Open

theorem stroth80_artin_sp_order (m : ℕ) (K : Type) [Field K] [Finite K] :
    Nat.card (StatedSp m K) = CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.spOrder m (Nat.card K) :=
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp m

end CFSG.RankThree.GF2n
