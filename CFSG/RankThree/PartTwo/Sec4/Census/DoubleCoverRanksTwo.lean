module

public import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks
public import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanksU42
public import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanksL34
public import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanksG24

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem twoCoverRanksOpen''_psu42 :
    NoRankThreeDoubleCover (projSU 4 2 1) :=
  DoubleCoverRanksTwo.noRankThreeDoubleCover_psu42

theorem twoCoverRanksOpen''_psl34 :
    ∀ (J : Type) [Group J] [Finite J], IsTwoCover J (projSL 3 (GaloisField 2 2)) →
      CFSG.pRank 2 J = 3 → IsCyclic (Subgroup.center J) ∧ Nat.card (Subgroup.center J) = 4 :=
  DoubleCoverRanksTwo.psl34_center

theorem twoCoverRanksOpen''_g24 :
    ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid), q.p = 2 →
      q.exponent = 2 → NoRankThreeDoubleCover (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group :=
  DoubleCoverRanksTwo.noRankThreeDoubleCover_g24

theorem twoCoverRanksOpen'' :
    TwoCoverRanksOpen'' where
  psu42 := twoCoverRanksOpen''_psu42
  psl34 := twoCoverRanksOpen''_psl34
  g24 := twoCoverRanksOpen''_g24

end CFSG.RankThree.PartTwo.Sec4.Census
