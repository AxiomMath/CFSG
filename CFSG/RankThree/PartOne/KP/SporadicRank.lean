module

public import CFSG.RankThree.PartOne.KP.SporadicRankMathieu
public import CFSG.RankThree.PartOne.KP.SporadicRankPairs
public import CFSG.RankThree.PartOne.KP.SporadicRankHe
public import CFSG.RankThree.PartOne.KP.SporadicRankMcL
public import CFSG.RankThree.PartOne.KP.SporadicRankFi22
public import CFSG.RankThree.PartOne.KP.SporadicRankFi23
public import CFSG.RankThree.PartOne.KP.SporadicRankFi24
public import CFSG.RankThree.PartOne.KP.SporadicRankSuz
public import CFSG.RankThree.PartOne.KP.SporadicRankRu
public import CFSG.RankThree.PartOne.KP.SporadicRankON
public import CFSG.RankThree.PartOne.KP.SporadicRankCo1
public import CFSG.RankThree.PartOne.KP.SporadicRankCo2
public import CFSG.RankThree.PartOne.KP.SporadicRankCo3

public section

namespace CFSG.RankThree.PartOne

structure SporadicCoprimeRankData : Prop where
  hn : SporadicCoprimeRank .HN
  ly : SporadicCoprimeRank .Ly
  th : SporadicCoprimeRank .Th

theorem sporadicCoprimeRank_of_data (h : SporadicCoprimeRankData) (s : TauCeti.SporadicName)
    (hs : s ≠ .J4 ∧ s ≠ .B ∧ s ≠ .M) : SporadicCoprimeRank s :=
  match s, hs with
  | .M11, _ => sporadicCoprimeRank_M11
  | .M12, _ => sporadicCoprimeRank_M12
  | .M22, _ => sporadicCoprimeRank_M22
  | .M23, _ => sporadicCoprimeRank_M23
  | .M24, _ => sporadicCoprimeRank_M24
  | .J1, _ => sporadicCoprimeRank_J1
  | .J2, _ => sporadicCoprimeRank_J2
  | .J3, _ => sporadicCoprimeRank_J3
  | .J4, hs => absurd rfl hs.1
  | .Co1, _ => sporadicCoprimeRank_Co1
  | .Co2, _ => sporadicCoprimeRank_Co2
  | .Co3, _ => sporadicCoprimeRank_Co3
  | .Fi22, _ => sporadicCoprimeRank_Fi22
  | .Fi23, _ => sporadicCoprimeRank_Fi23
  | .Fi24Prime, _ => sporadicCoprimeRank_Fi24Prime
  | .HS, _ => sporadicCoprimeRank_HS
  | .McL, _ => sporadicCoprimeRank_McL
  | .He, _ => sporadicCoprimeRank_He
  | .Ru, _ => sporadicCoprimeRank_Ru
  | .Suz, _ => sporadicCoprimeRank_Suz
  | .ONan, _ => sporadicCoprimeRank_ONan
  | .HN, _ => h.hn
  | .Ly, _ => h.ly
  | .Th, _ => h.th
  | .B, hs => absurd rfl hs.2.1
  | .M, hs => absurd rfl hs.2.2

end CFSG.RankThree.PartOne
