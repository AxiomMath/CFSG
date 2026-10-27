module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec91N5
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91QB
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91Cent
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec92Quot

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

theorem split95_of_step94 (h92 : Stroth92Statement) (hB : Step94ConjVStatement)
    {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {s : G} (hs0 : s ∈ Z0) {x : G} (hxL : x ∈ LB M Q B) (hxN : x ∉ hc.CN t)
    (hconj : ConjMod M Q s x) {Y : Subgroup G}
    (hdp : IsDirectProdQuot (Rt M (LB M Q B) t) (Sec9R0 hc t x) Y Q)
    (hYsl : QuotSat Y Q (IsSLModel 2 (Nat.card Z))) :
    HS9.Split95 M Q Z B t (Sec9R0 hc t x) Y := by
  have hVW := hB G M Q Z B hc n t hs _ _ rfl rfl Z0 hZ0 s hs0 x hxL hxN hconj
  exact ⟨hdp, hYsl, (h92 G M Q Z B hc n t hs _ _ rfl rfl x hxL hxN hVW).2⟩

theorem stroth92_of_split (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bCard : Stroth311bCardStatement) (h311bComm : Stroth311bCommStatement)
    (hSplit : Step92SplitStatement) : Stroth92Statement := by
  have hNC := sec9NComm_of_311b h34 h311bComm
  have hA := sec9AExists_of h34 h311a hNC
  have h91b : Stroth91bStatement := stroth91b_of_steps h34 h311a hNC (step91OrderQB_of h34)
    (step91OrderVQB_of h34) (step91Inter_of h34) (step91MixedComm_of h34)
  have hn5 := sec9NGeFive_of h34 h311a h311bComm h311bCard
  exact stroth92_of_steps hA h91b
    (step92Nontriv_of h34 hA h91b hn5 (step91OrderQB_of h34) (step91OrderVQB_of h34))
    step92Quot hSplit

end CFSG.RankThree.GF2n.Stroth80
