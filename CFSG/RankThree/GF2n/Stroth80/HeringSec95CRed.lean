module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

@[expose] def Step95CentreStatementFrom (n0 : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → n0 ≤ n → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
      HS9.Centre95 hc t Z0

@[expose] def Step95ChoiceStatementFrom (n0 : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G)
    (Z0 : Subgroup G), HS9.Cfg95 hc n t Z0 → n0 ≤ n → ∃ z : G, HS9.ZPair95 hc t Z0 z

@[expose] def Step95OneStatementFrom (n0 : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G)
    (Z0 : Subgroup G), HS9.Cfg95 hc n t Z0 → n0 ≤ n → HS9.One95 hc t Z0

@[expose] def Sec95ExcludedStatement (n0 : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → 6 < n → n < n0 → False

theorem sec95Excluded_seven : Sec95ExcludedStatement 7 := by
  intro G _ _ M Q Z B hc n t hs h1 h2
  omega

end CFSG.RankThree.GF2n.Stroth80
