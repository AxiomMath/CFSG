module

public import CFSG.RankThree.GF2n.Stroth80.Sec57
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def CaseVIMeetStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z X B : Subgroup G), Ctx M Q Z X → Ctx M Q Z B →
    ∀ n : ℕ, Width Q Z n → 2 < n → CaseVI M Q Z (Lgen M (LB M Q X)) →
    ¬ (LB M Q B ⊓ Lgen M (LB M Q X) ≤ Q)

@[expose] def CaseVIClosureStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z X B : Subgroup G), Ctx M Q Z X → Ctx M Q Z B →
    ∀ n : ℕ, Width Q Z n → 2 < n → CaseVI M Q Z (Lgen M (LB M Q X)) →
    NoA2 Q Z (LB M Q B) → LB M Q B ⊓ Lgen M (LB M Q X) ≤ Q

theorem strothNoA2Spread_of_inputs (h1111 : Stroth1111Statement)
    (hmeet : CaseVIMeetStatement) (hclosure : CaseVIClosureStatement) :
    StrothNoA2SpreadStatement := by
  intro G _ _ M Q Z B hc n hw hn hno _ B' hc' a ha hA2
  have hCase := h1111 G M Q Z B' hc' n hw hn ⟨a, ha, hA2⟩
  exact hmeet G M Q Z B' B hc' hc n hw hn hCase
    (hclosure G M Q Z B' B hc' hc n hw hn hCase hno)

end CFSG.RankThree.GF2n.Stroth80
