module

public import CFSG.RankThree.GF2n.Tim81.Induction
public import CFSG.RankThree.GF2n.Tim81.Sec5.OfStatements
public import CFSG.RankThree.GF2n.Tim81.Sec5.S51S52
public import CFSG.RankThree.GF2n.Tim81.Sec6.S61

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75

@[expose] def Sec5ResultsStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Sec5Results G

@[expose] def Sec65Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V : Subgroup G), Sec6Hyp M V → ∀ n : ℕ,
    Nat.card ↥(Pc M V) = Nat.card V ^ (2 * n + 1) → n ≤ 3 → UnitaryConclusion V

@[expose] def Sec7Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Theorem1Below (Nat.card G) → ∀ M V : Subgroup G,
    Sec6Hyp M V → ∀ n : ℕ, Nat.card ↥(Pc M V) = Nat.card V ^ (2 * n + 1) → 4 ≤ n →
      UnitaryConclusion V

theorem sections4to7Statement_of (h79 : Tim79aStatementWCQ) (h45 : Sec45Statement)
    (h5 : Sec5ResultsStatement) (h65 : Sec65Statement) (h7 : Sec7Statement) :
    Sections4to7Statement := by
  intro G _ _ hb M V h ⟨H, hH⟩
  have hS : Sec6Hyp M V :=
    ⟨Sec5Hyp.of_statements h79 h45 h, h.sigmaSet_nonempty hH (h.le_pCore_of_isHMember h79 hH),
      h5 G⟩
  obtain ⟨n, -, hn, -⟩ := hS.stmt61b
  rcases le_or_gt n 3 with h3 | h4
  · exact h65 G M V hS n hn h3
  · exact h7 G hb M V hS n hn h4

end CFSG.RankThree.GF2n.Tim81
