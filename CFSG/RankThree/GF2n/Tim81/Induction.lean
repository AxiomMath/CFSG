module

public import CFSG.RankThree.GF2n.Tim81.RootType

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75

@[expose] def Theorem1For (G : Type) [Group G] : Prop :=
  ∀ M V : Subgroup G, Hyp M V → 4 ≤ Nat.card V → WeaklyClosedIn V (inSubgroup (pCore 2) M) →
    WeaklyClosedIn V M ∨ UnitaryConclusion V ∨ ∀ H : Subgroup G, ¬ IsHMember M V H

@[expose] def Theorem1Below (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → Theorem1For G

@[expose] def Sections4to7Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Theorem1Below (Nat.card G) →
    ∀ M V : Subgroup G, RootHyp M V → (∃ H : Subgroup G, IsHMember M V H) → UnitaryConclusion V

variable {G : Type} [Group G]

theorem theorem1For_of_below [Finite G] (h79 : Tim79aStatementWCQ) (h47 : Sections4to7Statement)
    (hb : Theorem1Below (Nat.card G)) : Theorem1For G := by
  intro M V h h4 hwc
  by_cases hwcM : WeaklyClosedIn V M
  · exact Or.inl hwcM
  by_cases hH : ∃ H : Subgroup G, IsHMember M V H
  · exact Or.inr (Or.inl (h47 G hb M V
      (h.rootHyp h79 h4 hwc hwcM) hH))
  · exact Or.inr (Or.inr fun H hH' => hH ⟨H, hH'⟩)

theorem theorem1Statement_of_sections4to7 (h79 : Tim79aStatementWCQ)
    (h47 : Sections4to7Statement) :
    Theorem1Statement := by
  have key : ∀ n, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → Theorem1For G := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro G _ _ hn
      exact theorem1For_of_below h79 h47 fun G' _ _ hG' => ih _ (hn ▸ hG') G' rfl
  intro G _ _
  exact key _ G rfl

end CFSG.RankThree.GF2n.Tim81
