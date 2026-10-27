module

public import CFSG.Quasithin.EmptyFaithful.S151XF

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def ListBSL15120 {G : Type} [Group G] (L : Subgroup G) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧
    IsPSL 3 2 n ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))

@[expose] def ListB15120' {G : Type} [Group G] (L : Subgroup G) : Prop :=
  ListB15120 L ∨ ListBSL15120 L

@[expose] def Input15120B42ListF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → CharTwo L →
    ListA15120 L ∨ ListB15120' L ∨ ListC15120 L ∨ ListD15120 L

@[expose] def Input15120RankTwoExclF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → CharTwo L → ListB15120' L → False

theorem listB15120_le' {G : Type} [Group G] {L : Subgroup G} (h : ListB15120 L) : ListB15120' L :=
  Or.inl h

theorem input15120_pair_of_faithful (h1 : Input15120B42ListF) (h2 : Input15120RankTwoExclF) :
    Input15120B42List ∧ Input15120RankTwoExcl := by
  refine ⟨fun G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hchar => ?_, fun G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hB =>
    h2 G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar (listB15120_le' hB)⟩
  rcases h1 G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar with h | h | h | h
  · exact Or.inl h
  · exact (h2 G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar h).elim
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

end CFSG.Quasithin
