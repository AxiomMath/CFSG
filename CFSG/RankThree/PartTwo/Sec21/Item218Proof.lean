module

public import CFSG.RankThree.PartTwo.Sec21.Item21Statements
public import CFSG.RankThree.PartTwo.Sec21.Item215

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.Blueprint

@[expose] def IsList218 {G : Type} [Group G] [Finite G] (L : Subgroup G) : Prop :=
  Nonempty (lBar L ≃* NativeSporadic.M24) ∨ Nonempty (lBar L ≃* NativeSporadic.He) ∨
    Nonempty (lBar L ≃* NativeSporadic.J2) ∨ Nonempty (lBar L ≃* NativeSporadic.Ru) ∨
    Nonempty (lBar L ≃* NativeSporadic.J4) ∨
    (∃ n : ℕ, ChevalleyExceptionalModel (lBar L) .G2 2 n) ∨
    ∃ n : ℕ, ChevalleyExceptionalModel (lBar L) .trialityD4 2 n

theorem item218_of_not_isList218
    (h : ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
      Sec21Pair G A E U c L → ¬ IsList218 L) : Item218 := by
  intro G _ _ A E U c L hpair
  have hL := h G A E U c L hpair
  refine ⟨not_nonempty_iff.mp fun e => hL (Or.inl e),
    not_nonempty_iff.mp fun e => hL (Or.inr (Or.inl e)),
    not_nonempty_iff.mp fun e => hL (Or.inr (Or.inr (Or.inl e))),
    not_nonempty_iff.mp fun e => hL (Or.inr (Or.inr (Or.inr (Or.inl e)))),
    not_nonempty_iff.mp fun e => hL (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))),
    fun n hn => hL (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn⟩)))))),
    fun n hn => hL (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, hn⟩))))))⟩

@[expose] def Item218Normal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L →
      Subgroup.normalizer (A : Set G) ≤
        Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G)

@[expose] def Item218Step214 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L U₀ : Subgroup G) (b : G)
    (K : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → U₀ ∈ fourGroupsMinus E → U₀ ≤ L →
    b ∈ E ⊓ Subgroup.centralizer (U₀ : Set G) → b ∉ Subgroup.zpowers c →
    K ∈ lThreeStarAt A b → (b, K) ∈ lThreeStarPairs A E U₀ → IsList218 K

@[expose] def Item218Final : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L U₀ : Subgroup G) (b : G)
    (K : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → U₀ ∈ fourGroupsMinus E → U₀ ≤ L →
    Sec21Pair G A E U₀ b K → IsList218 K → b ∈ E ⊓ Subgroup.centralizer (U₀ : Set G) →
    b ∉ Subgroup.zpowers c →
    Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) →
    Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers b : Subgroup G) : Set G) → False

@[expose] def KF218NotU4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsList218 L →
    ¬ ∃ n : ℕ, Odd n ∧ Nonempty (L ≃* projSU 4 2 n)

theorem exists_pair_of_isList218 (h214 : Item214) (h215 : Item215) (hU4 : KF218NotU4)
    (h2114 : Item218Step214) {G : Type} [Group G] [Finite G] {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hL : IsList218 L) :
    ∃ (U₀ : Subgroup G) (b : G) (K : Subgroup G), U₀ ∈ fourGroupsMinus E ∧ U₀ ≤ L ∧
      b ∈ E ⊓ Subgroup.centralizer (U₀ : Set G) ∧ b ∉ Subgroup.zpowers c ∧
      Sec21Pair G A E U₀ b K ∧ IsList218 K := by
  obtain ⟨U₀, hU₀, hU₀L⟩ := (h214 G A E U c L hpair).mpr (hU4 G L hL)
  obtain ⟨b, hb, hbc, K, hK, hbK⟩ := h215 G A E U c L hpair U₀ hU₀
  have hpair' : Sec21Pair G A E U₀ b K :=
    { toSec21Std := hpair.toSec21Std
      mem_E := hpair.mem_E
      mem_U := hU₀.1
      mem_pair := hbK }
  exact ⟨U₀, b, K, hU₀, hU₀L, hb, hbc, hpair',
    h2114 G A E U c L U₀ b K hpair hL hU₀ hU₀L hb hbc hK hbK⟩

theorem item218_of_steps (h214 : Item214) (h215 : Item215) (hU4 : KF218NotU4)
    (hN : Item218Normal) (h2114 : Item218Step214) (hF : Item218Final) : Item218 := by
  refine item218_of_not_isList218 fun G _ _ A E U c L hpair hL => ?_
  obtain ⟨U₀, b, K, hU₀, hU₀L, hb, hbc, hpair', hK⟩ :=
    exists_pair_of_isList218 h214 h215 hU4 h2114 hpair hL
  exact hF G A E U c L U₀ b K hpair hL hU₀ hU₀L hpair' hK hb hbc
    (hN G A E U c L hpair hL) (hN G A E U₀ b K hpair' hK)

end CFSG.RankThree.PartTwo.Sec21
