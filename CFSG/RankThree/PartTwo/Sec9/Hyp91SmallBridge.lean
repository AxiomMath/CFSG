module

public import CFSG.RankThree.PartTwo.Sec9.Hyp91Small
public import CFSG.RankThree.PartTwo.Sec11.Statements
import CFSG.RankThree.PartTwo.Sec11.Theorem1134
import CFSG.RankThree.PartTwo.Sec9.NotLTwoEight
import CFSG.RankThree.PartTwo.Sec9.NormalizerL

public section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace CFSG.RankThree.PartTwo.Sec9

theorem hyp91Small_of_hyp91 (h45 : Sec4.Item4_5) {G : Type} [Group G] [Finite G]
    {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R : Subgroup G}
    (h : Hyp91 G A c L a R) : Hyp91Small G A c L a R where
  toHyp81 := h.toHyp81
  card_eq := h.card_eq
  not_lTwoEight := notLTwoEight_of h45 G A c L a R h
  not_slThreePiEight := fun h8 => by
    have h1 := item93_of_item45 h45 G A c L a R 1
      ⟨h, by rwa [show (2 : ℕ) ^ (3 * 1) = 8 by norm_num]⟩
    omega
  isSylowOf := h.isSylowOf
  isSylowOf_inf := h.isSylowOf_inf
  not_mem_partTwoT_or_mem_partTwoS := h.not_mem_partTwoT_or_mem_partTwoS

theorem hyp91_of_hyp91Small {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R : Subgroup G} (h : Hyp91Small G A c L a R) :
    Hyp91 G A c L a R where
  toHyp81 := h.toHyp81
  card_eq := h.card_eq
  invTwo_or_commutator := Or.inr ⟨h.not_lTwoEight, h.not_slThreePiEight⟩
  isSylowOf := h.isSylowOf
  isSylowOf_inf := h.isSylowOf_inf
  not_mem_partTwoT_or_mem_partTwoS := h.not_mem_partTwoT_or_mem_partTwoS

theorem hyp91SmallNever_of_hyp91Never (h : Sec11.Hyp91Never) : Hyp91SmallNever :=
  fun G _ _ A c L a R hs => h G A c L a R (hyp91_of_hyp91Small hs)

end CFSG.RankThree.PartTwo.Sec9

namespace CFSG.RankThree.PartTwo.Sec11

@[expose] def Item1134E27N : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    PartTwoStanding G → A ∈ partTwoF G → A ∉ partTwoT G → Nat.card A = 27 → c ∈ A → c ≠ 1 →
    L ∈ lStarAt A c →
    Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G) →
    ¬ Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 3)) →
    ¬ Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) 8 →
    (Nat.card A = 27 → partTwoE G = partTwoF G) →
    ∀ x ∈ A, ¬ KFacts.InducesStdKind L x .field ∧ ¬ KFacts.InducesStdKind L x .graphField

theorem item1134E27N_of (h91 : Sec9.Hyp91SmallNever) : Item1134E27N := by
  intro G _ _ A c L hst hAF hAT h27 hcA hc1 hL hC hL8 hU8 hEF x hxA
  suffices hk : ¬ (KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField) from
    ⟨fun h => hk (Or.inl h), fun h => hk (Or.inr h)⟩
  intro hk
  have hx1 : x ≠ 1 := by
    rintro rfl
    rcases hk with h | h
    · exact (oneNotFieldKind G L).1 h
    · exact (oneNotFieldKind G L).2 h
  have h81 : Sec8.Hyp81 G A c L x :=
    ⟨hst, hAF, hcA, hc1, hL.2, hC, hxA, hx1, hk, fun hbig => absurd hbig (by omega), hEF⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, hR, hRW⟩ := exists_isSylowOf_inf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (Subgroup.normalizer (A : Set G))
  exact h91 G A c L x R ⟨h81, h27, hL8, hU8, hR, hRW, Or.inl hAT⟩

theorem item1134E27_of_item1134E27N (h45 : Sec4.Item4_5) (h : Item1134E27N) : Item1134E27 := by
  intro G _ _ A c L hst hAF hAT h27 hcA hc1 hL hC halt hEF x hxA
  suffices hk : ¬ (KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField) from
    ⟨fun h => hk (Or.inl h), fun h => hk (Or.inr h)⟩
  intro hk
  have hx1 : x ≠ 1 := by
    rintro rfl
    rcases hk with h | h
    · exact (oneNotFieldKind G L).1 h
    · exact (oneNotFieldKind G L).2 h
  have h81 : Sec8.Hyp81 G A c L x :=
    ⟨hst, hAF, hcA, hc1, hL.2, hC, hxA, hx1, hk, fun hbig => absurd hbig (by omega), hEF⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, hR, hRW⟩ := exists_isSylowOf_inf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (Subgroup.normalizer (A : Set G))
  have h91 : Sec9.Hyp91 G A c L x R := by
    refine ⟨h81, h27, ?_, hR, hRW, Or.inl hAT⟩
    rcases halt with ⟨E, hE, hEA, hbar⟩ | ⟨-, hA'⟩
    · have hEeq : E = A := Subgroup.eq_of_le_of_card_ge hEA (by rw [h27, hE.2.1])
      exact Or.inl (Or.inl (hEeq ▸ hbar))
    · exact Or.inl (Or.inr hA')
  have hs := Sec9.hyp91Small_of_hyp91 h45 h91
  have hx := h G A c L hst hAF hAT h27 hcA hc1 hL hC hs.not_lTwoEight hs.not_slThreePiEight hEF x
    hxA
  rcases hk with hk | hk
  · exact hx.1 hk
  · exact hx.2 hk

end CFSG.RankThree.PartTwo.Sec11
