module

public import CFSG.RankThree.PartTwo.Sec21.Item211ProofList

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem mem_partTwoE_of_card {G : Type} [Group G] [Finite G] {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (h27 : Nat.card A = 3 ^ 3) : A ∈ partTwoE G := by
  obtain ⟨hE, hEA⟩ := hpair.mem_E
  have hEA' : E = A := Subgroup.eq_of_le_of_card_ge hEA (by rw [h27, hE.2.1]; norm_num)
  exact hEA' ▸ hE

section Certs

@[expose] def Item211NoFieldThreeT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 3 → A ∈ partTwoT G →
      ∀ x ∈ A, ¬ KFacts.InducesStdKind L x .field ∧ ¬ KFacts.InducesStdKind L x .graphField

theorem item211NoFieldThree_of
    (h1134 : Sec11.Item1134E27) (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (hT : Item211NoFieldThreeT) : Item211NoFieldThree := by
  intro G _ _ A E U c L hpair h27 x hx
  by_cases hAT : A ∈ partTwoT G
  · exact hT G A E U c L hpair h27 hAT x hx
  · have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
    have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
    have hL : L ∈ lStarAt A c :=
      ⟨lZeroStar_subset_lStar A (lZeroStarAt_subset_lZeroStar A c hpairs.2.2.1),
        (lZeroStarAt_subset A c) hpairs.2.2.1⟩
    exact h1134 G A c L hpair.standing hpair.mem_S.1 hAT (by rw [h27]; norm_num) hcA
      hpairs.2.1 hL (Item211Proof.sectionCentralizer_eq h45 h66 hpair)
      (Or.inl (Item211Proof.exists_invTwoBarNontrivial hpair))
      (fun _ => hpair.side (mem_partTwoE_of_card hpair h27)) x hx

end Certs

end CFSG.RankThree.PartTwo.Sec21
