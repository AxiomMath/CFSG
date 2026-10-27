module

public import CFSG.RankThree.PartTwo.Sec11.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item1134Four :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    PartTwoStanding G → A ∈ partTwoF G → Nat.card A = 3 ^ 4 → c ∈ A → c ≠ 1 →
    L ∈ lStarAt A c →
    Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G) →
    (∃ E ∈ partTwoE G, E ≤ A ∧ Sec8.InvTwoBarNontrivial E L) →
    ∀ x ∈ A, ¬ KFacts.InducesStdKind L x .field ∧ ¬ KFacts.InducesStdKind L x .graphField

theorem Item223PrintProof.not_mem_partTwoT_of_card_eq {G : Type} [Group G] [Finite G]
    {A : Subgroup G} (hA : Nat.card A = 3 ^ 4) : A ∉ partTwoT G := fun hT => by
  have h27 := hT.1.2.1
  rw [hA] at h27
  norm_num at h27

theorem item1134Four_of_item1134
    (h : Sec11.Item1134) :
    Item1134Four := by
  intro G _ _ A c L hst hAF hA81 hcA hc1 hL hC halt x hxA
  exact h G A c L hst hAF (Item223PrintProof.not_mem_partTwoT_of_card_eq hA81) hcA hc1 hL hC
    (Or.inl halt)
    (fun h27 => absurd (h27.symm.trans hA81) (by norm_num)) x hxA

end CFSG.RankThree.PartTwo.Sec21
