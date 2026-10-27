module

public import CFSG.Quasithin.Vol2.Ch11SecO7t
public import CFSG.Quasithin.Vol2.Ch11SecO7s

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE.C10KH

open CFSG.Open CFSG.Blueprint

@[expose] def InLists (X : Type) [Group X] (n : ℕ) : Prop :=
  2 ≤ n ∧ (List11_1_1Two X n ∨ (n = 2 ∧ List11_1_1Three X)) ∧ ¬ A36Case4 X ∧ ¬ IsSL2pE X


variable {X : Type} [Group X] {n : ℕ}

theorem lists_ge (h : InLists X n) : Nat.card X = 660 ∨ 1080 < Nat.card X := by
  obtain ⟨hn, h2 | ⟨-, h3⟩, hA, hE⟩ := h
  · exact Or.inr (by have := list2_ge hn h2; omega)
  · exact list3_ge h3 hA hE

theorem lists_three_dvd (h : InLists X n) : 3 ∣ Nat.card X := by
  obtain ⟨hn, h2 | ⟨-, h3⟩, hA, hE⟩ := h
  · exact list2_three_dvd hn h2
  · exact list3_three_dvd h3 hA hE

theorem lists_not_dvd (h : InLists X n) {N : ℕ} (hN : Nat.card X ∣ N) (hN0 : 0 < N)
    (h1080 : N ≤ 1080) (h660 : ¬ 660 ∣ N) : False := by
  have hle := Nat.le_of_dvd hN0 hN
  rcases lists_ge h with h1 | h1
  · exact h660 (h1 ▸ hN)
  · omega


theorem lists_qs [Finite X] (h : InLists X n) :
    CFSG.IsQuasisimple X ∧ Nat.card (Subgroup.center X) ∣ 3 := by
  obtain ⟨hn, h2 | ⟨-, h3⟩, hA, hE⟩ := h
  · obtain ⟨hq, hZ, -⟩ := SecA.factList2Table_holds X n hn h2
    exact ⟨hq, hZ⟩
  · refine ⟨list11_1_1ThreeQuasisimpleFact_holds X h3 hA hE, ?_⟩
    obtain ⟨h1, h2⟩ := SecA.factList3Table_holds
    have hz : Subgroup.center X = ⊥ → Nat.card (Subgroup.center X) ∣ 3 := fun hz => by
      rw [hz, Subgroup.card_bot]
      norm_num
    rcases h3 with h | h | ⟨p, hp, h5, -, h⟩ | h | ⟨s, h | h⟩ | h | h | h | h | h | h | h | h |
      h | h
    · exact (h1 X (Or.inl h)).2.1
    · exact (h1 X (Or.inr (Or.inl h))).2.1
    · exact hz (h2 X (Or.inl ⟨p, hp, eleven_le_of_mod_five hp h5, h⟩)).2.1
    · exact hz (h2 X (Or.inr (Or.inl h))).2.1
    · cases s
      · exact (h1 X (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inl h)).2.1
      · exact hz (h2 X (Or.inr (Or.inr (Or.inl h)))).2.1
    · cases s
      · exact (h1 X (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr h)).2.1
      · exact hz (h2 X (Or.inr (Or.inr (Or.inr (Or.inl h))))).2.1
    · exact (h1 X (Or.inr (Or.inr (Or.inl h)))).2.1
    · exact (h1 X (Or.inr (Or.inr (Or.inr (Or.inl h))))).2.1
    · exact (h1 X (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))).2.1
    · exact hz (h2 X (Or.inr (Or.inr (Or.inr (Or.inr h))))).2.1
    · exact (h1 X (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h)).2.1
    · exact (h1 X (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h)).2.1
    · exact (h1 X (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inl h)).2.1
    · exact (h1 X (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inl h)).2.1
    · exact absurd h hA
    · exact absurd h hE

end CFSG.Quasithin.Vol2.Ch11.SecE.C10KH
