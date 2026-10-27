module

public import CFSG.RankThree.PartTwo.Sec8.Steps

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item83Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Choice86Var : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G) (n : ℕ),
    Sec8Std G A c L a d n → ∃ (c' : G) (L' : Subgroup G) (a' b : G) (X : Subgroup G),
      ((c' = c ∧ L' = L) ∨ PairRel A c L c' L') ∧ (∃ k : ℤ, a' = a * c' ^ k) ∧
        Sec8Pair G A c' L' a' b X n

theorem item812_of_choice86Var (h83 : Item83) (h83a : Item83After) (h86 : Choice86Var)
    (hnever : Sec8Never) : Item812 := by
  intro G _ _ A c L a h
  obtain ⟨E, hE, hEA⟩ := h.mem_partTwoF.2.2
  have hle : 27 ≤ Nat.card A := hE.2.1 ▸ Subgroup.card_le_of_le hEA
  rcases hle.lt_or_eq with hbig | h27
  · exfalso
    obtain ⟨A₀, d, n, hd⟩ := h83 G A c L a h hbig
    obtain ⟨-, -, a', -, h81', hd', hg2⟩ := h83a G A c L a h hbig A₀ d n hd
    obtain ⟨c', L', a'', b, X, -, -, hpair⟩ :=
      h86 G A₀ c L a' d n { h81' with data83 := hd', gTwo := hg2 }
    exact hnever G A₀ c' L' a'' b X n hpair
  · exact h27.symm

end CFSG.RankThree.PartTwo.Sec8.Item83Proof
