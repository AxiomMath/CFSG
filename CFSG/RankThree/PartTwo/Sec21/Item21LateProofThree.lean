module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res3ProofThree
public import CFSG.RankThree.PartTwo.Sec21.Item21LateProofIdent

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU)

@[expose] def Item2130ThreeYU4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Config2130 G A E U c L → 27 ≤ Nat.card (A ⊓ L : Subgroup G) →
    (∃ n : ℕ, 1 < n ∧ Odd n ∧ Nonempty (lBar L ≃* projSU 4 2 n)) → Nat.card A = 3 ^ 4 →
    Nonempty (starOf A L ≃* Equiv.Perm (Fin 4)) →
      ∃ b ∈ A ⊓ L, b ≠ 1 ∧ ∃ Y ∈ thetaComponentsAt 3 b, Y ∈ lZeroUnion A ∧
        ∃ I : Subgroup G, I ≤ L ∧ Y = I ⊔ inSubgroup (aschbacherSolvableCore 3) Y

theorem item2130ThreeY_of (h211 : Item211) (h213 : Item213)
    (h217 : Item217) (h2116 : Item2116) (hU : Item2130ThreeYU4) : Item2130ThreeY := by
  intro G _ _ A E U c L hcfg h27
  have hA : 27 < Nat.card A := by rw [hcfg.card_eq]; omega
  obtain ⟨hL, h81, hS4⟩ := Item21LateProof.case10_of_lt_card h211 h213 h217 h2116 hcfg.pair hA
  exact hU G A E U c L hcfg h27 hL h81 hS4

end CFSG.RankThree.PartTwo.Sec21
