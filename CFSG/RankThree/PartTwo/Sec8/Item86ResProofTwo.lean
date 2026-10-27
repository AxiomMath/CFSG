module

public import CFSG.RankThree.PartTwo.Sec8.Item83ProofDefs
public import CFSG.RankThree.PartTwo.Sec6.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Item83Proof


@[expose] def Item82TwoList : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G),
    Hyp81 G A c L a → Nat.card A = 81 → IsList82Two (L ⧸ aschbacherSolvableCore 3 L)

theorem card_eq_eightyOne_of_hyp81 (h611 : Sec6.Item6_11_1) {G : Type} [Group G] [Finite G]
    {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} (h : Hyp81 G A c L a)
    (hA : 27 < Nat.card A) : Nat.card A = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hAp
  have hk4 : k ≤ CFSG.Open.pRank 3 A :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three A)
      ⟨A, le_rfl, hAe, hk⟩
  have hrank := h611 G h.toPartTwoStanding A h.mem_partTwoF
  have hk' : k = 4 := by
    have hle : k ≤ 4 := hk4.trans hrank
    have hgt : 3 < k := by
      by_contra hcon
      have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega
  rw [hk, hk']
  norm_num

theorem item82Two_of (h611 : Sec6.Item6_11_1) (hL : Item82TwoList) : Item82Two := by
  intro G _ _ A c L a h hA
  have h81 := card_eq_eightyOne_of_hyp81 h611 h hA
  exact ⟨h81, hL G A c L a h h81⟩

end CFSG.RankThree.PartTwo.Sec8.Item86ResProof
