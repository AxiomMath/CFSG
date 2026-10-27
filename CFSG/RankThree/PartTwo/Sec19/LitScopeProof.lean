module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res3ProofCensus194

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock NineThreeConclusion barM InClassXBlock
  NineThreeTwo NineThreeThree NineThreeFour NineThreeFive NineThreeEight Asc81bEightFour
  Asc81bEightFive Asc81bNineThree)

@[expose] def Asc81bNineThreeRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L →
    (∀ p : ℕ, p.Prime → 3 < p → CFSG.Open.pRank p X ≤ 2) → CFSG.Open.pRank 3 X ≤ 3 →
      NineThreeConclusion X S L

@[expose] def Asc81bNineThreeNatRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L →
    (∀ p : ℕ, p.Prime → 3 < p → CFSG.Open.pRank p X ≤ 2) → CFSG.Open.pRank 3 X ≤ 3 →
      InClassXBlock L ∨ NineThreeTwo X S L ∨ (NineThreeThree X S L ∧ IsTypeScriptL L) ∨
        (NineThreeFour X S L ∧ IsA6Z3Type L) ∨ (NineThreeFive X L ∧ IsA7FourType L) ∨
        NineThreeSixNat X S L ∨ NineThreeSevenNat X S L ∨
        (NineThreeEight X S L ∧ IsTypeScriptL L)

theorem asc81bNineThreeNatRank_of_nat (h : Asc81bNineThreeNat) : Asc81bNineThreeNatRank :=
  fun G _ _ X S L hX hhyp hL _ _ => h G X S L hX hhyp hL

theorem asc81bNineThreeRank_of_natRank (hN : Asc81bNineThreeNatRank) : Asc81bNineThreeRank := by
  intro G _ _ X S L hX hhyp hL hp hp3
  rcases hN G X S L hX hhyp hL hp hp3 with h | h | h | h | h | ⟨hirr, n, hn, ⟨φ⟩, -, -, -, hψ⟩ |
      ⟨hirr, n, hn, hφ, hψ⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h.1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h.1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.1))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hirr, n, ?_, hψ⟩)))))
    have hZ : Subgroup.center ↥(barM X L) = ⊥ := by
      have h4 : 4 ≤ Nat.card (Fin (2 * n)) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fin]
        omega
      have hc := Subgroup.map_center_eq φ
      rw [alternatingGroup.center_eq_bot h4] at hc
      exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp hc
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans φ⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hirr, n, hφ, hψ⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h.1))))))

open Item194Proof

namespace Item19Res3Proof

variable {G : Type} [Group G] [Finite G]

theorem concl194Wide_of_natRank (hN : Asc81bNineThreeNatRank) (h85 : Asc81bEightFive)
    (hC : KS194ClassicalCensus) {X S K : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X)
    (hhyp : Asc81bHyp X S) (hK : IsWeakSBlock X S K)
    (hL : ∀ L : Subgroup G, ¬ IsScriptLBlock X L)
    (hp : ∀ p : ℕ, p.Prime → 3 < p → CFSG.Open.pRank p X ≤ 2)
    (hp3 : CFSG.Open.pRank 3 X ≤ 3) : Concl194Wide K (Subgroup.normalizer (S : Set G)) := by
  rcases hN G X S K hX hhyp hK hp hp3 with
      h1 | h2 | ⟨h3, ht⟩ | ⟨h4, ht⟩ | ⟨h5, ht⟩ | h6 | h7 | ⟨h8, ht⟩
  · exact (hL K (Item194Proof.isScriptLBlock_of_inClassXBlock hK.le hK.subnormal h1)).elim
  · exact concl_of_nineThreeTwo h85 hC hX hhyp hK hL hp hp3 h2
  · exact (hL K (isScriptLBlock_of_isShort2 hK.toIsTwoPrimeComponent h3.1 ht)).elim
  · exact (hL K (isScriptLBlock_of_isShort2 hK.toIsTwoPrimeComponent h4.1
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht))))))).elim
  · exact (hL K (isScriptLBlock_of_isShort2 hK.toIsTwoPrimeComponent h5.1
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ht))))))).elim
  · exact concl_of_nineThreeSixNat hK hp3 h6
  · obtain ⟨-, n, hn3, ⟨φ⟩, -⟩ := h7
    exact (false_of_alternating (N := 4 * n) (by omega) φ hp3).elim
  · exact (hL K (isScriptLBlock_of_isShort2 hK.toIsTwoPrimeComponent h8.1 ht)).elim

end Item19Res3Proof

open Item19Res3Proof

theorem census194Wide_of_natRank (hN : Asc81bNineThreeNatRank) (h85 : Asc81bEightFive)
    (hC : KS194ClassicalCensus) : Census194Wide := by
  intro G _ _ X S K hX hhyp hK _ hL hp hp3
  exact concl194Wide_of_natRank hN h85 hC hX hhyp hK hL hp hp3

theorem item194UsedWide3_of_natRank (h84 : Asc81bEightFour) (hN : Asc81bNineThreeNatRank)
    (h85 : Asc81bEightFive) (h316 : Item316) (hC : KS194ClassicalCensus) :
    Item194UsedWide3 := by
  intro G _ _ hG A M H hA hM hH hHM
  have h : Setting194 G A M H := Setting194.mk hG hA hM hH hHM
  refine ⟨h.scriptJ_nonempty h84 h316, fun K hK => ?_⟩
  have hc := concl194Wide_of_natRank hN h85 hC h.isKGroup h.asc81bHyp (h.mem_scriptJ_iff.mp hK)
    (h.not_isScriptLBlock h316) (fun _ hp hp3 => h.pRank_le_two hp hp3) h.pRank_three_le
  rw [h.normalizer_twoCore] at hc
  exact hc

end CFSG.RankThree.PartTwo.Sec19
