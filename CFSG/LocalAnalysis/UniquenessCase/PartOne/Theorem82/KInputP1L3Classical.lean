module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1L3Order
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1L3Small
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1L3TwoAdic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

@[expose] def LieOrderBridgeHyp : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G],
    Nonempty (G ≃* (TauCeti.CFSGIndex.lie d).Group) → Nat.card G = lieOrderFormula d.1

@[expose] def LieCharPartHyp : Prop :=
  ∀ d : TauCeti.LieTypeIndex, d.Valid → ∃ v M : ℕ,
    lieOrderFormula d = d.characteristic ^ v * M ∧ M < d.characteristic ^ (2 * v)

theorem characteristic_eq_two_of_classicalOrG2 {d : TauCeti.LieTypeIndex}
    (h : CFSG.AGLEmbedding.IsClassicalOrG2Index d) : d.characteristic = 2 := by
  cases d <;> first | exact h.elim | simpa [CFSG.AGLEmbedding.IsClassicalOrG2Index] using h

theorem not_isClassicalTwoOrG2_of_order (hB : LieOrderBridgeHyp) (hC : LieCharPartHyp)
    {Y : Type} [Group Y] [Finite Y] {q c : ℕ} (hq : q % 2 = 1) (h5 : 5 ≤ q)
    (hc : c = q ^ 3 - 1 ∨ c = q ^ 3 + 1) (hY : Nat.card Y = q ^ 3 * ((q ^ 2 - 1) * c)) :
    ¬ CFSG.AGLEmbedding.IsClassicalTwoOrG2 Y := by
  have hge := order_ge_of_five_le h5 hc
  rintro (⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩)
  · have hord : Nat.card Y = lieOrderFormula d.1 := hB d Y ⟨e⟩
    obtain ⟨v, M, hv, hM⟩ := hC d.1 d.2
    rw [characteristic_eq_two_of_classicalOrG2 hd] at hv hM
    have hdvd : 2 ^ v ∣ q ^ 3 * ((q ^ 2 - 1) * c) := ⟨M, by rw [← hY, hord, hv]⟩
    have hle := two_pow_three_mul_le hq h5 hc hdvd
    rw [← hY, hord, hv] at hle
    have hlt : 2 ^ v * M < 2 ^ (3 * v) :=
      calc 2 ^ v * M < 2 ^ v * 2 ^ (2 * v) := Nat.mul_lt_mul_of_pos_left hM (by positivity)
        _ = 2 ^ (3 * v) := by rw [← pow_add]; congr 1; omega
    omega
  · have hcard := card_alt_fin_small hn
    rw [← Nat.card_congr e.toEquiv, hY] at hcard
    omega
  · have hle := lieOrderFormula_small_le (d := d) hd
    rw [hB d Y ⟨e⟩] at hY
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
