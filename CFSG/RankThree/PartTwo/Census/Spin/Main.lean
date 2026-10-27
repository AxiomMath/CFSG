module

public import CFSG.RankThree.PartTwo.Census.Assembly
public import CFSG.RankThree.PartTwo.Census.Spin.ExcludeOdd
public import CFSG.RankThree.PartTwo.Census.Spin.ExcludeTwo

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

open CFSG.Assembly CFSG.Assembly.RankThreeEven TauCeti

theorem spinWitness_typeB (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.B r q).Valid) (hr : 3 ≤ r) (h42 : ¬ (r = 4 ∧ q.p = 2 ∧ q.exponent = 1))
    (h34 : ¬ (r = 3 ∧ q.p = 2 ∧ q.exponent = 2)) (h32 : ¬ (r = 3 ∧ q.p = 2 ∧ q.exponent = 1)) :
    Excluded433 (.lie ⟨.B r q, hv⟩) := by
  have hf1 := q.exponent_pos
  by_cases hp : q.p = 2
  · by_cases hf : 2 ≤ q.exponent
    · exact excluded433_B_even r q hv hr hp hf fun h => h34 ⟨h.1, hp, h.2⟩
    · have hf' : q.exponent = 1 := by omega
      rcases (show r = 3 ∨ r = 4 ∨ 5 ≤ r by omega) with rfl | rfl | h5
      · exact absurd ⟨rfl, hp, hf'⟩ h32
      · exact absurd ⟨rfl, hp, hf'⟩ h42
      · exact excluded433_B_two r q hv hp h5
  · exact excluded433_B_odd r q hv hr hp

theorem spinWitness_typeD (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.D r q).Valid) (h42 : ¬ (r = 4 ∧ q.p = 2 ∧ q.exponent = 1)) :
    Excluded433 (.lie ⟨.D r q, hv⟩) := by
  have hf1 := q.exponent_pos
  by_cases hp : q.p = 2
  · by_cases hf : 2 ≤ q.exponent
    · exact excluded433_D_even r q hv hp hf
    · have hf' : q.exponent = 1 := by omega
      have h4 : 4 ≤ r := TypeDDiagramLieIndex.four_le_rank
        (TypeDLieIndex.toTypeDDiagramLieIndex ⟨⟨.D r q, hv⟩, by simp⟩)
      rcases (show r = 4 ∨ 5 ≤ r by omega) with rfl | h5
      · exact absurd ⟨rfl, hp, hf'⟩ h42
      · exact excluded433_D_two r q hv hp h5
  · exact excluded433_D_odd r q hv hp

theorem spinWitness_typeTwistedD (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedD r q).Valid) (h42 : ¬ (r = 4 ∧ q.p = 2 ∧ q.exponent = 1)) :
    Excluded433 (.lie ⟨.twistedD r q, hv⟩) := by
  have hf1 := q.exponent_pos
  have h4 : 4 ≤ r := CarrierTD.four_le ⟨⟨.twistedD r q, hv⟩, by simp⟩
  by_cases hp : q.p = 2
  · by_cases hf : 2 ≤ q.exponent
    · by_cases h44 : r = 4 ∧ q.exponent = 2
      · obtain ⟨rfl, he⟩ := h44
        exact excluded433_twistedD_four_four q hv hp he
      · exact excluded433_twistedD_even r q hv hp hf h44
    · have hf' : q.exponent = 1 := by omega
      rcases (show r = 4 ∨ 5 ≤ r by omega) with rfl | h5
      · exact absurd ⟨rfl, hp, hf'⟩ h42
      · rcases (show r = 5 ∨ 6 ≤ r by omega) with rfl | h6
        · exact excluded433_twistedD_five_two q hv hp hf'
        · exact excluded433_twistedD_two r q hv hp h6
  · exact excluded433_twistedD_odd r q hv hp

theorem spinCarrierExclusions_of_B32
    (hB32 : ∀ (q : PrimePower) (hv : (LieTypeIndex.B 3 q).Valid), q.p = 2 → q.exponent = 1 →
      Excluded433 (.lie ⟨.B 3 q, hv⟩)) : SpinCarrierExclusions where
  typeB r q hv hr h42 h34 := by
    by_cases h32 : r = 3 ∧ q.p = 2 ∧ q.exponent = 1
    · obtain ⟨rfl, hp, he⟩ := h32
      exact hB32 q hv hp he
    · exact spinWitness_typeB r q hv hr h42 h34 h32
  typeD := spinWitness_typeD
  typeTwistedD := spinWitness_typeTwistedD

theorem item433Case_B_of_bridges (hSp8 : BridgeSp8Two) (hSp64 : BridgeSp6Four)
    (hB32 : ∀ (q : PrimePower) (hv : (LieTypeIndex.B 3 q).Valid), q.p = 2 → q.exponent = 1 →
      Excluded433 (.lie ⟨.B 3 q, hv⟩))
    (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid) (hr : 3 ≤ r) :
    Item433Case (.lie ⟨.B r q, hv⟩) :=
  item433Case_B_of_open hSp8 hSp64 (spinCarrierExclusions_of_B32 hB32) r q hv hr

theorem item433Case_D_of_bridge (hOp : BridgeOmega8PlusTwo) (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.D r q).Valid) : Item433Case (.lie ⟨.D r q, hv⟩) := by
  by_cases h8 : r = 4 ∧ q.p = 2 ∧ q.exponent = 1
  · obtain ⟨rfl, hp, he⟩ := h8
    obtain ⟨b⟩ := hOp q hv hp he
    exact fun _ _ _ _ e => iiModel_of_projOmegaPlus_four_two (e.trans b)
  exact (spinWitness_typeD r q hv h8).item433Case

theorem item433Case_twistedD_of_bridge (hOm : BridgeOmega8MinusTwo) (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedD r q).Valid) :
    Item433Case (.lie ⟨.twistedD r q, hv⟩) := by
  by_cases h8 : r = 4 ∧ q.p = 2 ∧ q.exponent = 1
  · obtain ⟨rfl, hp, he⟩ := h8
    obtain ⟨b, c, hbc, ⟨f⟩⟩ := hOm q hv hp he
    exact fun _ _ _ _ e => iiModel_of_projOmegaMinus_three_two hbc (e.trans f)
  exact (spinWitness_typeTwistedD r q hv h8).item433Case

end CFSG.RankThree.PartTwo.Census.Spin
