module

public import CFSG.RankThree.PartTwo.Census.Alternating
public import CFSG.RankThree.PartTwo.Census.Models

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven TauCeti

@[expose] def BridgeSp8Two : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.B 4 q).Valid), q.p = 2 → q.exponent = 1 →
    Nonempty (ValidLieTypeIndex.Group ⟨.B 4 q, hv⟩ ≃* projSp 4 (GaloisField 2 1))

@[expose] def BridgeSp6Four : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.B 3 q).Valid), q.p = 2 → q.exponent = 2 →
    Nonempty (ValidLieTypeIndex.Group ⟨.B 3 q, hv⟩ ≃* projSp 3 (GaloisField 2 2))

@[expose] def BridgeOmega8PlusTwo : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.D 4 q).Valid), q.p = 2 → q.exponent = 1 →
    Nonempty (ValidLieTypeIndex.Group ⟨.D 4 q, hv⟩ ≃* projOmegaPlus 4 (GaloisField 2 1))

@[expose] def BridgeOmega8MinusTwo : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.twistedD 4 q).Valid), q.p = 2 → q.exponent = 1 →
    ∃ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) ∧
      Nonempty (ValidLieTypeIndex.Group ⟨.twistedD 4 q, hv⟩ ≃*
        projOmegaMinus 3 (GaloisField 2 1) b c)

structure SpinCarrierExclusions : Prop where
  typeB : ∀ (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid), 3 ≤ r →
    ¬ (r = 4 ∧ q.p = 2 ∧ q.exponent = 1) → ¬ (r = 3 ∧ q.p = 2 ∧ q.exponent = 2) →
    Excluded433 (.lie ⟨.B r q, hv⟩)
  typeD : ∀ (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D r q).Valid),
    ¬ (r = 4 ∧ q.p = 2 ∧ q.exponent = 1) → Excluded433 (.lie ⟨.D r q, hv⟩)
  typeTwistedD : ∀ (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.twistedD r q).Valid),
    ¬ (r = 4 ∧ q.p = 2 ∧ q.exponent = 1) → Excluded433 (.lie ⟨.twistedD r q, hv⟩)

structure ExceptionalCarrierExclusions : Prop where
  e6 : ∀ (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid), Excluded433 (.lie ⟨.E6 q, hv⟩)
  e7 : ∀ (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid), Excluded433 (.lie ⟨.E7 q, hv⟩)
  e8 : ∀ (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid), Excluded433 (.lie ⟨.E8 q, hv⟩)
  f4 : ∀ (q : PrimePower) (hv : (LieTypeIndex.F4 q).Valid), ¬ (q.p = 2 ∧ q.exponent = 1) →
    Excluded433 (.lie ⟨.F4 q, hv⟩)
  g2 : ∀ (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid), Excluded433 (.lie ⟨.G2 q, hv⟩)
  twistedE6 : ∀ (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid),
    Excluded433 (.lie ⟨.twistedE6 q, hv⟩)
  trialityD4 : ∀ (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid),
    Excluded433 (.lie ⟨.trialityD4 q, hv⟩)
  reeG2 : ∀ (m : ℕ) (hv : (LieTypeIndex.reeG2 m).Valid), Excluded433 (.lie ⟨.reeG2 m, hv⟩)
  reeF4 : ∀ (m : ℕ) (hv : (LieTypeIndex.reeF4 m).Valid), Excluded433 (.lie ⟨.reeF4 m, hv⟩)
  tits : ∀ hv : LieTypeIndex.tits.Valid, Excluded433 (.lie ⟨.tits, hv⟩)

theorem item433Case_B_of_open (hSp8 : BridgeSp8Two) (hSp64 : BridgeSp6Four)
    (hspin : SpinCarrierExclusions) (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid)
    (hr : 3 ≤ r) : Item433Case (.lie ⟨.B r q, hv⟩) := by
  by_cases h8 : r = 4 ∧ q.p = 2 ∧ q.exponent = 1
  · obtain ⟨rfl, hp, he⟩ := h8
    obtain ⟨b⟩ := hSp8 q hv hp he
    exact fun _ _ _ _ e => iiModel_of_projSp_four_two (e.trans b)
  by_cases h6 : r = 3 ∧ q.p = 2 ∧ q.exponent = 2
  · obtain ⟨rfl, hp, he⟩ := h6
    obtain ⟨b⟩ := hSp64 q hv hp he
    exact fun _ _ _ _ e => iiModel_of_projSp_three_four (e.trans b)
  exact (hspin.typeB r q hv hr h8 h6).item433Case

theorem item433Case_D_of_open (hOp : BridgeOmega8PlusTwo) (hspin : SpinCarrierExclusions)
    (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D r q).Valid) :
    Item433Case (.lie ⟨.D r q, hv⟩) := by
  by_cases h8 : r = 4 ∧ q.p = 2 ∧ q.exponent = 1
  · obtain ⟨rfl, hp, he⟩ := h8
    obtain ⟨b⟩ := hOp q hv hp he
    exact fun _ _ _ _ e => iiModel_of_projOmegaPlus_four_two (e.trans b)
  exact (hspin.typeD r q hv h8).item433Case

theorem item433Case_twistedD_of_open (hOm : BridgeOmega8MinusTwo)
    (hspin : SpinCarrierExclusions) (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedD r q).Valid) : Item433Case (.lie ⟨.twistedD r q, hv⟩) := by
  by_cases h8 : r = 4 ∧ q.p = 2 ∧ q.exponent = 1
  · obtain ⟨rfl, hp, he⟩ := h8
    obtain ⟨b, c, hbc, ⟨f⟩⟩ := hOm q hv hp he
    exact fun _ _ _ _ e => iiModel_of_projOmegaMinus_three_two hbc (e.trans f)
  exact (hspin.typeTwistedD r q hv h8).item433Case

theorem item433Case_F4_of_open (hexc : ExceptionalCarrierExclusions) (q : PrimePower)
    (hv : (LieTypeIndex.F4 q).Valid) : Item433Case (.lie ⟨.F4 q, hv⟩) := by
  by_cases h2 : q.p = 2 ∧ q.exponent = 1
  · exact item433Case_F4_two q hv h2.1 h2.2
  · exact (hexc.f4 q hv h2).item433Case

theorem item433_of_families
    (hspor : ∀ s : SporadicName, Item433Case (.sporadic s))
    (hA : ∀ (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.A r q).Valid),
      Item433Case (.lie ⟨.A r q, hv⟩))
    (h2A : ∀ (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.twistedA r q).Valid),
      Item433Case (.lie ⟨.twistedA r q, hv⟩))
    (hB2 : ∀ (q : PrimePower) (hv : (LieTypeIndex.B 2 q).Valid),
      Item433Case (.lie ⟨.B 2 q, hv⟩))
    (hC : ∀ (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.C r q).Valid),
      Item433Case (.lie ⟨.C r q, hv⟩))
    (hSz : ∀ (m : ℕ) (hv : (LieTypeIndex.suzuki m).Valid),
      Item433Case (.lie ⟨.suzuki m, hv⟩))
    (hSp8 : BridgeSp8Two) (hSp64 : BridgeSp6Four) (hOp : BridgeOmega8PlusTwo)
    (hOm : BridgeOmega8MinusTwo) (hspin : SpinCarrierExclusions)
    (hexc : ExceptionalCarrierExclusions) : Item433 := by
  have hlie : ∀ d, Item433Case (.lie d) := by
    refine item433Case_lie_of_families hA h2A ?_ hC (item433Case_D_of_open hOp hspin)
      (item433Case_twistedD_of_open hOm hspin) (fun q hv => (hexc.e6 q hv).item433Case)
      (fun q hv => (hexc.e7 q hv).item433Case) (fun q hv => (hexc.e8 q hv).item433Case)
      (item433Case_F4_of_open hexc) (fun q hv => (hexc.g2 q hv).item433Case)
      (fun q hv => (hexc.twistedE6 q hv).item433Case)
      (fun q hv => (hexc.trialityD4 q hv).item433Case) hSz
      (fun m hv => (hexc.reeG2 m hv).item433Case) (fun m hv => (hexc.reeF4 m hv).item433Case)
      (fun hv => (hexc.tits hv).item433Case)
    intro r q hv
    have h2 : 2 ≤ r :=
      ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).1
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr
    · exact hB2 q hv
    · exact item433Case_B_of_open hSp8 hSp64 hspin r q hv hr
  refine item433_of_cases fun i => ?_
  cases i with
  | cyclic p hp => exact (excluded433_cyclic p hp).item433Case
  | alternating n hn => exact (excluded433_alternating n hn).item433Case
  | lie d => exact hlie d
  | sporadic s => exact hspor s

end CFSG.RankThree.PartTwo.Census
