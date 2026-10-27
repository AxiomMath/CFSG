module

public import CFSG.RankThree.PartTwo.Census.Main
import CFSG.RankThree.PartTwo.Census.Classical.EvenMain
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.RankThree.PartOne.S10.PlaneAuxiliary

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven TauCeti

structure SpinWitnessCases433 : Prop where
  typeB : ∀ (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid), 3 ≤ r →
    ¬ (r = 4 ∧ q.p = 2 ∧ q.exponent = 1) → ¬ (r = 3 ∧ q.p = 2 ∧ q.exponent = 2) →
    ¬ (r = 3 ∧ q.p = 2 ∧ q.exponent = 1) → Excluded433 (.lie ⟨.B r q, hv⟩)
  typeD : ∀ (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D r q).Valid),
    ¬ (r = 4 ∧ q.p = 2 ∧ q.exponent = 1) → Excluded433 (.lie ⟨.D r q, hv⟩)
  typeTwistedD : ∀ (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.twistedD r q).Valid),
    ¬ (r = 4 ∧ q.p = 2 ∧ q.exponent = 1) → Excluded433 (.lie ⟨.twistedD r q, hv⟩)

structure ExceptionalWitnessCases433 : Prop where
  e6 : ∀ (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid)
    [Finite (CFSGIndex.lie ⟨.E6 q, hv⟩).Group],
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.E6 q, hv⟩).Group
  e7 : ∀ (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid)
    [Finite (CFSGIndex.lie ⟨.E7 q, hv⟩).Group],
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.E7 q, hv⟩).Group
  e8 : ∀ (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid)
    [Finite (CFSGIndex.lie ⟨.E8 q, hv⟩).Group],
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.E8 q, hv⟩).Group
  twistedE6 : ∀ (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid)
    [Finite (CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group],
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group
  f4 : ∀ (q : PrimePower) (hv : (LieTypeIndex.F4 q).Valid), ¬ (q.p = 2 ∧ q.exponent = 1) →
    ∀ [Finite (CFSGIndex.lie ⟨.F4 q, hv⟩).Group],
      4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.F4 q, hv⟩).Group
  g2 : ∀ (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid), q.p ≠ 2 → 2 ≤ q.exponent →
    ∀ [Finite (CFSGIndex.lie ⟨.G2 q, hv⟩).Group],
      4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.G2 q, hv⟩).Group
  trialityD4 : ∀ (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid), q.p ≠ 2 →
    ∀ [Finite (CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group],
      4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group
  reeG2 : ∀ (m : ℕ) (hv : (LieTypeIndex.reeG2 m).Valid), 2 ≤ m →
    ∀ [Finite (CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group],
      4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group

structure CarrierCases433 : Prop where
  sp8Two : BridgeSp8Two
  sp6Four : BridgeSp6Four
  omega8PlusTwo : BridgeOmega8PlusTwo
  omega8MinusTwo : BridgeOmega8MinusTwo
  b3Two : ∀ (q : PrimePower) (hv : (LieTypeIndex.B 3 q).Valid), q.p = 2 → q.exponent = 1 →
    Excluded433 (.lie ⟨.B 3 q, hv⟩)
  g2Even : ∀ (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid), q.p = 2 →
    Excluded433 (.lie ⟨.G2 q, hv⟩)
  g2Three : ∀ (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid), q.p = 3 → q.exponent = 1 →
    Excluded433 (.lie ⟨.G2 q, hv⟩)
  g2Prime : ∀ (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid), q.p ≠ 2 → q.p ≠ 3 →
    q.exponent = 1 → Excluded433 (.lie ⟨.G2 q, hv⟩)
  trialityD4Even : ∀ (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid), q.p = 2 →
    Excluded433 (.lie ⟨.trialityD4 q, hv⟩)
  reeG2One : ∀ hv : (LieTypeIndex.reeG2 1).Valid, Excluded433 (.lie ⟨.reeG2 1, hv⟩)
  reeF4 : ∀ (m : ℕ) (hv : (LieTypeIndex.reeF4 m).Valid), Excluded433 (.lie ⟨.reeF4 m, hv⟩)
  tits : ∀ hv : LieTypeIndex.tits.Valid, Excluded433 (.lie ⟨.tits, hv⟩)

theorem excluded433_of_four_le_twoLocalOddRank {i : CFSGIndex}
    (h : ∀ [Finite i.Group], 4 ≤ CFSG.twoLocalOddRank i.Group) : Excluded433 i := by
  intro G _ _ hG e
  have : Finite i.Group := Finite.of_equiv G e.toEquiv
  have h4 : 4 ≤ evenRank i.Group := by
    rw [CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]
    exact h
  have hle := CFSG.RankThree.PartOne.PlaneAux.evenRank_le_of_injective e.symm.toMonoidHom
    e.symm.injective
  rw [hG.evenRank_eq] at hle
  omega

theorem spinCarrierExclusions_of (hw : SpinWitnessCases433) (hc : CarrierCases433) :
    SpinCarrierExclusions where
  typeB r q hv hr h8 h6 := by
    by_cases h2 : r = 3 ∧ q.p = 2 ∧ q.exponent = 1
    · obtain ⟨rfl, hp, he⟩ := h2
      exact hc.b3Two q hv hp he
    · exact hw.typeB r q hv hr h8 h6 h2
  typeD := hw.typeD
  typeTwistedD := hw.typeTwistedD

theorem exceptionalCarrierExclusions_of (hw : ExceptionalWitnessCases433)
    (hc : CarrierCases433) : ExceptionalCarrierExclusions where
  e6 q hv := excluded433_of_four_le_twoLocalOddRank (hw.e6 q hv)
  e7 q hv := excluded433_of_four_le_twoLocalOddRank (hw.e7 q hv)
  e8 q hv := excluded433_of_four_le_twoLocalOddRank (hw.e8 q hv)
  f4 q hv h2 := excluded433_of_four_le_twoLocalOddRank (hw.f4 q hv h2)
  g2 q hv := by
    by_cases hp2 : q.p = 2
    · exact hc.g2Even q hv hp2
    by_cases he : q.exponent = 1
    · by_cases hp3 : q.p = 3
      · exact hc.g2Three q hv hp3 he
      · exact hc.g2Prime q hv hp2 hp3 he
    · exact excluded433_of_four_le_twoLocalOddRank
        (hw.g2 q hv hp2 (by have := q.exponent_pos; omega))
  twistedE6 q hv := excluded433_of_four_le_twoLocalOddRank (hw.twistedE6 q hv)
  trialityD4 q hv := by
    by_cases hp2 : q.p = 2
    · exact hc.trialityD4Even q hv hp2
    · exact excluded433_of_four_le_twoLocalOddRank (hw.trialityD4 q hv hp2)
  reeG2 m hv := by
    have hm : 1 ≤ m :=
      (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
    by_cases h1 : m = 1
    · subst h1
      exact hc.reeG2One hv
    · exact excluded433_of_four_le_twoLocalOddRank (hw.reeG2 m hv (by omega))
  reeF4 := hc.reeF4
  tits := hc.tits

theorem item433_of_carrierCases (hspor : ∀ s : SporadicName, Item433Case (.sporadic s))
    (hspin : SpinWitnessCases433) (hexc : ExceptionalWitnessCases433)
    (hcar : CarrierCases433) : Item433 :=
  item433_of_evenCases hspor item433Case_A_even item433Case_twistedA_even item433Case_B2_even
    hcar.sp8Two hcar.sp6Four hcar.omega8PlusTwo hcar.omega8MinusTwo
    (spinCarrierExclusions_of hspin hcar) (exceptionalCarrierExclusions_of hexc hcar)

end CFSG.RankThree.PartTwo.Census
