module

public import CFSG.RankThree.PartOne.Census3.Interface

public section

namespace CFSG.RankThree.PartOne.Census3

open TauCeti

structure SpinRankFour : Prop where
  typeB : ∀ (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid), 3 ≤ r →
    ¬ (r = 3 ∧ q.p = 2) → ¬ (r = 4 ∧ q.p = 2 ∧ q.exponent = 1) →
    ∀ [Finite (CFSGIndex.lie ⟨.B r q, hv⟩).Group],
      4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.B r q, hv⟩).Group
  typeD : ∀ (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D r q).Valid),
    ¬ (r = 4 ∧ q.p = 2 ∧ q.exponent = 1) →
    ∀ [Finite (CFSGIndex.lie ⟨.D r q, hv⟩).Group],
      4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.D r q, hv⟩).Group
  typeTwistedD : ∀ (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.twistedD r q).Valid),
    ¬ (r = 4 ∧ q.p = 2) →
    ∀ [Finite (CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group],
      4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group

structure ExceptionalRankFour : Prop where
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

@[expose] def RankFourBabyMonster : Prop :=
  ExcludedIndex (.sporadic .B)

end CFSG.RankThree.PartOne.Census3
