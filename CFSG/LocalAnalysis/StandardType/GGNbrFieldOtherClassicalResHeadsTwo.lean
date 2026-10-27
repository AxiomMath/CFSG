module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResCover
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResHeads
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResL3Three
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResL3ThreeFour
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU3Three

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGFieldOtherU3ThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ lab.rank = 2 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1 ∧ 3 ∣ lab.n ∧ lab.n ≠ 3

section UnitaryThree


theorem ggFieldKLevel_u3Three (hpc : GGRawPCyclicOn GGNotD4Three)
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldOtherU3ThreeLabel p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) :=
  ggFieldKLevel_of_fixKX (Kp := fun _ k => k ∣ 3) (S := GGFieldOtherU3ThreeLabel)
    (fun _ _ _ hab hb => hab.trans hb) (fun _ _ ⟨ht, _⟩ => ggFieldOther_twA_not ht)
    (fun p _ _ _ hlab ⟨ht, hl, hp, hq, hd, h3⟩ => by
      subst hp
      exact largeEvenLabelAll_rowKX_u3Three hlab ⟨ht, hl, hq, hd, h3⟩)
    (fun p _ _ _ hlab ⟨ht, hl, hp, hq, hd, h3⟩ => by
      subst hp
      exact largeEvenLabelAll_fixKX_u3Three hlab ⟨ht, hl, hq, hd, h3⟩)
    hpc hconj hcen hinn

theorem ggNbrInnerWeylOn_of_u3Three (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hG : GGNbrGraphInput) (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) {T : ℕ → LargeEvenLabel → Prop}
    (hT : GGNbrInnerWeylOn fun p lab => T p lab ∧ ¬ GGFieldOtherU3ThreeLabel p lab) :
    GGNbrInnerWeylOn T :=
  ggNbrInnerWeylOn_of_fieldFixKLevel hL hPJ hG (ggFieldKLevel_u3Three hpc hconj hcen hinn) hT

end UnitaryThree

@[expose] def GGFieldOtherL3ThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∧ lab.rank = 2 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n - 1 ∧ 3 ∣ lab.n ∧ lab.n ≠ 6

@[expose] def GGFieldOtherL3SixtyFourLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∧ lab.rank = 2 ∧ p = 3 ∧ lab.n = 6

theorem ggFieldOther_A_not {p : ℕ} {lab : LargeEvenLabel} (ht : lab.tag = .A) :
    GGNotD4Three p lab ∧ ¬ (lab.tag = .triD4 ∧ p = 3) := by
  refine ⟨?_, ?_⟩ <;> rintro ⟨h', -⟩ <;> rw [ht] at h' <;> cases h'

theorem ggFieldKLevel_l3Three (hpc : GGRawPCyclicOn GGNotD4Three)
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldOtherL3ThreeLabel p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) :=
  ggFieldKLevel_of_fixKX (Kp := fun _ k => k ∣ 3) (S := GGFieldOtherL3ThreeLabel)
    (fun _ _ _ hab hb => hab.trans hb) (fun _ _ ⟨ht, _⟩ => ggFieldOther_A_not ht)
    (fun p _ _ _ hlab ⟨ht, hl, hp, hq, hd, h6⟩ => by
      subst hp
      exact largeEvenLabelAll_rowKX_l3Three hlab ⟨ht, hl, hq, hd, h6⟩)
    (fun p _ _ _ hlab ⟨ht, hl, hp, hq, hd, h6⟩ => by
      subst hp
      exact largeEvenLabelAll_fixKX_l3Three hlab ⟨ht, hl, hq, hd, h6⟩)
    hpc hconj hcen hinn

theorem ggNbrInnerWeylOn_of_l3Three (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hG : GGNbrGraphInput) (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) {T : ℕ → LargeEvenLabel → Prop}
    (hT : GGNbrInnerWeylOn fun p lab => T p lab ∧ ¬ GGFieldOtherL3ThreeLabel p lab) :
    GGNbrInnerWeylOn T :=
  ggNbrInnerWeylOn_of_fieldFixKLevel hL hPJ hG (ggFieldKLevel_l3Three hpc hconj hcen hinn) hT

section SixtyFour

theorem ggFieldKLevel_l3SixtyFour (hpc : GGRawPCyclicOn GGNotD4Three)
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldOtherL3SixtyFourLabel p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) :=
  ggFieldKLevel_of_fixKX (Kp := fun _ k => k ∣ 3) (S := GGFieldOtherL3SixtyFourLabel)
    (fun _ _ _ hab hb => hab.trans hb) (fun _ _ ⟨ht, _⟩ => ggFieldOther_A_not ht)
    (fun p _ _ _ hlab ⟨ht, hl, hp, h6⟩ => by
      subst hp
      exact largeEvenLabelAll_rowKX_l3ThreeFour hlab ⟨ht, hl, h6⟩)
    (fun p _ _ _ hlab ⟨ht, hl, hp, h6⟩ => by
      subst hp
      exact largeEvenLabelAll_fixKX_l3ThreeFour hlab ⟨ht, hl, h6⟩)
    hpc hconj hcen hinn

theorem ggNbrInnerWeylOn_of_l3SixtyFour (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hG : GGNbrGraphInput) (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) {T : ℕ → LargeEvenLabel → Prop}
    (hT : GGNbrInnerWeylOn fun p lab => T p lab ∧ ¬ GGFieldOtherL3SixtyFourLabel p lab) :
    GGNbrInnerWeylOn T :=
  ggNbrInnerWeylOn_of_fieldFixKLevel hL hPJ hG (ggFieldKLevel_l3SixtyFour hpc hconj hcen hinn) hT

end SixtyFour

@[expose] def GGFieldClassicalResidualU3EightLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ lab.rank = 2 ∧ p = 3 ∧ lab.n = 3

section Head


theorem ggNbrInnerWeylOn_c9_of_nonClassicalU3Eight (hL : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hG : GGNbrGraphInput) (hpc : GGRawPCyclicOn GGNotD4Three)
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput)
    (h : GGNbrInnerWeylOn fun p lab => GGNbrWeylFieldOtherOpenLabel p lab ∧
      ¬ GGFieldFixLabel p lab ∧ ¬ GGFieldFixNsLabel p lab ∧ ¬ GGFieldFixD4Label p lab ∧
      ¬ (p = 3 ∧ lab.tag = .G2 ∧ 6 ∣ lab.n) ∧
      (¬ GGFieldClassicalTag lab ∨ GGFieldClassicalResidualU3EightLabel p lab)) :
    GGNbrInnerWeylOn fun p lab => GGNbrWeylFieldOtherOpenLabel p lab ∧
      ¬ GGFieldFixLabel p lab ∧ ¬ GGFieldFixNsLabel p lab ∧ ¬ GGFieldFixD4Label p lab ∧
      ¬ (p = 3 ∧ lab.tag = .G2 ∧ 6 ∣ lab.n) := by
  refine ggNbrInnerWeylOn_c9_of_nonClassicalExc hL hPJ hG hpc hconj hcen hinn ?_
  refine ggNbrInnerWeylOn_of_sp4Eight hL hPJ hG hpc hconj hcen hinn ?_
  refine ggNbrInnerWeylOn_of_u5Five hL hPJ hG hpc hconj hcen hinn ?_
  refine ggNbrInnerWeylOn_of_u3Three hL hPJ hG hpc hconj hcen hinn ?_
  refine ggNbrInnerWeylOn_of_l3Three hL hPJ hG hpc hconj hcen hinn ?_
  refine ggNbrInnerWeylOn_of_l3SixtyFour hL hPJ hG hpc hconj hcen hinn ?_
  refine h.mono_of_lambda fun p lab _ hp2 _ hr => ?_
  obtain ⟨⟨⟨⟨⟨⟨hO, hFF, hFN, hFD, hG2, hres⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := hr
  refine ⟨hO, hFF, hFN, hFD, hG2, ?_⟩
  rcases hres with hnc | hres
  · exact Or.inl hnc
  · right
    rcases ggFieldClassicalResidual_split hp2 ⟨hO, hFF, hFN, hFD, hG2⟩ hres with
      h | h | h | h | (h | h)
    · exact absurd h h4
    · exact absurd h h3
    · exact absurd h h2
    · exact absurd h h1
    · exact absurd h h5
    · exact h

end Head

end CFSG.StandardType

end
