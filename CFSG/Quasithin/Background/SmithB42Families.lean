module

public import CFSG.Quasithin.Background.B4Statement

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def AsB42For (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L : Subgroup (MulAut V), B4Hyp G L → P ↥L →
      ∀ A : Subgroup (MulAut V), IsFFStarOffender G A → B42Conclusion G L A

@[expose] def AsB42NoOffenderFor (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L : Subgroup (MulAut V), B4Hyp G L → P ↥L →
      ∀ A : Subgroup (MulAut V), ¬ IsFFStarOffender G A

section Types

variable (X : Type) [Group X]

@[expose] def B42TypeU3Even : Prop :=
  ∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 3 2 f

@[expose] def B42TypeSz : Prop :=
  ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ SuzukiModel (X ⧸ Subgroup.center X) 2 f

@[expose] def B42TypeTrialityD4 : Prop :=
  ∃ f : ℕ, 1 ≤ f ∧ ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .trialityD4 2 f

@[expose] def B42TypeReeF4 : Prop :=
  (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel (X ⧸ Subgroup.center X) .twistedF4 2 f) ∨
    ReeTitsModel (X ⧸ Subgroup.center X) .Tits 2 1

@[expose] def B42TypeL2Even : Prop :=
  Subgroup.center X = ⊥ ∧
    ∃ f : ℕ, 3 ≤ f ∧ StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 2 2 f

@[expose] def B42TypeL32 : Prop :=
  Subgroup.center X = ⊥ ∧ StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 3 2 1

@[expose] def B42TypeL3Even : Prop :=
  ∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 3 2 f

@[expose] def B42TypeSp4Even : Prop :=
  Subgroup.center X = ⊥ ∧
    ∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel (X ⧸ Subgroup.center X) .PSp 2 2 f

@[expose] def B42TypeG2Even : Prop :=
  Subgroup.center X = ⊥ ∧
    ∃ f : ℕ, 2 ≤ f ∧ ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 2 f

@[expose] def B42TypeU33 : Prop :=
  Subgroup.center X = ⊥ ∧ StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 3 3 1

@[expose] def B42TypeL42 : Prop :=
  Subgroup.center X = ⊥ ∧ StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 4 2 1 ∧
    Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 8))

@[expose] def B42TypeL52 : Prop :=
  Subgroup.center X = ⊥ ∧ StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 5 2 1

@[expose] def B42TypeAlt5 : Prop :=
  Subgroup.center X = ⊥ ∧ Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 5)) ∧
    StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 2 2 2

@[expose] def B42TypeAlt6 : Prop :=
  Subgroup.center X = ⊥ ∧ Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 6))

@[expose] def B42TypeHatA6 : Prop :=
  IsHat X ↥(alternatingGroup (Fin 6))

@[expose] def B42TypeAlt7 : Prop :=
  Subgroup.center X = ⊥ ∧ Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 7))

end Types

@[expose] def AsB42U3Even : Prop := AsB42NoOffenderFor B42TypeU3Even

@[expose] def AsB42Sz : Prop := AsB42NoOffenderFor B42TypeSz

@[expose] def AsB42TrialityD4 : Prop := AsB42NoOffenderFor B42TypeTrialityD4

@[expose] def AsB42ReeF4 : Prop := AsB42NoOffenderFor B42TypeReeF4

@[expose] def AsB42L2Even : Prop := AsB42For B42TypeL2Even

@[expose] def AsB42L32 : Prop := AsB42For B42TypeL32

@[expose] def AsB42L3Even : Prop := AsB42For B42TypeL3Even

@[expose] def AsB42Sp4Even : Prop := AsB42For B42TypeSp4Even

@[expose] def AsB42G2Even : Prop := AsB42For B42TypeG2Even

@[expose] def AsB42U33 : Prop := AsB42For B42TypeU33

@[expose] def AsB42L42 : Prop := AsB42For B42TypeL42

@[expose] def AsB42L52 : Prop := AsB42For B42TypeL52

@[expose] def AsB42Alt5 : Prop := AsB42For B42TypeAlt5

@[expose] def AsB42Alt6 : Prop := AsB42For B42TypeAlt6

@[expose] def AsB42HatA6 : Prop := AsB42For B42TypeHatA6

@[expose] def AsB42Alt7 : Prop := AsB42For B42TypeAlt7

end CFSG.Quasithin
