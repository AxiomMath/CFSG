module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIRows

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def KGFNIFieldExponentOn (S : LargeEvenLabel → Prop) : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → S lab →
    LargeEvenLabelAll lab fun R _ _ F => ∀ f ∈ F, f ^ (kgfniFieldDegree lab * lab.n) = 1

@[expose] def KGFNIRawSimpleOn (S : LargeEvenLabel → Prop) : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → S lab →
    LargeEvenLabelAll lab fun R _ _ _ => IsSimpleGroup R ∧ ∃ a b : R, a * b ≠ b * a

@[expose] def KGFNIClassicalLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨ lab.tag = .twD

@[expose] def KGFNIChevalleyLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .G2 ∨ lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8

@[expose] def KGFNITwistedLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨ lab.tag = .B2der ∨
    lab.tag = .G2der ∨ lab.tag = .twF4der

theorem kgfni_label_cover (lab : LargeEvenLabel) :
    KGFNIClassicalLabel lab ∨ KGFNIChevalleyLabel lab ∨ KGFNITwistedLabel lab := by
  unfold KGFNIClassicalLabel KGFNIChevalleyLabel KGFNITwistedLabel
  cases lab.tag <;> simp

theorem kgfniFieldExponentOn_of_parts (hc : KGFNIFieldExponentOn KGFNIClassicalLabel)
    (he : KGFNIFieldExponentOn KGFNIChevalleyLabel) (ht : KGFNIFieldExponentOn KGFNITwistedLabel) :
    KGFNIFieldExponentOn fun _ => True := by
  intro lab hlab _
  rcases kgfni_label_cover lab with h | h | h
  · exact hc lab hlab h
  · exact he lab hlab h
  · exact ht lab hlab h

theorem kgfniRawSimpleOn_of_parts (hc : KGFNIRawSimpleOn KGFNIClassicalLabel)
    (he : KGFNIRawSimpleOn KGFNIChevalleyLabel) (ht : KGFNIRawSimpleOn KGFNITwistedLabel) :
    KGFNIRawSimpleOn fun _ => True := by
  intro lab hlab _
  rcases kgfni_label_cover lab with h | h | h
  · exact hc lab hlab h
  · exact he lab hlab h
  · exact ht lab hlab h

end CFSG.StandardType
