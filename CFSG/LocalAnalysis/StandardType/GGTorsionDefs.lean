module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGForms
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionDefs

@[expose] def GGTorsionDatum (P : LargeEvenLabel → Prop) (p : ℕ) {X : Type} [Group X]
    (δ : MulAut X) (J : Subgroup X) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ δ ^ p = 1 ∧ δ ≠ 1 ∧ IsComponentOf J (ggAutFixedSubgroup δ) ∧
    LargeEvenMarking X fun lab _ _ I _ θ => P lab ∧ ggInducedAut θ δ ∈ I

@[expose] def GGTorsionKnownOver (P : LargeEvenLabel → Prop) : Prop :=
  ∀ (p : ℕ) (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ (δ : MulAut X) (J : Subgroup X), GGTorsionDatum P p δ J →
      ¬ LargeEvenMarking J fun lab _ _ _ _ _ => GGL45TorsionTag lab

@[expose] def GGTorsionKnown : Prop :=
  GGTorsionKnownOver fun _ => True

@[expose] def GGTorsionAmbA (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∨ lab.tag = .twA

@[expose] def GGTorsionAmbBCD (lab : LargeEvenLabel) : Prop :=
  lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨ lab.tag = .twD

@[expose] def GGTorsionAmbExc (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4 ∨ lab.tag = .twE6 ∨
    lab.tag = .triD4 ∨ lab.tag = .G2

@[expose] def GGTorsionAmbSmall (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twB2 ∨ lab.tag = .twF4 ∨ lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der

end TorsionDefs

end CFSG.StandardType
