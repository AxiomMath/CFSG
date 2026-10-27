module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4Regimes
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic

public section

namespace CFSG.StandardType.S2MathAs51600Small

open CFSG CFSG.Assembly

@[expose] def SmallRegime (lab : LargeEvenLabel) : Prop :=
  lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
    lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der

@[expose] def TableRegime (lab : LargeEvenLabel) : Prop :=
  lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twF4

@[expose] def DerivedRegime (lab : LargeEvenLabel) : Prop :=
  lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der

@[expose] noncomputable def A2Label (n : ℕ) : LargeEvenLabel :=
  ⟨if Even n then .A else .twA, 2, n⟩

@[expose] def TableComponentLabel (lab out : LargeEvenLabel) : Prop :=
  (lab.tag = .G2 ∧ (out = ⟨.A, 1, lab.n⟩ ∨ out = A2Label lab.n)) ∨
  (lab.tag = .triD4 ∧
    (out = ⟨.A, 1, 3 * lab.n⟩ ∨ (2 ≤ lab.n ∧ out = A2Label lab.n))) ∨
  (lab.tag = .twF4 ∧ out = ⟨.twA, 2, lab.n⟩)

@[expose] def SmallTableInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → TableRegime lab →
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
      ∀ τ : MulAut R, τ ∈ I → τ ^ 3 = 1 → τ ≠ 1 →
        ∀ L : Subgroup R, IsComponentOf L (ggAutFixedSubgroup τ) →
          ∃ out : LargeEvenLabel, LargeEvenInLambda2 out ∧
            TableComponentLabel lab out ∧ GGHasLabel out (↥L ⧸ Subgroup.center ↥L))

@[expose] def SmallInnerActorsInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    (TableRegime lab ∨ lab.tag = .twB2) →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
        ∀ τ : MulAut R, τ ∈ I → ∃ r : R, τ = MulAut.conj r)

@[expose] def SuzukiOrderInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .twB2 →
    LargeEvenLabelAll lab (fun R _ _ _ => ¬ 3 ∣ Nat.card R)

@[expose] def DerivedOrder (t : LargeEvenLieTag) : ℕ :=
  match t with
  | .B2der => 360
  | .G2der => 6048
  | .twF4der => 17971200
  | _ => 0

@[expose] def DerivedOrderInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → DerivedRegime lab →
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ _ _ =>
      Nat.card R = DerivedOrder lab.tag)

@[expose] def D4OrderLowerInput : Prop :=
  ∀ (lab : LargeEvenLabel) (R : Type) [Group R],
    LargeEvenInLambda2 lab → lab.tag = .D → lab.rank = 4 →
      GGHasLabel lab R → 174182400 ≤ Nat.card R

@[expose] def SmallVacuity : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (A : Subgroup (MulAut X))
    (σ : MulAut X) (J : Subgroup X),
    IsElemAbelian 3 A → σ ∈ A → IsComponentOf J (ggAutFixedSubgroup σ) →
    (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) →
    LargeEvenMarking X (fun lab _ _ I _ θ => SmallRegime lab ∧ GGInducedInn A θ I) →
    ∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ → labJ.tag = .D → labJ.rank = 4 →
      GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) → False

theorem smallAssembly_holds : SmallVacuity → (GGInnerOnD4On SmallRegime) := by
  unfold SmallVacuity
  intro h X _ _ A σ J hA hσ hJ hN hmark labJ hΛ htag hrk hlab
  exact False.elim (h X A σ J hA hσ hJ hN hmark labJ hΛ htag hrk hlab)

end CFSG.StandardType.S2MathAs51600Small

end
