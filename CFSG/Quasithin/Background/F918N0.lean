module

public import CFSG.Quasithin.Background.F918H0
public import CFSG.Quasithin.Background.B4Statement

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Matrix commutatorElement

structure Z35 {X : Type} [CommGroup X] [Finite X] (Mb Tb Lb : Subgroup (MulAut X)) (Vb : Subgroup X) :
    Prop where
  exp : ∀ x : X, x ^ 2 = 1
  qsqtk : IsQuotientOfSQTKTC ↥(Mb ⊔ Tb)
  sylow : IsSylowTwoOf Tb (Mb ⊔ Tb)
  quasi : CFSG.IsQuasisimple ↥Lb
  Mp_eq : Mb = conjClosure Lb Tb
  comm_conj : ∀ s ∈ Tb, conjAutSub s Lb = Lb ∨ ⁅Lb, conjAutSub s Lb⁆ = ⊥
  irr : XMod.IsIrr ↥Mb Vb
  indep : sSupIndep {S : Subgroup X | ∃ t ∈ Tb, S = Vb.map t.toMonoidHom}
  gen : orbSup Tb Vb = ⊤
  fix : fixV Mb = ⊥
  homog : ∀ s ∈ Tb, ∀ r ∈ Tb, XMod.Iso ↥Mb (Vb.map s.toMonoidHom) (Vb.map r.toMonoidHom) →
    Vb.map s.toMonoidHom = Vb.map r.toMonoidHom
  o2 : pCoreOf 2 (Mb ⊔ Tb) = ⊥
  qhat : qhatOf (Mb ⊔ Tb) ≤ ((2 : ℚ) : WithTop ℚ)
  nontriv : ∀ s ∈ Tb, ∃ l ∈ conjAutSub s Lb, ∃ v ∈ Vb, l v ≠ v
  lt : Vb < ⊤

@[expose] def Z35Concl {X : Type} [CommGroup X] [Finite X] (Mb Tb Lb : Subgroup (MulAut X))
    (Vb : Subgroup X) : Prop :=
  Mb = Lb ∧ (∃ t ∈ Tb, t ∉ stabSub Vb) ∧
  (∀ t ∈ Tb, t ∉ stabSub Vb →
    (∀ s ∈ Tb, s ∈ stabSub Vb ∨ t⁻¹ * s ∈ stabSub Vb) ∧
      IsIntDirect Vb (Vb.map t.toMonoidHom) ⊤) ∧
  D35Five (autSub Lb Vb) (⊤ : Subgroup ↥Vb)

@[expose] def Z35Main : Prop :=
  ∀ (X : Type) [CommGroup X] [Finite X] (Mb Tb Lb : Subgroup (MulAut X)) (Vb : Subgroup X),
    Z35 Mb Tb Lb Vb → Z35Concl Mb Tb Lb Vb

@[expose] def sec35Img {W : Type} [CommGroup W] (VT C V : Subgroup W) : Subgroup (Sec VT C) :=
  (V.subgroupOf VT).map (QuotientGroup.mk' (C.subgroupOf VT))

@[expose] def D35InspTwo : Prop :=
  ∀ (Y : Type) [CommGroup Y] [Finite Y], (∀ y : Y, y ^ 2 = 1) →
    ∀ (J K K' : Subgroup (MulAut Y)), B51Hyp J K → commV K = ⊤ →
      CFSG.IsQuasisimple ↥K' → (∀ a ∈ K, ∀ b ∈ K', a * b = b * a) → commV K' = ⊤ →
      (∃ (Λ : Type) (_ : Group Λ) (f : Λ →* ↥K) (g : Λ →* ↥K'),
        CFSG.IsQuasisimple Λ ∧ Function.Surjective f ∧ Function.Surjective g) → False

@[expose] def D35InspSum : Prop :=
  ∀ (Y : Type) [CommGroup Y] [Finite Y] (Lb A : Subgroup (MulAut Y)) (n : ℕ) (U₁ U₂ : Subgroup Y),
    (n = 4 ∨ n = 5) → IsIntDirect U₁ U₂ ⊤ →
    (∃ π : ↥(StatedSL n (ZMod 2)) →* ↥Lb,
      (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia Lb U₁ ⊥ π ∧
      (FFModel.dualNat (StatedSL n (ZMod 2))).RealizesVia Lb U₂ ⊥ π) →
    IsElemAbelian2 A → A ≤ Subgroup.normalizer (Lb : Set (MulAut Y)) → ¬ A ≤ stabSub U₁ →
    Nat.card A * Nat.card ↥(fixV A) < Nat.card Y

@[expose] def D35InspUniq : Prop :=
  ∀ (X : Type) [CommGroup X] [Finite X] (Mb Tb Lb : Subgroup (MulAut X)) (V₁ : Subgroup X)
    (A : Subgroup (MulAut X)) (t : MulAut X),
    Z35 Mb Tb Lb V₁ → Mb = Lb → t ∈ Tb → t ∉ stabSub V₁ → A ≤ Tb ⊓ stabSub V₁ →
    A ≤ stabSub (V₁.map t.toMonoidHom) →
    (∃ A₀ : Subgroup (MulAut X),
      B42Case8 (autSub (Lb ⊔ (Tb ⊓ stabSub V₁)) V₁) (autSub Lb V₁) (autSub A₀ V₁) ∨
      B42Case11 (autSub (Lb ⊔ (Tb ⊓ stabSub V₁)) V₁) (autSub Lb V₁) (autSub A₀ V₁)) →
    IsFFStarOffender (autSub (Lb ⊔ (Tb ⊓ stabSub V₁)) V₁) (autSub A V₁) →
    IsFFStarOffender (autSub (Lb ⊔ (Tb ⊓ stabSub (V₁.map t.toMonoidHom))) (V₁.map t.toMonoidHom))
      (autSub A (V₁.map t.toMonoidHom)) → False

@[expose] def D35InspB42 : Prop :=
  ∀ (X : Type) [CommGroup X] [Finite X] (Mb Tb Lb : Subgroup (MulAut X)) (Vb : Subgroup X)
    (A : Subgroup (MulAut X)),
    Z35 Mb Tb Lb Vb → Mb = Lb → A ≤ Tb ⊓ stabSub Vb →
    B42Conclusion (autSub (Lb ⊔ (Tb ⊓ stabSub Vb)) Vb) (autSub Lb Vb) (autSub A Vb) →
    (Tb ⊓ stabSub Vb).relIndex Tb ≤ 2 ∧
    (¬ Tb ≤ stabSub Vb →
      D35Five (autSub Lb Vb) (⊤ : Subgroup ↥Vb) ∨
      B42Case8 (autSub (Lb ⊔ (Tb ⊓ stabSub Vb)) Vb) (autSub Lb Vb) (autSub A Vb) ∨
      B42Case11 (autSub (Lb ⊔ (Tb ⊓ stabSub Vb)) Vb) (autSub Lb Vb) (autSub A Vb))

end CFSG.Quasithin
