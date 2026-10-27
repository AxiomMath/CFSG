module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

public section

namespace CFSG.StandardType.FrameRoute

@[expose] def tmLieOut : TauCeti.LieTypeIndex → ℕ
  | .A n q => Nat.gcd (n + 1) (q.card - 1) * q.exponent * (if n = 1 then 1 else 2)
  | .twistedA n q => 2 * Nat.gcd (n + 1) (q.card + 1) * q.exponent
  | .B n q => Nat.gcd 2 (q.card - 1) * q.exponent * (if n = 2 ∧ q.p = 2 then 2 else 1)
  | .C _ q => Nat.gcd 2 (q.card - 1) * q.exponent
  | .D n q => Nat.gcd 4 (q.card ^ n - 1) * q.exponent * (if n = 4 then 6 else 2)
  | .twistedD n q => Nat.gcd 4 (q.card ^ n + 1) * q.exponent * 2
  | .E6 q => 2 * Nat.gcd 3 (q.card - 1) * q.exponent
  | .E7 q => Nat.gcd 2 (q.card - 1) * q.exponent
  | .E8 q => q.exponent
  | .F4 q => q.exponent * (if q.p = 2 then 2 else 1)
  | .G2 q => q.exponent * (if q.p = 3 then 2 else 1)
  | .twistedE6 q => 2 * Nat.gcd 3 (q.card + 1) * q.exponent
  | .trialityD4 q => 3 * q.exponent
  | .suzuki m => 2 * m + 1
  | .reeG2 m => 2 * m + 1
  | .reeF4 m => 2 * m + 1
  | .tits => 2

@[expose] def TmLieOutAll : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (J : Type) [Group J] [Finite J],
    Nonempty (J ≃* (TauCeti.CFSGIndex.lie d).Group) →
      Nat.card (MulAut J) ∣ Nat.card J * tmLieOut d.1

@[expose] def TmSporadicOutInput : Prop :=
  ∀ (s : TauCeti.SporadicName) (J : Type) [Group J] [Finite J],
    Nonempty (J ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
      Nat.card (MulAut J) ∣ Nat.card J * 2

end CFSG.StandardType.FrameRoute

end
