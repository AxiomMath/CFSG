module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes

public section

namespace CFSG.Yardstones.Md42047359a2a

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator Subgroup

@[expose] def SimpleBp (p : ℕ) (S : Type) [Group S] : Prop :=
  ∀ β : MulAut S, β ^ p = 1 →
    ⁅GLAPLayer p (fixSubgroup β), GLAPPrimeCoreOf p (fixSubgroup β)⁆ = ⊥

@[expose] def CatalogueBp (p : ℕ) (i : TauCeti.CFSGIndex) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Nonempty (S ≃* i.Group) → SimpleBp p S

@[expose] def AlternatingTwoBp : Prop :=
  ∀ (n : ℕ) (hn : 5 ≤ n), CatalogueBp 2 (TauCeti.CFSGIndex.alternating n hn)

@[expose] def mathieuLeechNames : Finset TauCeti.SporadicName :=
  {.M11, .M12, .M22, .M23, .M24, .J2, .HS, .McL, .Suz, .Co1, .Co2, .Co3}

@[expose] def monsterSectionNames : Finset TauCeti.SporadicName :=
  {.He, .HN, .Th, .Fi22, .Fi23, .Fi24Prime, .B, .M}

@[expose] def pariahNames : Finset TauCeti.SporadicName :=
  {.J1, .J3, .J4, .ONan, .Ly, .Ru}

@[expose] def SporadicMathieuLeechBp : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ name ∈ mathieuLeechNames, B3SporPair name p

@[expose] def SporadicMonsterSectionBp : Prop :=
  ∀ p : ℕ, p.Prime → ∀ name ∈ monsterSectionNames, (p ≠ 2 ∨ name = .He) → B3SporPair name p

@[expose] def SporadicPariahBp : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ name ∈ pariahNames, B3SporPair name p

inductive LieFamily where
  | linearUnitary
  | symplecticOrthogonal
  | exceptional
  | suzukiReeTits
  deriving DecidableEq

@[expose] def lieFamily : TauCeti.LieTypeIndex → LieFamily
  | .A _ _ | .twistedA _ _ => .linearUnitary
  | .B _ _ | .C _ _ | .D _ _ | .twistedD _ _ => .symplecticOrthogonal
  | .E6 _ | .E7 _ | .E8 _ | .F4 _ | .G2 _ | .twistedE6 _ | .trialityD4 _ => .exceptional
  | .suzuki _ | .reeG2 _ | .reeF4 _ | .tits => .suzukiReeTits

@[expose] def LieSemisimpleCentOn (F : LieFamily) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, lieFamily idx.1 = F →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ idx.1.characteristic → ∀ β : MulAut S, β ^ p = 1 →
        β ≠ 1 → PerfectInLayer β

@[expose] def LieSemisimpleCentLinearUnitary : Prop := LieSemisimpleCentOn .linearUnitary

@[expose] def LieSemisimpleCentSymplecticOrthogonal : Prop :=
  LieSemisimpleCentOn .symplecticOrthogonal

@[expose] def LieSemisimpleCentExceptional : Prop := LieSemisimpleCentOn .exceptional

@[expose] def LieSemisimpleCentSuzukiReeTits : Prop := LieSemisimpleCentOn .suzukiReeTits

@[expose] def LieClassicalOddCharTwoBp : Prop :=
  ∀ idx : TauCeti.ValidLieTypeIndex,
    (lieFamily idx.1 = .linearUnitary ∨ lieFamily idx.1 = .symplecticOrthogonal) →
      idx.1.characteristic ≠ 2 → CatalogueBp 2 (TauCeti.CFSGIndex.lie idx)

@[expose] def LieExceptionalOddCharTwoBp : Prop :=
  ∀ idx : TauCeti.ValidLieTypeIndex,
    (lieFamily idx.1 = .exceptional ∨ lieFamily idx.1 = .suzukiReeTits) →
      idx.1.characteristic ≠ 2 → CatalogueBp 2 (TauCeti.CFSGIndex.lie idx)

@[expose] def LieEvenCharTwoBp : Prop :=
  ∀ idx : TauCeti.ValidLieTypeIndex, idx.1.characteristic = 2 →
    CatalogueBp 2 (TauCeti.CFSGIndex.lie idx)

@[expose] def ElementCaseBp : Prop :=
  ∀ (Z : Type) [Group Z] [Finite Z] (p : ℕ), p.Prime →
    lBalancePrimeCore p (⊤ : Subgroup Z) = ⊥ →
    (∀ K : Subgroup Z, CFSG.IsComponent K →
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer (K ⧸ center K)) ∧
        SimpleBp p (K ⧸ center K)) →
    ∀ x : Z, (∃ n : ℕ, x ^ p ^ n = 1) → x ^ p ∈ center Z →
      (∀ K : Subgroup Z, CFSG.IsComponent K →
        lBalancePrimeCore p (centralizer ({x} : Set Z)) ≤ normalizer (K : Set Z)) →
      ∀ a ∈ lBalancePLayer p (centralizer ({x} : Set Z)),
        ∀ b ∈ lBalancePrimeCore p (centralizer ({x} : Set Z)), a * b = b * a

end CFSG.Yardstones.Md42047359a2a
