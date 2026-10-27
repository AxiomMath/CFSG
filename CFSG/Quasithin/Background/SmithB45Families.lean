module

public import CFSG.Quasithin.Background.SmithB42Families
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Native

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def AsB45DichotomyNat : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ L : Subgroup (MulAut W), CFSG.IsQuasisimple ↥L → XMod.IsIrrSec ↥L (⊥ : Subgroup W) ⊤ →
      CFSG.Milestones.SQTKSimpleList (↥L ⧸ Subgroup.center ↥L) →
      ∀ E : Subgroup (MulAut W), E ≤ Subgroup.normalizer (L : Set (MulAut W)) → E ≠ ⊥ →
        IsElemAbelian2 E → commSeries E 3 = ⊥ →
        Nat.card W ≤ Nat.card E ^ 2 * Nat.card (fixV E) →
        (Bridge.SQTKCharTwoOrAltNative (↥L ⧸ Subgroup.center ↥L) ∨
          ∃ s : TauCeti.SporadicName,
            (s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J2) ∧
            Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier s)) ∧
        (Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7)) →
          Subgroup.center ↥L = ⊥)

@[expose] def AsB45For (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L : Subgroup (MulAut V), B4Hyp G L → P ↥L →
      ((1 : ℚ) : WithTop ℚ) < qhatOf G → qhatOf G ≤ ((2 : ℚ) : WithTop ℚ) →
        AsB45Table G L ∨ AsB45Part3 G L

@[expose] def AsB45FFOnlyFor (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L : Subgroup (MulAut V), B4Hyp G L → P ↥L →
      qhatOf G ≤ ((2 : ℚ) : WithTop ℚ) → qhatOf G ≤ ((1 : ℚ) : WithTop ℚ)

@[expose] def AsB45No2FFor (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L : Subgroup (MulAut V), B4Hyp G L → P ↥L → ((2 : ℚ) : WithTop ℚ) < qhatOf G

theorem AsB45No2FFor.ffOnly {P : ∀ (X : Type) [Group X], Prop} (h : AsB45No2FFor P) :
    AsB45FFOnlyFor P :=
  fun V _ _ hV G L hHyp hP hq => absurd hq (not_le.mpr (h V hV G L hHyp hP))

theorem AsB45FFOnlyFor.asB45For {P : ∀ (X : Type) [Group X], Prop} (h : AsB45FFOnlyFor P) :
    AsB45For P :=
  fun V _ _ hV G L hHyp hP h1 h2 => absurd (h V hV G L hHyp hP h2) (not_le.mpr h1)

theorem AsB45No2FFor.asB45For {P : ∀ (X : Type) [Group X], Prop} (h : AsB45No2FFor P) :
    AsB45For P :=
  h.ffOnly.asB45For

@[expose] def B45TypeSpor (s : TauCeti.SporadicName) (X : Type) [Group X] : Prop :=
  Subgroup.center X = ⊥ ∧ IsSporadic s X

@[expose] def B45TypeHatM22 (X : Type) [Group X] : Prop :=
  IsHat X (NativeSporadic.Carrier .M22)

@[expose] def AsB45TrialityD4 : Prop := AsB45No2FFor B42TypeTrialityD4

@[expose] def AsB45ReeF4 : Prop := AsB45No2FFor B42TypeReeF4

@[expose] def AsB45G2Even : Prop := AsB45FFOnlyFor B42TypeG2Even

@[expose] def AsB45L32 : Prop := AsB45FFOnlyFor B42TypeL32

@[expose] def AsB45L42 : Prop := AsB45FFOnlyFor B42TypeL42

@[expose] def AsB45L52 : Prop := AsB45FFOnlyFor B42TypeL52

@[expose] def AsB45Alt6 : Prop := AsB45FFOnlyFor B42TypeAlt6

@[expose] def AsB45HatA6 : Prop := AsB45FFOnlyFor B42TypeHatA6

@[expose] def AsB45Alt7 : Prop := AsB45For B42TypeAlt7

@[expose] def AsB45Alt5 : Prop := AsB45For B42TypeAlt5

@[expose] def AsB45L2Even : Prop := AsB45For B42TypeL2Even

@[expose] def AsB45U3Even : Prop := AsB45For B42TypeU3Even

@[expose] def AsB45Sz : Prop := AsB45For B42TypeSz

@[expose] def AsB45L3Even : Prop := AsB45For B42TypeL3Even

@[expose] def AsB45U33 : Prop := AsB45For B42TypeU33

@[expose] def AsB45Sp4Even : Prop := AsB45For B42TypeSp4Even

@[expose] def AsB45M12 : Prop := AsB45For (B45TypeSpor .M12)

@[expose] def AsB45HatM22 : Prop := AsB45For B45TypeHatM22

@[expose] def AsB45M22 : Prop := AsB45For (B45TypeSpor .M22)

@[expose] def AsB45M23 : Prop := AsB45For (B45TypeSpor .M23)

@[expose] def AsB45M24 : Prop := AsB45For (B45TypeSpor .M24)

@[expose] def AsB45J2 : Prop := AsB45For (B45TypeSpor .J2)

end CFSG.Quasithin
