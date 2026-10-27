module

public import CFSG.Quasithin.Background.B4ModelsLie
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

namespace Orbit

variable {V : Type*} [CommGroup V]

@[expose] def orbitIn (H : Subgroup (MulAut V)) (v : V) : Set V :=
  {w | ∃ h ∈ H, (h : MulAut V) v = w}

@[expose] def OrbitLengthsIn (H : Subgroup (MulAut V)) (ℓ : List ℕ) : Prop :=
  ∀ v : V, v ≠ 1 → Nat.card (orbitIn H v) ∈ ℓ

@[expose] def OrbitsSeparated (H : Subgroup (MulAut V)) : Prop :=
  ∀ v w : V, v ≠ 1 → w ≠ 1 → Nat.card (orbitIn H v) = Nat.card (orbitIn H w) →
    ∃ h ∈ H, (h : MulAut V) v = w

@[expose] def OrbitLengthsInMod (H : Subgroup (MulAut V)) (z : V) (ℓ : List ℕ) : Prop :=
  ∀ v : V, v ≠ 1 → v ≠ z → Nat.card (orbitIn H v) ∈ ℓ

@[expose] def OrbitsSeparatedMod (H : Subgroup (MulAut V)) (z : V) : Prop :=
  ∀ v w : V, v ≠ 1 → w ≠ 1 → v ≠ z → w ≠ z →
    Nat.card (orbitIn H v) = Nat.card (orbitIn H w) →
      ∃ h ∈ H, (h : MulAut V) v = w ∨ (h : MulAut V) v = w * z

end Orbit

open Orbit

@[expose] def zornO0Model {F : Type} [Field F]
    (Γ : Subgroup (quasithinZorn F ≃ₗ[F] quasithinZorn F)) : FFModel where
  Gam := ↥Γ
  Amb := Multiplicative (quasithinZorn F)
  act := zornAct Γ
  sec := zornO0 F
  ker := ⊥

@[expose] def G2WeylDerived {V : Type*} [CommGroup V] (H : Subgroup (MulAut V)) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
    (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).Realizes H ⊤ ⊥

@[expose] def OrbitL52Ten : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) → Nat.card V = 2 ^ 10 →
    ∀ H : Subgroup (MulAut V), Nonempty (↥H ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
      (∀ W : Subgroup V, (∀ h ∈ H, ∀ w ∈ W, (h : MulAut V) w ∈ W) → W = ⊥ ∨ W = ⊤) →
        OrbitLengthsIn H [155, 868] ∧ OrbitsSeparated H

@[expose] def OrbitHatA6Six : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) → Nat.card V = 2 ^ 6 →
    ∀ H : Subgroup (MulAut V), Group.IsPerfect ↥H → Nat.card (Subgroup.center ↥H) = 3 →
      Nonempty (↥H ⧸ Subgroup.center ↥H ≃* alternatingGroup (Fin 6)) →
        OrbitLengthsIn H [18, 45] ∧ OrbitsSeparated H

@[expose] def OrbitTripleA6Six : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H : Subgroup (MulAut V)),
    TripleA6Six H ⊤ ⊥ → OrbitLengthsIn H [18, 45] ∧ OrbitsSeparated H

@[expose] def HatA6SixModel : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) → Nat.card V = 2 ^ 6 →
    ∀ H : Subgroup (MulAut V), Group.IsPerfect ↥H → Nat.card (Subgroup.center ↥H) = 3 →
      Nonempty (↥H ⧸ Subgroup.center ↥H ≃* alternatingGroup (Fin 6)) → TripleA6Six H ⊤ ⊥

theorem orbitHatA6Six_of (h1 : OrbitTripleA6Six) (h2 : HatA6SixModel) : OrbitHatA6Six :=
  fun V _ _ hV2 hV H hperf hZ he => h1 V H (h2 V hV2 hV H hperf hZ he)

@[expose] def OrbitG2Weyl : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H : Subgroup (MulAut V)) (z : V), z ≠ 1 →
    z ∈ fixV H → G2WeylDerived H → OrbitLengthsInMod H z [63] ∧ OrbitsSeparatedMod H z

@[expose] def L32FourSylowFix : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) → Nat.card V = 2 ^ 4 →
    ∀ H : Subgroup (MulAut V), commV H = ⊤ → BinaryNaturalSL H ⊤ (fixV H) 3 1 →
      ∀ S : Subgroup (MulAut V), S ≤ H → Nat.card S = 8 → fixV S = fixV H

@[expose] def AltNaturalCoverSeven : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut V)) (Z : Subgroup V), Z ≤ fixV H → commV H = ⊤ →
      AlternatingNatural H ⊤ Z 7 → Z = ⊥

@[expose] def G2NaturalCover : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut V)) (Z : Subgroup V), Z ≤ fixV H → commV H = ⊤ →
      G2NaturalDerived H ⊤ Z 1 →
        Z = ⊥ ∨ (Nat.card Z = 2 ∧ Nat.card V = 2 ^ 7 ∧ G2WeylDerived H)

end CFSG.Quasithin.H13
