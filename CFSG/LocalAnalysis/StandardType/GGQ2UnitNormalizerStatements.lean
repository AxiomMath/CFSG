module

public import CFSG.LocalAnalysis.StandardType.GGQ2UnitStatements
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalNormalizers

public section

namespace CFSG.StandardType.GGQ2Frame.UnitPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Open (IsElemAbelian)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {K : Type} [Field K]

@[expose] def unitTorusAut (ζ : Multiplicative (ZMod 3) →* Kˣ) (N : ℕ)
    (X : Subgroup (LargeEvenProj (unitarySU 2 1 K N))) :
    Set (UnitRaw.Vfull N ≃ₗ[ZMod 3] UnitRaw.Vfull N) :=
  {φ | ∃ y ∈ X, ∀ (w w' : UnitRaw.W N)
      (hD : diagOf ζ w ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)))
      (hD' : diagOf ζ w' ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))),
      (UnitRaw.oneLine N).mkQ w' = φ ((UnitRaw.oneLine N).mkQ w) →
        MulAut.conj y * TableB.projConj _ ⟨diagOf ζ w, hD⟩ * (MulAut.conj y)⁻¹ =
          TableB.projConj _ ⟨diagOf ζ w', hD'⟩}

@[expose] def unitTorusAutH (ζ : Multiplicative (ZMod 3) →* Kˣ) (N : ℕ)
    (X : Subgroup (LargeEvenProj (unitarySU 2 1 K N))) :
    Set (↥(UnitRaw.heart N) ≃ₗ[ZMod 3] ↥(UnitRaw.heart N)) :=
  {φ | ∃ y ∈ X, ∀ (w w' : UnitRaw.W N)
      (hD : diagOf ζ w ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)))
      (hD' : diagOf ζ w' ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)))
      (hw : (UnitRaw.oneLine N).mkQ w ∈ UnitRaw.heart N)
      (hw' : (UnitRaw.oneLine N).mkQ w' ∈ UnitRaw.heart N),
      (⟨(UnitRaw.oneLine N).mkQ w', hw'⟩ : ↥(UnitRaw.heart N)) =
          φ ⟨(UnitRaw.oneLine N).mkQ w, hw⟩ →
        MulAut.conj y * TableB.projConj _ ⟨diagOf ζ w, hD⟩ * (MulAut.conj y)⁻¹ =
          TableB.projConj _ ⟨diagOf ζ w', hD'⟩}

@[expose] def UnitAmbientTorusAut : Prop :=
  ∀ {K : Type} [Field K] [Finite K] (ζ : Multiplicative (ZMod 3) →* Kˣ) (N : ℕ),
    Nat.card K = 4 → Function.Injective ζ → 5 ≤ N →
      unitTorusAut ζ N ⊤ = ((UnitRaw.ambientNormalizer N : Subgroup _) : Set _)

@[expose] def UnitAmbientTorusAutH : Prop :=
  ∀ {K : Type} [Field K] [Finite K] (ζ : Multiplicative (ZMod 3) →* Kˣ) (N : ℕ),
    Nat.card K = 4 → Function.Injective ζ → 5 ≤ N → 3 ∣ N →
      unitTorusAutH ζ N ⊤ = ((UnitRaw.ambientNormalizerH N : Subgroup _) : Set _)

@[expose] def UnitComponentTorusAut : Prop :=
  ∀ {K : Type} [Field K] [Finite K] (ζ : Multiplicative (ZMod 3) →* Kˣ) (N : ℕ),
    Nat.card K = 4 → Function.Injective ζ → 5 ≤ N →
    ∀ S : Finset (Fin N), UnitRaw.admissible S →
      unitTorusAut ζ N (blockPSU S) = ((UnitRaw.normalizerOf S : Subgroup _) : Set _)

@[expose] def UnitComponentTorusAutH : Prop :=
  ∀ {K : Type} [Field K] [Finite K] (ζ : Multiplicative (ZMod 3) →* Kˣ) (N : ℕ),
    Nat.card K = 4 → Function.Injective ζ → 5 ≤ N → 3 ∣ N →
    ∀ S : Finset (Fin N), UnitRaw.admissible S →
      unitTorusAutH ζ N (blockPSU S) = ((UnitRaw.normalizerOfH S : Subgroup _) : Set _)

@[expose] def AutomizerActEq : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {R : Type} [Group R]
    (hEN : E ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* R) (ρ : ↥E →* MulAut R),
    Function.Surjective π → π.ker ≤ Subgroup.center ↥H → commutator H = ⊤ → IsElemAbelian 3 E →
    ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G)) →
    (∀ (b : ↥E) (h : ↥H), π (H.normalizerMonoidHom ⟨b, hEN b.2⟩ h) = ρ b (π h)) →
    ∀ X : Subgroup ↥H, (∀ (b : ↥E) (x : ↥H), x ∈ X → H.normalizerMonoidHom ⟨b, hEN b.2⟩ x ∈ X) →
    ∀ φ : MulAut ↥E, φ ∈ ggAutomizer (X.map H.subtype) E ↔
      ∃ y ∈ X.map π, ∀ b : ↥E, ρ (φ b) = MulAut.conj y * ρ b * (MulAut.conj y)⁻¹

end

end CFSG.StandardType.GGQ2Frame.UnitPlacement
