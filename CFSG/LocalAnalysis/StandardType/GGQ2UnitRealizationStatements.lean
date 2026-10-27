module

public import CFSG.LocalAnalysis.StandardType.GGQ2UnitStatements
public import CFSG.LocalAnalysis.StandardType.GGQ2CoverDefs

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

namespace CoverComponents

@[expose] def fixedSub {A R : Type*} [Group A] [Group R] (ρ : A →* MulAut R) : Subgroup R where
  carrier := {r | ∀ a, ρ a r = r}
  mul_mem' {x y} hx hy a := by rw [map_mul, hx a, hy a]
  one_mem' a := map_one (ρ a)
  inv_mem' {x} hx a := by rw [map_inv, hx a]

theorem mem_fixedSub {A R : Type*} [Group A] [Group R] {ρ : A →* MulAut R} {r : R} :
    r ∈ fixedSub ρ ↔ ∀ a, ρ a r = r :=
  Iff.rfl

variable {G : Type} [Group G] {H A : Subgroup G} {R : Type} [Group R]

@[expose] def EquivariantAut (hAN : A ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* R)
    (ρ : ↥A →* MulAut R) : Prop :=
  ∀ (a : ↥A) (h : ↥H), π (H.normalizerMonoidHom ⟨(a : G), hAN a.2⟩ h) = ρ a (π h)

@[expose] def IsComponentOfCoverIffAut : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H A : Subgroup G} {R : Type} [Group R]
    (hAN : A ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* R) (ρ : ↥A →* MulAut R),
    IsPGroup 3 A → Function.Surjective π → π.ker ≤ Subgroup.center ↥H → ¬ 3 ∣ Nat.card π.ker →
    commutator H = ⊤ → EquivariantAut hAN π ρ → ∀ X : Subgroup G,
    IsComponentOf X (H ⊓ Subgroup.centralizer (A : Set G)) ↔
      ∃ Y : Subgroup R, IsComponentOf Y (fixedSub ρ) ∧
        X = (⁅Y.comap π, Y.comap π⁆).map H.subtype

@[expose] def CommuteCoverIffAut : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H A : Subgroup G} {R : Type} [Group R]
    (hAN : A ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* R) (ρ : ↥A →* MulAut R),
    π.ker ≤ Subgroup.center ↥H → EquivariantAut hAN π ρ →
    ∀ X : Subgroup ↥H, commutator X = ⊤ → ∀ e : ↥A,
    (∀ x ∈ X, (e : G) * (x : G) = (x : G) * (e : G)) ↔ ∀ y ∈ X.map π, ρ e y = y

end CoverComponents

namespace UnitPlacement

open CFSG.ClassicalGroups.UnitaryFlag

variable {K : Type} [Field K]

@[expose] def diagFix (ζ : Multiplicative (ZMod 3) →* Kˣ) (N : ℕ)
    (U : Submodule (ZMod 3) (UnitRaw.Vfull N)) : Subgroup (LargeEvenProj (unitarySU 2 1 K N)) where
  carrier := {y | ∀ w : UnitRaw.W N, (UnitRaw.oneLine N).mkQ w ∈ U →
    ∀ hD : diagOf ζ w ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)),
      TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, hD⟩ y = y}
  mul_mem' {x y} hx hy w hw hD := by rw [map_mul, hx w hw hD, hy w hw hD]
  one_mem' w _ hD := map_one _
  inv_mem' {x} hx w hw hD := by rw [map_inv, hx w hw hD]

theorem mem_diagFix {ζ : Multiplicative (ZMod 3) →* Kˣ} {N : ℕ}
    {U : Submodule (ZMod 3) (UnitRaw.Vfull N)} {y : LargeEvenProj (unitarySU 2 1 K N)} :
    y ∈ diagFix ζ N U ↔ ∀ w : UnitRaw.W N, (UnitRaw.oneLine N).mkQ w ∈ U →
      ∀ hD : diagOf ζ w ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)),
        TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, hD⟩ y = y :=
  Iff.rfl

@[expose] def UnitIsComponentOfDiagFixIff : Prop :=
  ∀ {K : Type} [Field K] [Finite K] (ζ : Multiplicative (ZMod 3) →* Kˣ) (N : ℕ),
    Nat.card K = 4 → Function.Injective ζ → 5 ≤ N →
    ∀ (U : Submodule (ZMod 3) (UnitRaw.Vfull N))
      (Y : Subgroup (LargeEvenProj (unitarySU 2 1 K N))),
      IsComponentOf Y (diagFix ζ N U) ↔
        ∃ S : Finset (Fin N), UnitRaw.admissible S ∧ UnitRaw.occurs U S ∧ Y = blockPSU S

@[expose] def UnitBlockPerfect : Prop :=
  ∀ {K : Type} [Field K] [Finite K] (N : ℕ), Nat.card K = 4 → 5 ≤ N →
    ∀ S : Finset (Fin N), UnitRaw.admissible S →
      ⁅blockPSU (K := K) S, blockPSU (K := K) S⁆ = blockPSU (K := K) S

@[expose] def UnitBlockMarked : Prop :=
  ∀ {K : Type} [Field K] [Finite K] (N : ℕ), Nat.card K = 4 → 5 ≤ N →
    ∀ S : Finset (Fin N), UnitRaw.admissible S →
      LargeEvenMarking ↥(blockPSU (K := K) S) (fun lab _ _ _ _ _ => lab = UnitRaw.label S)

end UnitPlacement

end

end CFSG.StandardType.GGQ2Frame

end
