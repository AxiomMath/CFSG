module

public import CFSG.RankThree.GF2n.Tim81.Sec7.Defs

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
open scoped MatrixGroups commutatorElement

abbrev perpRoots {K : Type} [Group K] (Δ : Set (Subgroup K)) (X : Subgroup K) : Subgroup K :=
  ⨆ C ∈ {C : Subgroup K | C ∈ Δ ∧ C ≤ Subgroup.centralizer (X : Set K)}, C

@[expose] def UnitaryTIModule : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (X₀ : Subgroup K) (Δ : Set (Subgroup K)) (f n : ℕ)
    (hf : 1 ≤ f) (hn : 4 ≤ n), 2 ≤ f → IsSUImage X₀ Δ f n hf (by omega) →
    ∀ (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
      (ρ : Representation (ZMod 2) K W), (∃ x ∈ X₀, ∃ w, ρ x w ≠ w) →
      (∀ A ∈ Δ, ∀ B ∈ Δ,
        Submodule.span (ZMod 2) {u | ∃ a ∈ A, ∃ w, u = ρ a w - w} =
          Submodule.span (ZMod 2) {u | ∃ b ∈ B, ∃ w, u = ρ b w - w} ∨
        Submodule.span (ZMod 2) {u | ∃ a ∈ A, ∃ w, u = ρ a w - w} ⊓
          Submodule.span (ZMod 2) {u | ∃ b ∈ B, ∃ w, u = ρ b w - w} = ⊥) →
      Nat.card W = (2 ^ f) ^ (2 * n) →
        ∀ U : Submodule (ZMod 2) W, (∀ x ∈ X₀, U.map (ρ x) ≤ U) → U = ⊥ ∨ U = ⊤

@[expose] def SU3ModuleBound : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (X₀ : Subgroup K) (Δ : Set (Subgroup K)) (f : ℕ)
    (hf : 1 ≤ f), 2 ≤ f → IsSUImage X₀ Δ f 3 hf (by norm_num) →
    ∀ (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
      (ρ : Representation (ZMod 2) K W), (∃ x ∈ X₀, ∃ w, ρ x w ≠ w) →
      (∀ U : Submodule (ZMod 2) W, (∀ x ∈ X₀, U.map (ρ x) ≤ U) → U = ⊥ ∨ U = ⊤) →
      (2 ^ f) ^ 6 ≤ Nat.card W

@[expose] def UnitaryLinePair : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (X₀ : Subgroup K) (Δ : Set (Subgroup K)) (f n : ℕ)
    (hf : 1 ≤ f) (hn : 4 ≤ n), 2 ≤ f → IsSUImage X₀ Δ f n hf (by omega) →
    ∀ A ∈ Δ, ∀ B ∈ Δ, IsL2Gen A B →
      (∀ h ∈ A ⊔ B, orderOf h = 2 ^ f + 1 → ∀ C ∈ Δ,
        h ∈ Subgroup.normalizer (C : Set K) → ⁅C, A ⊔ B⁆ = ⊥) ∧
      (∀ h5 : 5 ≤ n, IsSUImage (perpRoots Δ (A ⊔ B))
        {C | C ∈ Δ ∧ C ≤ Subgroup.centralizer ((A ⊔ B : Subgroup K) : Set K)}
        f (n - 2) hf (by omega)) ∧
      (n = 4 → ∃ C ∈ Δ, ∃ D ∈ Δ, IsL2Gen C D ∧ perpRoots Δ (A ⊔ B) = C ⊔ D ∧
        Nat.card ↥(X₀ ⊓ Subgroup.centralizer
          ((A ⊔ B ⊔ (C ⊔ D) : Subgroup K) : Set K)) = 2 ^ f + 1 ∧
        ∃ g ∈ X₀, conjSubgroup g (A ⊔ B) = C ⊔ D ∧ conjSubgroup g (C ⊔ D) = A ⊔ B)

@[expose] def UnitaryPerpCount : Prop :=
  ∀ (K K' : Type) [Group K] [Finite K] [Group K'] [Finite K'] (X : Subgroup K)
    (X' : Subgroup K') (Δ : Set (Subgroup K)) (Δ' : Set (Subgroup K')) (f m m' : ℕ)
    (hf : 1 ≤ f) (hm : 4 ≤ m) (hm' : 2 ≤ m'), IsSUImage X Δ f m hf (by omega) →
    IsSUImage X' Δ' f m' hf hm' → ∀ T ∈ Δ,
      Nat.card {B // B ∈ Δ ∧ B ≠ T ∧ ⁅T, B⁆ = ⊥} = (2 ^ f) ^ 2 * Nat.card Δ' → m = m' + 2

@[expose] def UnitaryAutCentralizer : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (X₀ : Subgroup K) (Δ : Set (Subgroup K)) (f n : ℕ)
    (hf : 1 ≤ f) (hn : 5 ≤ n), 2 ≤ f → X₀.Normal → IsSUImage X₀ Δ f n hf (by omega) →
    Odd (Nat.card ↥(Subgroup.centralizer (X₀ : Set K))) →
      ∀ A ∈ Δ, ∀ B ∈ Δ, IsL2Gen A B → ∀ h ∈ A ⊔ B, orderOf h = 2 ^ f + 1 →
        ∀ y ∈ Subgroup.centralizer ((perpRoots Δ (A ⊔ B) : Subgroup K) : Set K) ⊓
            Subgroup.centralizer ({h} : Set K),
          IsPGroup 2 (Subgroup.zpowers y) → y ∈ Subgroup.centralizer (X₀ : Set K)

@[expose] def UnitaryFourAutCentralizer : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (X₀ : Subgroup K) (Δ : Set (Subgroup K)) (f : ℕ)
    (hf : 1 ≤ f), 2 ≤ f → X₀.Normal → IsSUImage X₀ Δ f 4 hf (by norm_num) →
    Odd (Nat.card ↥(Subgroup.centralizer (X₀ : Set K))) →
    ∀ A ∈ Δ, ∀ B ∈ Δ, IsL2Gen A B → ∀ h ∈ A ⊔ B, orderOf h = 2 ^ f + 1 →
      (∀ y ∈ Subgroup.centralizer ((perpRoots Δ (A ⊔ B) : Subgroup K) : Set K) ⊓
          Subgroup.centralizer ({h} : Set K),
        IsPGroup 2 (Subgroup.zpowers y) →
          y ∈ Subgroup.centralizer ((A ⊔ B : Subgroup K) : Set K)) ∧
      (pPrimeCore 2 ↥(Subgroup.centralizer
        ((A ⊔ B ⊔ perpRoots Δ (A ⊔ B) : Subgroup K) : Set K))).index ≤ 2

@[expose] def Tim90Points : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (Δ : Set (Subgroup H)),
    Timmesfeld.Transvection.IsTransvectionClass Δ →
    (∀ A ∈ Δ, ∀ B ∈ Δ, Timmesfeld.ARS.Commuting A B ∨ IsL2Gen A B) →
    (∀ N : Subgroup H, N.Normal → Group.IsNilpotent N → N = ⊥) →
    Timmesfeld.Transvection.PointsDetermined Δ

abbrev sylowRoots {K : Type} [Group K] (X₀ : Subgroup K) (Δ : Set (Subgroup K))
    (S : Sylow 2 ↥X₀) : Subgroup K :=
  ⨆ A ∈ {A : Subgroup K | A ∈ Δ ∧ A ≤ (S : Subgroup ↥X₀).map X₀.subtype}, A

@[expose] def UnitaryRootTypeSylow : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (X₀ : Subgroup K) (Δ : Set (Subgroup K)) (f N : ℕ)
    (hf : 1 ≤ f) (hN : 6 ≤ N), 2 ≤ f → IsSUImage X₀ Δ f N hf (by omega) →
    Subgroup.centralizer (X₀ : Set K) = ⊥ →
    ∀ W : Subgroup K, W ≤ Subgroup.normalizer (X₀ : Set K) → (∃ k : K, conjSubgroup k W ∈ Δ) →
      Tim78.IsRootTypeTI W → ∀ T ∈ Δ, ⁅T, W⁆ = ⊥ →
        ∃ S : Sylow 2 ↥X₀, W ≤ sylowRoots X₀ Δ S ∧ T ≤ sylowRoots X₀ Δ S

@[expose] def UnitarySylowRoots : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (X₀ : Subgroup K) (Δ : Set (Subgroup K)) (f N : ℕ)
    (hf : 1 ≤ f) (hN : 6 ≤ N), 2 ≤ f → IsSUImage X₀ Δ f N hf (by omega) →
    ∀ S : Sylow 2 ↥X₀,
      (∀ x ∈ sylowRoots X₀ Δ S, ∀ y ∈ sylowRoots X₀ Δ S, x * y = y * x) ∧
      (∀ x ∈ sylowRoots X₀ Δ S, x * x = 1) ∧
      Nat.card ↥(sylowRoots X₀ Δ S) = (2 ^ f) ^ ((N / 2) ^ 2) ∧
      (∀ T ∈ Δ, T ≤ sylowRoots X₀ Δ S →
        inSubgroup (pCore 2) (X₀ ⊓ Subgroup.normalizer (T : Set K)) ≤
          Subgroup.normalizer (sylowRoots X₀ Δ S : Set K)) ∧
      (∀ A ∈ Δ, A ≤ Subgroup.centralizer (sylowRoots X₀ Δ S : Set K) → A ≤ sylowRoots X₀ Δ S) ∧
      (∀ E : Subgroup K, E ≤ X₀ ⊓ Subgroup.normalizer (sylowRoots X₀ Δ S : Set K) →
        (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x * x = 1) →
          Nat.card ↥(sylowRoots X₀ Δ S) ≤ Nat.card ↥E → E = sylowRoots X₀ Δ S)
