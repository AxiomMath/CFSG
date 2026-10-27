module

public import CFSG.Quasithin.Background.C3Defs
public import CFSG.Quasithin.Background.A3Structure312Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {A : Type} [Group A]

structure C35Data (K Y M₀ V : Subgroup A) : Prop where
  quasisimple : CFSG.Open.IsQuasisimple ↥K
  center : IsPGroup 2 ↥(centerOf K)
  parabolic : IsParabolic2 K Y
  ne_top : Y ≠ K
  normalizer_eq : K ⊓ Subgroup.normalizer (pCoreOf 2 Y : Set A) = Y
  center_le : centerOf K ≤ pCoreOf 2 Y
  eq_perfectCore : M₀ = perfectCore Y
  ne_bot : M₀ ≠ ⊥
  sylow : IsSylowTwoOf (pCoreOf 2 Y) (centralizerSection K M₀ (pCoreOf 2 M₀))
  V_le : V ≤ M₀
  V_le_center : V ≤ centerOf (pCoreOf 2 Y)
  V_elem : IsElemAbelian 2 V
  V_comm : ⁅V, M₀⁆ = V
  V_ne : V ≠ ⊥

@[expose] def C35Concl1 (K Y M₀ V : Subgroup A) : Prop :=
  ∃ n : ℕ, IsRankTwoLie2Over n (↥K ⧸ Subgroup.center ↥K) ∧ IsMaxParabolic2 K Y ∧
    IsPSL 2 2 n (ModO2 M₀) ∧
    ((∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
        IsNaturalSection M₀ V (V ⊓ centerOf K) (CFSG.pCore 2 ↥M₀) (StatedSL 2 F)) ∨
      (IsPSp4 2 n (↥K ⧸ Subgroup.center ↥K) ∧
        ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
          IsNaturalSection M₀ V (V ⊓ Subgroup.centralizer (M₀ : Set A)) (CFSG.pCore 2 ↥M₀)
            (StatedSL 2 F)))

@[expose] def C35Concl2a (n : ℕ) (K Y M₀ V : Subgroup A) : Prop :=
  IsPSL n 2 1 ↥K ∧ IsMaxParabolic2 K Y ∧ IsPSL (n - 1) 2 1 (ModO2 M₀) ∧ V = pCoreOf 2 M₀ ∧
    IsNaturalSection M₀ V ⊥ (CFSG.pCore 2 ↥M₀) (StatedSL (n - 1) (ZMod 2))

@[expose] def C35Concl2b (K Y M₀ V : Subgroup A) : Prop :=
  IsPSL 5 2 1 ↥K ∧ IsExt ↥M₀ (fun N _ => IsE2 6 N) (fun X _ => IsPSL 3 2 1 X) ∧
    IsNaturalSection M₀ V ⊥ (CFSG.pCore 2 ↥M₀) (StatedSL 3 (ZMod 2)) ∧
    ∀ Q : Subgroup A, IsParabolic2 K Q → Y ≤ Q → Q ≠ K →
      Q ≤ Subgroup.normalizer (M₀ : Set A) → perfectCore Q = M₀

@[expose] def C35Concl10 (K M₀ V : Subgroup A) : Prop :=
  IsDoubleCover ↥K ↥(alternatingGroup (Fin 8)) ∧
    centerOf K = V ⊓ Subgroup.centralizer (M₀ : Set A) ∧ IsB48TwoModule M₀ V

structure InspC35 : Prop where
  small : ∀ (A : Type) [Group A] [Finite A] (K Y M₀ V : Subgroup A), C35Data K Y M₀ V →
    ((∃ f : ℕ, (2 ≤ f ∧ IsPSL 2 2 f (↥K ⧸ Subgroup.center ↥K)) ∨
        (2 ≤ f ∧ IsPSU 3 2 f (↥K ⧸ Subgroup.center ↥K)) ∨
        (Odd f ∧ 3 ≤ f ∧ IsSz f (↥K ⧸ Subgroup.center ↥K))) ∨
      IsAlt 5 (↥K ⧸ Subgroup.center ↥K) ∨ IsAlt 6 (↥K ⧸ Subgroup.center ↥K) ∨
      IsPSL 3 2 1 (↥K ⧸ Subgroup.center ↥K) ∨ IsTits (↥K ⧸ Subgroup.center ↥K)) → False
  l3 : ∀ (A : Type) [Group A] [Finite A] (K Y M₀ V : Subgroup A), C35Data K Y M₀ V →
    ∀ f : ℕ, 2 ≤ f → IsPSL 3 2 f (↥K ⧸ Subgroup.center ↥K) → C35Concl1 K Y M₀ V
  sp4 : ∀ (A : Type) [Group A] [Finite A] (K Y M₀ V : Subgroup A), C35Data K Y M₀ V →
    ∀ f : ℕ, 2 ≤ f → IsPSp4 2 f (↥K ⧸ Subgroup.center ↥K) → C35Concl1 K Y M₀ V
  g2 : ∀ (A : Type) [Group A] [Finite A] (K Y M₀ V : Subgroup A), C35Data K Y M₀ V →
    ∀ f : ℕ, 2 ≤ f → IsG2 2 f (↥K ⧸ Subgroup.center ↥K) → C35Concl1 K Y M₀ V
  d4 : ∀ (A : Type) [Group A] [Finite A] (K Y M₀ V : Subgroup A), C35Data K Y M₀ V →
    ∀ f : ℕ, 1 ≤ f → Is3D4 2 f (↥K ⧸ Subgroup.center ↥K) → C35Concl1 K Y M₀ V
  f4 : ∀ (A : Type) [Group A] [Finite A] (K Y M₀ V : Subgroup A), C35Data K Y M₀ V →
    ∀ f : ℕ, Odd f → 3 ≤ f → Is2F4 f (↥K ⧸ Subgroup.center ↥K) → C35Concl1 K Y M₀ V
  l45 : ∀ (A : Type) [Group A] [Finite A] (K Y M₀ V : Subgroup A), C35Data K Y M₀ V →
    Subgroup.center ↥K = ⊥ →
    (IsPSL 4 2 1 (↥K ⧸ Subgroup.center ↥K) ∨ IsAlt 8 (↥K ⧸ Subgroup.center ↥K) ∨
      IsPSL 5 2 1 (↥K ⧸ Subgroup.center ↥K)) →
    (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ C35Concl2a n K Y M₀ V) ∨ C35Concl2b K Y M₀ V
  a8cover : ∀ (A : Type) [Group A] [Finite A] (K Y M₀ V : Subgroup A), C35Data K Y M₀ V →
    Nat.card ↥(Subgroup.center ↥K) = 2 →
    (IsPSL 4 2 1 (↥K ⧸ Subgroup.center ↥K) ∨ IsAlt 8 (↥K ⧸ Subgroup.center ↥K)) →
    C35Concl10 K M₀ V
  levi : ∀ (A : Type) [Group A] [Finite A] (K Y : Subgroup A), CFSG.Open.IsQuasisimple ↥K →
    IsPGroup 2 ↥(centerOf K) →
    (IsAlt 5 (↥K ⧸ Subgroup.center ↥K) ∨ IsAlt 6 (↥K ⧸ Subgroup.center ↥K) ∨
      IsAlt 8 (↥K ⧸ Subgroup.center ↥K) ∨
      ((∃ f : ℕ, (2 ≤ f ∧ IsPSL 2 2 f (↥K ⧸ Subgroup.center ↥K)) ∨
          (1 ≤ f ∧ IsPSL 3 2 f (↥K ⧸ Subgroup.center ↥K)) ∨
          (2 ≤ f ∧ IsPSU 3 2 f (↥K ⧸ Subgroup.center ↥K)) ∨
          (2 ≤ f ∧ IsPSp4 2 f (↥K ⧸ Subgroup.center ↥K)) ∨
          (2 ≤ f ∧ IsG2 2 f (↥K ⧸ Subgroup.center ↥K)) ∨
          (1 ≤ f ∧ Is3D4 2 f (↥K ⧸ Subgroup.center ↥K)) ∨
          (Odd f ∧ 3 ≤ f ∧ Is2F4 f (↥K ⧸ Subgroup.center ↥K)) ∨
          (Odd f ∧ 3 ≤ f ∧ IsSz f (↥K ⧸ Subgroup.center ↥K))) ∨
        IsTits (↥K ⧸ Subgroup.center ↥K)) ∨
      ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ IsPSL n 2 1 (↥K ⧸ Subgroup.center ↥K)) →
    IsParabolic2 K Y → Y ≠ K → perfectCore Y ≠ ⊥ →
    CharTwo (perfectCore Y) ∧
      ((∃ m : ℕ, 2 ≤ m ∧ IsPSL 2 2 m (ModO2 (perfectCore Y))) ∨
        (∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ IsSz m (ModO2 (perfectCore Y))) ∨
        IsPSL 3 2 1 (ModO2 (perfectCore Y)) ∨ IsPSL 4 2 1 (ModO2 (perfectCore Y))) ∧
      (IsPSL 4 2 1 (ModO2 (perfectCore Y)) →
        IsPSL 5 2 1 (↥K ⧸ Subgroup.center ↥K) ∧ IsMaxParabolic2 K Y ∧
          ∀ g ∈ Subgroup.normalizer (K : Set A) ⊓ Subgroup.normalizer (Y : Set A),
            ∃ k ∈ K, ∀ x ∈ K, (g * x * g⁻¹)⁻¹ * (k * x * k⁻¹) ∈ centerOf K)

end CFSG.Quasithin
