module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

section Primes

variable {G : Type} [Group G] [Finite G]

@[expose] def piSet (X : Subgroup G) : Set ℕ :=
  {p | p.Prime ∧ p ∣ Nat.card X}

@[expose] def etaSet (n : ℕ) : Set ℕ :=
  {p | p.Prime ∧ p ∣ 2 ^ n - 1}

@[expose] def oPi (α : Set ℕ) (X : Subgroup G) : Subgroup G :=
  ⨆ (N : Subgroup G) (_ : N ≤ X ∧ (N.subgroupOf X).Normal ∧ piSet N ⊆ α), N

@[expose] def IsHallOddIn (A Y : Subgroup G) : Prop :=
  A ≤ Y ∧ Odd (Nat.card A) ∧ ∃ k : ℕ, (A.subgroupOf Y).index = 2 ^ k

@[expose] def IsSU3CentralSquare (X : Type) [Group X] : Prop :=
  ∃ K₁ K₂ : Subgroup X, K₁ ⊔ K₂ = ⊤ ∧ (∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) ∧
    IsSU3 ↥K₁ 3 ∧ IsSU3 ↥K₂ 3 ∧ Nat.card ↥(K₁ ⊓ K₂) = 3

@[expose] def IsSzL2Product (X : Type) [Group X] (n : ℕ) : Prop :=
  ∃ (A B : Type) (_ : Group A) (_ : Group B), Nonempty (X ≃* A × B) ∧
    (IsSz A n ∨ IsL2 A n) ∧ (IsSz B n ∨ IsL2 B n)

@[expose] def IsL2Square (X : Type) [Group X] (n : ℕ) : Prop :=
  ∃ (A B : Type) (_ : Group A) (_ : Group B), Nonempty (X ≃* A × B) ∧ IsL2 A n ∧ IsL2 B n

@[expose] def IsSzSquare (X : Type) [Group X] (n : ℕ) : Prop :=
  ∃ (A B : Type) (_ : Group A) (_ : Group B), Nonempty (X ≃* A × B) ∧ IsSz A n ∧ IsSz B n

@[expose] def NParamSingle (X : Type) [Group X] (n : ℕ) : Prop :=
  IsSz X n ∨ IsL2 X n ∨ IsSU3 X n ∨ IsSL3 X n ∨ IsSp4 X n

@[expose] def NParam (L : Subgroup G) (n : ℕ) : Prop :=
  NParamSingle (Bar2 L) n ∨
    ∃ L₁ L₂ : Subgroup G, L₁ ∈ calC L ∧ L₂ ∈ calC L ∧ L = L₁ ⊔ L₂ ∧ L₁ ≠ L₂ ∧
      ∀ L' ∈ ({L₁, L₂} : Set (Subgroup G)),
        IsSz (Bar2 L') n ∨ IsL2 (Bar2 L') n ∨ (n = 3 ∧ IsSU3 (Bar2 L') 3)

end Primes

section Parabolics

variable {G : Type} [Group G] [Finite G]

@[expose] def IsParabolicTwo (X : Type) [Group X] (P : Subgroup X) : Prop :=
  ∃ S : Sylow 2 X, normalizer (S : Set X) ≤ P

@[expose] def ParabolicOf (L P : Subgroup G) : Prop :=
  CFSG.Open.pCoreOf 2 L ≤ P ∧ P ≤ L ∧
    IsParabolicTwo (Bar2 L) ((P.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))

end Parabolics

section Induced

variable {G : Type} [Group G] [Finite G]

@[expose] def InducedBar (L : Subgroup G) (x : G) (θ : MulAut (Bar2 L)) : Prop :=
  ∀ l l' : ↥L, (l' : G) = x * (l : G) * x⁻¹ → θ (QuotientGroup.mk l) = QuotientGroup.mk l'

@[expose] def InducedQuot (L : Subgroup G) (x : G)
    (θ : MulAut (Bar2 L ⧸ Subgroup.center (Bar2 L))) : Prop :=
  ∀ l l' : ↥L, (l' : G) = x * (l : G) * x⁻¹ →
    θ (QuotientGroup.mk (QuotientGroup.mk l)) = QuotientGroup.mk (QuotientGroup.mk l')

end Induced

end CFSG.LocalAnalysis.UniquenessCase.UC22
