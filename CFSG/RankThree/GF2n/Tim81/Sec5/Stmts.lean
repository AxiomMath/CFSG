module

public import CFSG.RankThree.GF2n.Tim81.Sec5.Defs

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec5

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

@[expose] def Stmt51a (M V : Subgroup G) : Prop :=
  ∀ U ∈ sigmaSet M V, ∀ x ∈ Pc M V, x ∉ Subgroup.centralizer (U : Set G) →
    V ⊔ ⁅U, Subgroup.zpowers x⁆ ∈ fSet M V

@[expose] def Stmt51d (M V : Subgroup G) : Prop :=
  ∀ A ∈ fSet M V,
    Nat.card ↥(Pc M V ⊓ Subgroup.centralizer (A : Set G)) * Nat.card V = Nat.card ↥(Pc M V)

@[expose] def Stmt51e (M V : Subgroup G) : Prop :=
  ∀ A ∈ fSet M V, ∀ B ∈ fSet M V, A = B ∨ A ⊓ B = V

@[expose] def Stmt52a (M V : Subgroup G) : Prop :=
  ∀ U ∈ sigmaSet M V, ∀ x ∈ ⁅Pc M V, U⁆, ∃ A ∈ fSet M V, x ∈ A ∧ A ≤ ⁅Pc M V, U⁆

@[expose] def Stmt53 (M V : Subgroup G) : Prop :=
  ∀ U ∈ sigmaSet M V, ∀ U' ∈ sigmaSet M V,
    ⁅Pc M V, U⁆ ≤ Pc M V ⊓ Subgroup.centralizer (↑⁅Pc M V, U'⁆ : Set G) → ⁅U, U'⁆ = ⊥

@[expose] def Stmt54 (M V : Subgroup G) : Prop :=
  ∀ U ∈ sigmaSet M V, ∀ U' ∈ omegaSet V, U' ≠ V → U' ⊓ (U ⊔ V) ≠ ⊥ → U' = U

@[expose] def Stmt55 (M V : Subgroup G) : Prop :=
  ∀ U ∈ sigmaSet M V, ∀ U' ∈ sigmaSet M V, U' ⊓ (U ⊔ Pc M V) ≠ ⊥ →
    ∃ p ∈ Pc M V, U' = conjSubgroup p U

@[expose] def Stmt55e (M V : Subgroup G) : Prop :=
  ∀ U ∈ sigmaSet M V, ∀ x ∈ U, x ≠ 1 → ∀ m ∈ M, (∃ p ∈ Pc M V, m * x * m⁻¹ = x * p) →
    ∃ p ∈ Pc M V, m * x * m⁻¹ = p * x * p⁻¹

@[expose] def Stmt56a (M V : Subgroup G) : Prop :=
  ∀ U ∈ sigmaSet M V, ∀ U' ∈ sigmaSet M V,
    ⁅Pc M V, U'⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (↑⁅Pc M V, U⁆ : Set G)) = V →
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (π : ↥(U ⊔ U') →* SL(2, F)),
      Function.Surjective π ∧ π.ker = (Pc M V).subgroupOf (U ⊔ U') ∧
        Nat.card F = Nat.card V ∧ (U.subgroupOf (U ⊔ U')).map π = utri F ∧
        (U'.subgroupOf (U ⊔ U')).map π = ltri F

@[expose] def Stmt56 (M V : Subgroup G) : Prop :=
  ∀ U ∈ sigmaSet M V, ∀ U' ∈ sigmaSet M V,
    ⁅Pc M V, U'⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (↑⁅Pc M V, U⁆ : Set G)) = V → IsL2Gen U U'

@[expose] def Stmt57 (M V : Subgroup G) : Prop :=
  ∀ U ∈ sigmaSet M V, ∀ U' ∈ sigmaSet M V,
    (⁅Pc M V, U⁆ ≤ Pc M V ⊓ Subgroup.centralizer (U' : Set G) ∧ ⁅U, U'⁆ = ⊥) ∨
    (⁅Pc M V, U⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (U' : Set G)) = V ∧ IsL2Gen U U') ∨
    (⁅Pc M V, U⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (U' : Set G)) ∈ fSet M V ∧
      IsPGroup 2 ↥(U ⊔ U') ∧ ⁅U, U'⁆ ≠ ⊥)

@[expose] def Stmt58 (M V : Subgroup G) : Prop :=
  ∀ g h : G, conjSubgroup h V ∈ sigmaSet M V → conjSubgroup g V ∈ sigmaSet M V →
    ⁅conjSubgroup g V, conjSubgroup h V⁆ = ⊥ →
    hOf M V g = hOf M V h ∨
      Pc M V = (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊔
        (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))

@[expose] def Stmt512 (M V : Subgroup G) : Prop :=
  ∀ g h : G, conjSubgroup h V ∈ sigmaSet M V → conjSubgroup g V ∈ sigmaSet M V →
    ⁅conjSubgroup g V, conjSubgroup h V⁆ = ⊥ → conjSubgroup g V ≠ conjSubgroup h V →
    IsHMember (conjSubgroup h M) (conjSubgroup h V)
      (conjSubgroup g (Pc M V) ⊔ conjSubgroup h (Pc M V))

@[expose] def Stmt513 (M V : Subgroup G) : Prop :=
  ∀ U ∈ sigmaSet M V, ∀ U' ∈ sigmaSet M V,
    (⁅U, U'⁆ = ⊥ ∧ ⁅Pc M V, U⁆ ≤ Pc M V ⊓ Subgroup.centralizer (U' : Set G)) ∨
    (IsL2Gen U U' ∧ Pc M V ⊓ Subgroup.centralizer (U' : Set G) ⊓ ⁅Pc M V, U⁆ = V)

@[expose] def StmtI5a (M V : Subgroup G) : Prop :=
  ∀ (H : Subgroup G) (h₀ y : G), Sec45Shape M V H h₀ → y ∈ H → conjSubgroup y V ≠ V →
    ∃ p ∈ Pc M V, conjSubgroup y V = conjSubgroup p (conjSubgroup h₀ V)

@[expose] def StmtI5b (M V : Subgroup G) : Prop :=
  ∀ (H : Subgroup G) (h₀ y d : G), Sec45Shape M V H h₀ → y ∈ H → conjSubgroup y V ≠ V →
    d ∈ V ⊔ conjSubgroup y V → d ∈ Tim78.classD V → d ∈ V ∨ d ∈ conjSubgroup y V

end CFSG.RankThree.GF2n.Tim81.Sec5
