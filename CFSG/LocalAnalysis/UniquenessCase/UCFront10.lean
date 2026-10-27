module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open scoped Pointwise MatrixGroups

variable {G : Type} [Group G] [Finite G]

@[expose] def Hyp10 (T B : Subgroup G) : Prop :=
  CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ ∧ IsMulCommutative B ∧ Odd (Nat.card B) ∧ Permutes B T ∧
    ∀ p : ℕ, p.Prime → p ∣ Nat.card B → CFSG.Open.pRank p B ≤ 2

@[expose] def OpRes (p : ℕ) (X : Subgroup G) : Subgroup G :=
  Subgroup.closure {x : G | x ∈ X ∧ ¬ p ∣ orderOf x}

structure LieAutVocab10 where
  InducesField : ∀ {G : Type} [Group G], Subgroup G → G → Prop
  InducesGraphField : ∀ {G : Type} [Group G], Subgroup G → G → Prop
  IsFundamental : ∀ {G : Type} [Group G], Subgroup G → Subgroup G → Prop

@[expose] def IsReeType10 (X : Type) [Group X] (q : ℕ) : Prop :=
  (∃ n : ℕ, q = 3 ^ (2 * n + 1)) ∧ (∀ P : Sylow 2 X, IsMulCommutative (P : Subgroup X)) ∧
    ∃ t : X, orderOf t = 2 ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = q ∧
      Nonempty (↥(Subgroup.centralizer ({t} : Set X)) ≃* (Multiplicative (ZMod 2) × PSL(2, F)))

@[expose] def IsTits10 (X : Type) [Group X] : Prop :=
  LieModel X .Tits 0 2 1

@[expose] def IsJankoReeType10 (X : Type) [Group X] : Prop :=
  (∀ P : Sylow 2 X, Nat.card P = 8 ∧ ∀ x ∈ P, ∀ y ∈ P, x * y = y * x ∧ x ^ 2 = 1) ∧
    ∃ (J : X) (L : Subgroup X) (F : Type) (_ : Field F) (_ : Fintype F),
      orderOf J = 2 ∧ Odd (Fintype.card F) ∧ 3 < Fintype.card F ∧ J ∉ L ∧
      L ≤ Subgroup.centralizer ({J} : Set X) ∧
      Subgroup.centralizer ({J} : Set X) = Subgroup.zpowers J ⊔ L ∧ Nonempty (L ≃* PSL(2, F))

@[expose] def CartanActing10 (X T H : Subgroup G) : Prop :=
  H ≤ X ⊓ normalizer ((T ⊓ X : Subgroup G) : Set G) ∧ Odd (Nat.card H) ∧
    ∃ k : ℕ, (H.subgroupOf (X ⊓ normalizer ((T ⊓ X : Subgroup G) : Set G))).index = 2 ^ k

@[expose] def K101 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T B : Subgroup G), Hyp10 T B →
    (∃ n : ℕ, IsAlt ↥(genFittingFStar G) n) → IsPGroup 3 ↥B

@[expose] def K104 (V : LieAutVocab10) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T B : Subgroup G), Hyp10 T B →
    ∀ L : Subgroup G, L = genFittingFStar G → IsChev ↥L 2 → ¬ IsTits10 ↥L → ¬ 3 ∣ Nat.card B →
      (∀ b ∈ B, ¬ V.InducesField L b) →
      ∃ H : Subgroup G, CartanActing10 (B ⊔ L) T H ∧ B ≤ H

@[expose] def K105 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T B : Subgroup G), Hyp10 T B →
    (∃ s : TauCeti.SporadicName, IsSpor ↥(genFittingFStar G) s) →
      IsPGroup 3 ↥B ∨ (IsJ1 G ∧ Nat.card B = 7)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
