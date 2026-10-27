module

public import CFSG.Quasithin.MS93.S36Frat

public section

namespace CFSG.Quasithin.MS93.S36SP

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def ActsLike (M : Subgroup G) (t l : G) : Prop :=
  ∀ A B : Subgroup G, M ≤ Subgroup.normalizer (A : Set G) →
    M ≤ Subgroup.normalizer (B : Set G) → B ≤ A → A ≤ pCoreOf 2 M →
      ⁅A, pCoreOf 2 M⁆ ≤ B → ∀ a ∈ A, t * a * t⁻¹ * (l * a * l⁻¹)⁻¹ ∈ B

structure EndSide (M T L : Subgroup G) (k : ℕ) (φ : MulAut ↥T) (Y : Subgroup G) : Prop where
  crit : ¬ Z0q M T ≤ tImage φ (pCoreOf 2 M)
  crit' : ¬ tImage φ (Z0q M T) ≤ pCoreOf 2 M
  index : (tImage φ (pCoreOf 2 M)).relIndex (Z0q M T) = 2 ^ k
  inf_C : 2 ≤ k → Uq M T L ⊓ Zq M L ⊓ tImage φ (Uq M T L ⊓ Zq M L) = ⊥
  C_le : 2 ≤ k → tImage φ (Uq M T L ⊓ Zq M L) ≤ Uq M T L
  Y_ge : omegaOneCenterOf T ≤ Y
  Y_le : Y ≤ tImage φ (Z0q M T) ⊓ pCoreOf 2 M
  Y_comm : 2 ≤ k → ⁅Y, pCoreOf 2 M⁆ ≤ Uq M T L ⊓ Zq M L
  not_le : ¬ ⁅normalClosureIn M Y, L⁆ ≤ Z0q M T
  index_le : ∀ K : Subgroup G, K ≤ T → ⁅pCoreOf 2 M, K⁆ ≤ Z0q M T →
    (tImage φ (pCoreOf 2 M)).relIndex K ≤ (2 ^ k) ^ 3
  comm_le : ∀ K : Subgroup G, K ≤ T → Z0q M T ≤ K → ⁅pCoreOf 2 M, K⁆ ≤ Z0q M T →
    (2 ^ k) ^ 3 ≤ (tImage φ (pCoreOf 2 M)).relIndex K →
      ⁅pCoreOf 2 M, tImage φ (Z0q M T)⁆ ≤ ⁅K, tImage φ (Z0q M T)⁆
  key : 2 ≤ k → ∀ t ∈ tImage φ (pCoreOf 2 M), ∃ l ∈ L, ActsLike M t l
  two : k = 1 → ∃ K₁ : Subgroup G, ⁅Y, pCoreOf 2 M⁆ ≤ K₁ ∧ K₁ ≤ tImage φ (Uq M T L) ∧
    K₁ ≤ Subgroup.centralizer (M : Set G) ∧ K₁ ⊓ tImage φ (Uq M T L ⊓ Zq M L) = ⊥

structure EndCommon (M T L : Subgroup G) (k : ℕ) : Prop where
  sp4 : IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) k
  card_C : Nat.card ↥(Uq M T L ⊓ Zq M L) = 2 ^ k
  comm_Xq : ⁅Xq M, L⁆ ≤ Uq M T L

@[expose] def S36SpEnd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G), PUHyp M T L →
    ∀ (k : ℕ) (ψ : MulAut ↥T) (Yp Ym : Subgroup G), EndCommon M T L k →
      EndSide M T L k ψ Yp → EndSide M T L k ψ⁻¹ Ym → False

end CFSG.Quasithin.MS93.S36SP
