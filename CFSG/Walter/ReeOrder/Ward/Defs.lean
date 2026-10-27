module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.Walter.Ward

open scoped MatrixGroups

@[expose] def wardSign (q : ℕ) : ℤ := if q % 8 = 3 then -1 else 1

structure ReeTypeHyp (G : Type) [Group G] [Finite G] where
  p : ℕ
  f : ℕ
  [fact_prime : Fact p.Prime]
  p_ne_two : p ≠ 2
  f_pos : 0 < f
  card_sylow : ∀ P : Sylow 2 G, Nat.card P = 8
  elementary_sylow : ∀ P : Sylow 2 G, IsElementaryAbelian 2 P
  index_ne_two : ∀ N : Subgroup G, N.Normal → N.index ≠ 2
  J : G
  orderOf_J : orderOf J = 2
  L : Subgroup G
  le_centralizer : L ≤ Subgroup.centralizer ({J} : Set G)
  J_not_mem : J ∉ L
  centralizer_eq : Subgroup.centralizer ({J} : Set G) = Subgroup.zpowers J ⊔ L
  iso : L ≃* PSL(2, GaloisField p f)
  normalizer_le : ∀ R ∈ L, 2 * (orderOf R : ℤ) = p ^ f + wardSign (p ^ f) →
    ∀ R₀ ∈ Subgroup.zpowers R, R₀ ≠ 1 →
      Subgroup.normalizer (Subgroup.zpowers R₀ : Set G) ≤ Subgroup.centralizer ({J} : Set G)
  not_commute : ∀ J' ∈ L, orderOf J' = 2 →
    ∀ S ∈ L, 4 * (orderOf S : ℤ) = p ^ f - wardSign (p ^ f) → S * J' = J' * S →
      ∀ A : G, orderOf A = 3 →
        A ∈ Subgroup.normalizer (Subgroup.closure ({J, J'} : Set G) : Set G) → A * S ≠ S * A

attribute [instance] ReeTypeHyp.fact_prime

variable {G : Type} [Group G] [Finite G]

@[expose] def ReeTypeHyp.q (h : ReeTypeHyp G) : ℕ := h.p ^ h.f

@[expose] def ReeTypeHyp.e (h : ReeTypeHyp G) : ℤ := wardSign h.q

end CFSG.Walter.Ward
