module

public import CFSG.Walter.Defs

public section

namespace CFSG.Walter.JT

open scoped MatrixGroups

structure JTHyp (G : Type) [Group G] [Finite G] where
  p : ℕ
  f : ℕ
  [fact_prime : Fact p.Prime]
  five_lt : 5 < p ^ f
  abelian_sylow : HasAbelianSylowTwo G
  index_ne_two : ∀ H : Subgroup G, H.index ≠ 2
  t : G
  orderOf_t : orderOf t = 2
  F : Subgroup G
  le_centralizer : F ≤ Subgroup.centralizer ({t} : Set G)
  t_not_mem : t ∉ F
  centralizer_eq : Subgroup.centralizer ({t} : Set G) = Subgroup.zpowers t ⊔ F
  iso : F ≃* PSL(2, GaloisField p f)

attribute [instance] JTHyp.fact_prime

variable {G : Type} [Group G] [Finite G]

@[expose] def JTHyp.q (h : JTHyp G) : ℕ := h.p ^ h.f

@[expose] def JTHyp.eps (h : JTHyp G) : ℤ := if h.q % 4 = 3 then 1 else -1

@[expose] def IsTwoSignalizer {X : Type*} [Group X] (K : Subgroup X) : Prop :=
  Odd (Nat.card K) ∧ ∃ S : Sylow 2 X, (S : Subgroup X) ≤ Subgroup.normalizer (K : Set X)

@[expose] def IsInternalDirectProduct {X : Type*} [Group X] (A B H : Subgroup X) : Prop :=
  A ⊔ B = H ∧ Disjoint A B ∧ A ≤ Subgroup.centralizer (B : Set X)

end CFSG.Walter.JT
