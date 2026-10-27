module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.Walter.Ree

structure ThompsonIConditions {N : Type*} [Group N] (q : ℕ) (P R : Subgroup N) : Prop where
  sup_eq_top : P ⊔ R = ⊤
  normal : P.Normal
  card_P : Nat.card P = q ^ 3
  card_R : Nat.card R = q - 1
  isCyclic_R : IsCyclic R
  centralizer_eq_bot : ∀ r ∈ R, r ^ 2 ≠ 1 → P ⊓ Subgroup.centralizer {r} = ⊥
  card_commutator : Nat.card (⁅P, P⁆ : Subgroup N) = q ^ 2
  elementary_commutator : IsElementaryAbelian 3 (⁅P, P⁆ : Subgroup N)
  commutator_commutator : ⁅(⁅P, P⁆ : Subgroup N), P⁆ = (Subgroup.center P).map P.subtype
  card_center : Nat.card (Subgroup.center P) = q
  elementary_center : IsElementaryAbelian 3 (Subgroup.center P)
  commutator_eq_prod : ∀ J ∈ R, orderOf J = 2 →
    ⁅P, P⁆ = (P ⊓ Subgroup.centralizer {J}) ⊔ (Subgroup.center P).map P.subtype ∧
      (P ⊓ Subgroup.centralizer {J}) ⊓ (Subgroup.center P).map P.subtype = ⊥
  centralizer_of_mem_commutator : ∀ x ∈ ⁅P, P⁆, x ∉ (Subgroup.center P).map P.subtype →
    P ⊓ Subgroup.centralizer {x} = ⁅P, P⁆
  commutator_eq_omega : ⁅P, P⁆ = Subgroup.closure {x | x ∈ P ∧ x ^ 3 = 1}
  centralizer_of_notMem_commutator : ∀ x ∈ P, x ∉ ⁅P, P⁆ →
    P ⊓ Subgroup.centralizer {x} = Subgroup.zpowers x ⊔ (Subgroup.center P).map P.subtype

structure ThompsonIHyp (N : Type*) [Group N] [Finite N] (q : ℕ) : Prop where
  card : Nat.card N = q ^ 3 * (q - 1)
  exists_conditions : ∃ P R : Subgroup N, ThompsonIConditions q P R

end CFSG.Walter.Ree
