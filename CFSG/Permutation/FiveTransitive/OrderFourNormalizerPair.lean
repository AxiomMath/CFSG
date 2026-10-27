module

public import CFSG.Permutation.FiveTransitive.FourPointAutomorphismUnique
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Tactic.Group

public section

namespace CFSG

namespace FiveTransitive.OrderFourNormalizerPair

private theorem conjugation_ne_one
    {G : Type*} [Group G] (Q : Subgroup G) [Finite Q] (hQ : Nat.card Q = 4)
    (b : Subgroup.normalizer (Q : Set G))
    (hb : Nat.card ((Subgroup.centralizer ({b.val} : Set G)).subgroupOf Q) = 2) :
    Q.normalizerMonoidHom b ≠ 1 := by
  intro he
  have ht : (Subgroup.centralizer ({b.val} : Set G)).subgroupOf Q = ⊤ := by
    apply top_unique
    intro q _
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    have hh : b.val * q.val * b.val⁻¹ = q.val := by
      rw [← Q.normalizerMonoidHom_apply_apply_coe b q, he]
      rfl
    have hh' := congrArg (fun t : G => t * b.val) hh
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh'.symm
  rw [ht, Subgroup.card_top, hQ] at hb
  contradiction

private theorem conjugation_eq
    {G : Type*} [Group G] (Q : Subgroup G) [Finite Q] (hQ : Nat.card Q = 4)
    (a : Q) (ha : a ≠ 1) (b c : Subgroup.normalizer (Q : Set G))
    (hba : Commute b.val a.val) (hca : Commute c.val a.val)
    (hb : Nat.card ((Subgroup.centralizer ({b.val} : Set G)).subgroupOf Q) = 2)
    (hc : Nat.card ((Subgroup.centralizer ({c.val} : Set G)).subgroupOf Q) = 2) :
    Q.normalizerMonoidHom b = Q.normalizerMonoidHom c := by
  apply FourPointAutomorphismUnique.automorphism_unique hQ a ha _ _
    (conjugation_ne_one Q hQ b hb) (conjugation_ne_one Q hQ c hc)
  · apply Subtype.ext
    rw [Q.normalizerMonoidHom_apply_apply_coe, hba.eq]
    group
  · apply Subtype.ext
    rw [Q.normalizerMonoidHom_apply_apply_coe, hca.eq]
    group

private theorem mul_inv_mem_centralizer
    {G : Type*} [Group G] (Q : Subgroup G) [Finite Q] (hQ : Nat.card Q = 4)
    (a : Q) (ha : a ≠ 1) (b c : Subgroup.normalizer (Q : Set G))
    (hba : Commute b.val a.val) (hca : Commute c.val a.val)
    (hb : Nat.card ((Subgroup.centralizer ({b.val} : Set G)).subgroupOf Q) = 2)
    (hc : Nat.card ((Subgroup.centralizer ({c.val} : Set G)).subgroupOf Q) = 2) :
    b.val * c.val⁻¹ ∈ Subgroup.centralizer (Q : Set G) := by
  have he := conjugation_eq Q hQ a ha b c hba hca hb hc
  have hk : b * c⁻¹ ∈ Q.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
  rw [Q.normalizerMonoidHom_ker] at hk
  exact hk

theorem mul_mem_centralizer
    {G : Type*} [Group G] (Q : Subgroup G) [Finite Q] (hQ : Nat.card Q = 4)
    (a : Q) (ha : a ≠ 1) (b c : Subgroup.normalizer (Q : Set G))
    (hba : Commute b.val a.val) (hca : Commute c.val a.val)
    (hb : Nat.card ((Subgroup.centralizer ({b.val} : Set G)).subgroupOf Q) = 2)
    (hc : Nat.card ((Subgroup.centralizer ({c.val} : Set G)).subgroupOf Q) = 2)
    (hc2 : c.val * c.val = 1) :
    b.val * c.val ∈ Subgroup.centralizer (Q : Set G) := by
  have hi : c.val⁻¹ = c.val := inv_eq_of_mul_eq_one_left hc2
  simpa only [hi] using mul_inv_mem_centralizer Q hQ a ha b c hba hca hb hc

end FiveTransitive.OrderFourNormalizerPair

end CFSG
