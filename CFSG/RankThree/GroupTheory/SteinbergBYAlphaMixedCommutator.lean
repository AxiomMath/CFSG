module

public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
import Mathlib.Algebra.Group.Pointwise.Set.Card

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBY

open CFSG CFSG.RankThree.GroupTheory
open scoped Pointwise

variable {G : Type*} [Group G]

theorem mul_comm_of_isMulCommutative {A : Subgroup G} [IsMulCommutative A] {x y : G}
    (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x :=
  congrArg Subtype.val ((IsMulCommutative.is_comm (M := A)).comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem orderOf_eq_of_isElementaryAbelian {p : ℕ} (hp : p.Prime) {A : Subgroup G}
    [IsElementaryAbelian p A] {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) : orderOf a = p :=
  have : Fact p.Prime := ⟨hp⟩
  orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a ha) ha1

theorem card_zpowers_sup_zpowers {p : ℕ} (hp : p.Prime) {A : Subgroup G}
    [IsElementaryAbelian p A] (hAcard : Nat.card A = p ^ 3) {a x : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) (hx : x ∈ A) (hxa : x ∉ Subgroup.zpowers a) :
    Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers x : Subgroup G) = p ^ 2 := by
  have hx1 : x ≠ 1 := fun h => hxa (h ▸ one_mem _)
  have hoa := orderOf_eq_of_isElementaryAbelian hp ha ha1
  have hox := orderOf_eq_of_isElementaryAbelian hp hx hx1
  set S := Subgroup.zpowers a ⊔ Subgroup.zpowers x with hS
  have hSA : S ≤ A := sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hx)
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hAcard]; exact pow_ne_zero 3 hp.ne_zero)
  have : Finite S := Finite.of_injective (Subgroup.inclusion hSA) (Subgroup.inclusion_injective _)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp (hAcard ▸ Subgroup.card_dvd_of_le hSA)
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ ?_)
    rw [← centralizer_singleton_eq_centralizer_zpowers, Subgroup.mem_centralizer_singleton_iff]
    exact mul_comm_of_isMulCommutative hx ha
  have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle
  have hup : Nat.card S ≤ p ^ 2 := by
    have h := Set.natCard_mul_le (s := (Subgroup.zpowers a : Set G))
      (t := (Subgroup.zpowers x : Set G))
    rw [← hcoe] at h
    have h1 : Nat.card (Subgroup.zpowers a : Set G) = p := by
      change Nat.card (Subgroup.zpowers a) = p
      rw [Nat.card_zpowers, hoa]
    have h2 : Nat.card (Subgroup.zpowers x : Set G) = p := by
      change Nat.card (Subgroup.zpowers x) = p
      rw [Nat.card_zpowers, hox]
    rw [h1, h2] at h
    change Nat.card S ≤ _
    exact h.trans (le_of_eq (sq p).symm)
  have hlt : Subgroup.zpowers a < S :=
    lt_of_le_of_ne le_sup_left fun h => hxa (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hlow : p < Nat.card S := by
    have := Subgroup.card_lt_of_lt hlt
    rwa [Nat.card_zpowers, hoa] at this
  rw [hk] at hup hlow ⊢
  have hk2 : k ≤ 2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hup
  have hk1 : 1 < k := (Nat.pow_lt_pow_iff_right hp.one_lt).mp (by rwa [pow_one])
  rw [show k = 2 by omega]

theorem alpha_local_mixed_commutator_bound {p : ℕ} (hp : p.Prime) {A : Subgroup G}
    (hA : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 3)
    (hα : ∀ E : Subgroup G, E ≤ A → Nat.card E = p ^ 2 → ∀ c ∈ A, c ≠ 1 →
      (twoCoreAlpha (E.subgroupOf (Subgroup.centralizer ({c} : Set G)))).map
          (Subgroup.centralizer ({c} : Set G)).subtype ≤
        inSubgroup (pCore 2) (Subgroup.centralizer ({c} : Set G))) :
    ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 →
      ⁅inSubgroup (pCore 2) (Subgroup.centralizer ({a} : Set G)) ⊓
          Subgroup.centralizer ({b} : Set G), A⁆ ≤
        inSubgroup (pCore 2) (Subgroup.centralizer ({b} : Set G)) := by
  intro a ha ha1 b hb hb1
  have := hA
  set Ca := Subgroup.centralizer ({a} : Set G) with hCa
  set Cb := Subgroup.centralizer ({b} : Set G) with hCb
  have hACb : A ≤ Cb := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (mul_comm_of_isMulCommutative hx hb)
  have hT : inSubgroup (pCore 2) Ca ⊓ Cb ≤ inSubgroup (pCore 2) (Cb ⊓ Ca) := fun t ht =>
    inf_inSubgroup_pCore_le inf_le_right ⟨⟨ht.2, inSubgroup_pCore_le 2 Ca ht.1⟩, ht.1⟩
  rw [Subgroup.commutator_le]
  intro t ht x hx
  by_cases hxS : x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b
  ·
    have hta : a ∈ Subgroup.centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (inSubgroup_pCore_le 2 Ca ht.1)).symm
    have htb : b ∈ Subgroup.centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp ht.2).symm
    have hxt := (sup_le (Subgroup.zpowers_le.mpr hta) (Subgroup.zpowers_le.mpr htb)) hxS
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hxt).symm]
    exact one_mem _
  ·
    have hxa : x ∉ Subgroup.zpowers a := fun h => hxS (Subgroup.mem_sup_left h)
    set E := Subgroup.zpowers a ⊔ Subgroup.zpowers x with hE
    have hEA : E ≤ A := sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hx)
    have hEcard : Nat.card E = p ^ 2 := card_zpowers_sup_zpowers hp hAcard ha ha1 hx hxa
    have haE : (⟨a, hACb ha⟩ : Cb) ∈ E.subgroupOf Cb :=
      Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
    have ha1' : (⟨a, hACb ha⟩ : Cb) ≠ 1 := fun h =>
      ha1 (by simpa using congrArg Subtype.val h)
    have hJ := Subgroup.map_mono (f := Cb.subtype) (commutator_le_twoCoreJ haE ha1')
    rw [Subgroup.map_commutator, map_subtype_inSubgroup_pCore_centralizer,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hEA.trans hACb)] at hJ
    have hmem := hJ (Subgroup.commutator_mem_commutator (hT ht)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))
    exact hα E hEA hEcard b hb hb1
      (Subgroup.map_mono (twoCoreJ_le_twoCoreAlpha _) hmem)

end CFSG.RankThree.GroupTheory.SteinbergBY
