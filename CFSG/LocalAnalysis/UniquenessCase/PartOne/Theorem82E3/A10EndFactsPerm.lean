module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndPerm
import CFSG.RankThree.PartTwo.Sec15.ThmDA10Core

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Perm

open Equiv Equiv.Perm Subgroup
open CFSG.GH74.Uniqueness.SU.SU13.TA.L10

private theorem not_mem_zpowers_of_ne {x z : Perm (Fin 10)} (h3 : x ^ 3 = 1)
    (hz1 : z ≠ 1) (hzx : z ≠ x) (hzx2 : z ≠ x ^ 2) : z ∉ zpowers x := by
  intro h
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
  rw [zpow_eq_zpow_emod' m h3] at hm
  have hm0 : m % ((3 : ℕ) : ℤ) = 0 ∨ m % ((3 : ℕ) : ℤ) = 1 ∨
      m % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hm0 with h0 | h1 | h2
  · rw [h0, zpow_zero] at hm
    exact hz1 hm.symm
  · rw [h1, zpow_one] at hm
    exact hzx hm.symm
  · rw [h2] at hm
    exact hzx2 hm.symm

private def HasBasis (x : Perm (Fin 10)) : Prop :=
  ∃ y ∈ atilde, ∃ z ∈ atilde, y.support.card = 3 ∧ Disjoint y.support x.support ∧
    (∀ u ∈ atilde, u ≠ 1 → Disjoint u.support x.support → u.support = y.support) ∧
    z.support = x.support ∧ z ∉ zpowers x ∧ (x * z).support.card = 3 ∧
    (∀ u ∈ atilde, u.support = x.support → u ∈ zpowers x ∨ u ∈ zpowers z) ∧
    atilde ≤ zpowers x ⊔ zpowers y ⊔ zpowers z

private abbrev IsBasis (x y z : Perm (Fin 10)) : Prop :=
  y.support.card = 3 ∧ Disjoint y.support x.support ∧
  (∀ i j k : Fin 3, toP i j k ≠ 1 → Disjoint (toP i j k).support x.support →
    (toP i j k).support = y.support) ∧
  z.support = x.support ∧ z ≠ 1 ∧ z ≠ x ∧ z ≠ x ^ 2 ∧
  (x * z).support.card = 3 ∧
  (∀ i j k : Fin 3, (toP i j k).support = x.support →
    toP i j k = 1 ∨ toP i j k = x ∨ toP i j k = x ^ 2 ∨
    toP i j k = z ∨ toP i j k = z ^ 2) ∧
  (∃ a b c : Fin 3, pa = x ^ (a : ℕ) * y ^ (b : ℕ) * z ^ (c : ℕ)) ∧
  (∃ a b c : Fin 3, pb = x ^ (a : ℕ) * y ^ (b : ℕ) * z ^ (c : ℕ)) ∧
  (∃ a b c : Fin 3, pc = x ^ (a : ℕ) * y ^ (b : ℕ) * z ^ (c : ℕ))

private theorem hasBasis_of_isBasis {x y z : Perm (Fin 10)}
    (hy : y ∈ atilde) (hz : z ∈ atilde) (hx3 : x ^ 3 = 1) (h : IsBasis x y z) :
    HasBasis x := by
  obtain ⟨hy3, hdis, huniq_d, hzs, hz1, hzx, hzx2, hxz3, huniq2_d, hpa, hpb, hpc⟩ := h
  have hznot : z ∉ zpowers x := not_mem_zpowers_of_ne hx3 hz1 hzx hzx2
  have huniq : ∀ u ∈ atilde, u ≠ 1 → Disjoint u.support x.support →
      u.support = y.support := by
    intro u hu hu1 hdu
    obtain ⟨i, j, k, rfl⟩ := mem_atilde_iff.mp hu
    exact huniq_d i j k hu1 hdu
  have huniq2 : ∀ u ∈ atilde, u.support = x.support →
      u ∈ zpowers x ∨ u ∈ zpowers z := by
    intro u hu huS
    obtain ⟨i, j, k, rfl⟩ := mem_atilde_iff.mp hu
    rcases huniq2_d i j k huS with h | h | h | h | h
    · rw [h]; exact Or.inl (Subgroup.one_mem _)
    · rw [h]; exact Or.inl (Subgroup.mem_zpowers x)
    · rw [h]; exact Or.inl (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 2)
    · rw [h]; exact Or.inr (Subgroup.mem_zpowers z)
    · rw [h]; exact Or.inr (Subgroup.pow_mem _ (Subgroup.mem_zpowers z) 2)
  have hgen : atilde ≤ zpowers x ⊔ zpowers y ⊔ zpowers z := by
    let H : Subgroup (Perm (Fin 10)) := zpowers x ⊔ zpowers y ⊔ zpowers z
    have mem_prod : ∀ a b c : Fin 3,
        x ^ (a : ℕ) * y ^ (b : ℕ) * z ^ (c : ℕ) ∈ H := by
      intro a b c
      exact Subgroup.mul_mem _
        (Subgroup.mul_mem _
          (Subgroup.pow_mem _ (Subgroup.mem_sup_left
            (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))) a)
          (Subgroup.pow_mem _ (Subgroup.mem_sup_left
            (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))) b))
        (Subgroup.pow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers z)) c)
    rw [atilde, Subgroup.closure_le]
    intro w hw
    change w ∈ H
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · obtain ⟨a, b, c, hw⟩ := hpa
      rw [hw]; exact mem_prod a b c
    · obtain ⟨a, b, c, hw⟩ := hpb
      rw [hw]; exact mem_prod a b c
    · obtain ⟨a, b, c, hw⟩ := hpc
      rw [hw]; exact mem_prod a b c
  unfold HasBasis
  exact ⟨y, hy, z, hz, hy3, hdis, huniq, hzs, hznot, hxz3, huniq2, hgen⟩

private theorem isBasis_ab (i j : Fin 3) (hi : i ≠ 0) (hj : j ≠ 0) :
    IsBasis (toP i j 0) (toP 0 0 1) (toP i (j + j) 0) := by
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hi
      | exact absurd rfl hj
      | decide +kernel

private theorem exists_basis_ab (i j : Fin 3) (hi : i ≠ 0) (hj : j ≠ 0) :
    HasBasis (toP i j 0) :=
  hasBasis_of_isBasis (mem_atilde_iff.mpr ⟨0, 0, 1, rfl⟩)
    (mem_atilde_iff.mpr ⟨i, j + j, 0, rfl⟩)
    (CFSG.RankThree.PartTwo.Sec15.ThmD.toP_pow_three i j 0) (isBasis_ab i j hi hj)

private theorem isBasis_ac (i k : Fin 3) (hi : i ≠ 0) (hk : k ≠ 0) :
    IsBasis (toP i 0 k) (toP 0 1 0) (toP i 0 (k + k)) := by
  fin_cases i <;> fin_cases k <;>
    first
      | exact absurd rfl hi
      | exact absurd rfl hk
      | decide +kernel

private theorem exists_basis_ac (i k : Fin 3) (hi : i ≠ 0) (hk : k ≠ 0) :
    HasBasis (toP i 0 k) :=
  hasBasis_of_isBasis (mem_atilde_iff.mpr ⟨0, 1, 0, rfl⟩)
    (mem_atilde_iff.mpr ⟨i, 0, k + k, rfl⟩)
    (CFSG.RankThree.PartTwo.Sec15.ThmD.toP_pow_three i 0 k) (isBasis_ac i k hi hk)

private theorem isBasis_bc (j k : Fin 3) (hj : j ≠ 0) (hk : k ≠ 0) :
    IsBasis (toP 0 j k) (toP 1 0 0) (toP 0 j (k + k)) := by
  fin_cases j <;> fin_cases k <;>
    first
      | exact absurd rfl hj
      | exact absurd rfl hk
      | decide +kernel

private theorem exists_basis_bc (j k : Fin 3) (hj : j ≠ 0) (hk : k ≠ 0) :
    HasBasis (toP 0 j k) :=
  hasBasis_of_isBasis (mem_atilde_iff.mpr ⟨1, 0, 0, rfl⟩)
    (mem_atilde_iff.mpr ⟨0, j, k + k, rfl⟩)
    (CFSG.RankThree.PartTwo.Sec15.ThmD.toP_pow_three 0 j k) (isBasis_bc j k hj hk)

theorem exists_basis_of_card_support_eq_six {x : Perm (Fin 10)} (hx : x ∈ atilde)
    (h6 : x.support.card = 6) :
    ∃ y ∈ atilde, ∃ z ∈ atilde, y.support.card = 3 ∧ Disjoint y.support x.support ∧
      (∀ u ∈ atilde, u ≠ 1 → Disjoint u.support x.support → u.support = y.support) ∧
      z.support = x.support ∧ z ∉ zpowers x ∧ (x * z).support.card = 3 ∧
      (∀ u ∈ atilde, u.support = x.support → u ∈ zpowers x ∨ u ∈ zpowers z) ∧
      atilde ≤ zpowers x ⊔ zpowers y ⊔ zpowers z := by
  obtain ⟨i, j, k, rfl⟩ := mem_atilde_iff.mp hx
  change HasBasis (toP i j k)
  fin_cases k
  · fin_cases i
    · exfalso
      fin_cases j <;> revert h6 <;> decide +kernel
    · by_cases hj : j = 0
      · subst j; exfalso; revert h6; decide +kernel
      · exact exists_basis_ab 1 j (by decide +kernel) hj
    · by_cases hj : j = 0
      · subst j; exfalso; revert h6; decide +kernel
      · exact exists_basis_ab 2 j (by decide +kernel) hj
  · fin_cases i
    · by_cases hj : j = 0
      · subst j; exfalso; revert h6; decide +kernel
      · exact exists_basis_bc j 1 hj (by decide +kernel)
    · by_cases hj : j = 0
      · subst j; exact exists_basis_ac 1 1 (by decide +kernel) (by decide +kernel)
      · exfalso
        fin_cases j <;> first | exact absurd rfl hj | (revert h6; decide +kernel)
    · by_cases hj : j = 0
      · subst j; exact exists_basis_ac 2 1 (by decide +kernel) (by decide +kernel)
      · exfalso
        fin_cases j <;> first | exact absurd rfl hj | (revert h6; decide +kernel)
  · fin_cases i
    · by_cases hj : j = 0
      · subst j; exfalso; revert h6; decide +kernel
      · exact exists_basis_bc j 2 hj (by decide +kernel)
    · by_cases hj : j = 0
      · subst j; exact exists_basis_ac 1 2 (by decide +kernel) (by decide +kernel)
      · exfalso
        fin_cases j <;> first | exact absurd rfl hj | (revert h6; decide +kernel)
    · by_cases hj : j = 0
      · subst j; exact exists_basis_ac 2 2 (by decide +kernel) (by decide +kernel)
      · exfalso
        fin_cases j <;> first | exact absurd rfl hj | (revert h6; decide +kernel)

theorem support_eq_of_disjoint {x u v : Perm (Fin 10)} (hx : x ∈ atilde)
    (h6 : x.support.card = 6) (hu : u ∈ atilde) (hu1 : u ≠ 1)
    (hux : Disjoint u.support x.support) (hv : v ∈ atilde) (hv1 : v ≠ 1)
    (hvx : Disjoint v.support x.support) : v.support = u.support := by
  obtain ⟨y, hy, z, hz, hy3, hdis, huniq, hzs, hznot, hxz3, huniq2, hsup⟩ :=
    exists_basis_of_card_support_eq_six hx h6
  rw [huniq u hu hu1 hux, huniq v hv hv1 hvx]

theorem mem_zpowers_of_support_eq_of_not_mem {x u v : Perm (Fin 10)} (hx : x ∈ atilde)
    (h6 : x.support.card = 6) (hu : u ∈ atilde) (hux : u.support = x.support)
    (hu' : u ∉ zpowers x) (hv : v ∈ atilde) (hvx : v.support = x.support)
    (hv' : v ∉ zpowers x) : v ∈ zpowers u := by
  obtain ⟨y, hy, z, hz, hy3, hdis, huniq, hzs, hznot, hxz3, huniq2, hsup⟩ :=
    exists_basis_of_card_support_eq_six hx h6
  have hu_z : u ∈ zpowers z := (huniq2 u hu hux).resolve_left hu'
  have hv_z : v ∈ zpowers z := (huniq2 v hv hvx).resolve_left hv'
  have hu1 : u ≠ 1 := fun h => hu' (h ▸ Subgroup.one_mem (zpowers x))
  have hz1 : z ≠ 1 := fun h => hznot (h ▸ Subgroup.one_mem (zpowers x))
  have hu3 : u ^ 3 = 1 := by
    obtain ⟨i, j, k, rfl⟩ := mem_atilde_iff.mp hu
    exact CFSG.RankThree.PartTwo.Sec15.ThmD.toP_pow_three i j k
  have hz3 : z ^ 3 = 1 := by
    obtain ⟨i, j, k, rfl⟩ := mem_atilde_iff.mp hz
    exact CFSG.RankThree.PartTwo.Sec15.ThmD.toP_pow_three i j k
  have hord : orderOf u = orderOf z := by
    rw [orderOf_eq_prime (hp := ⟨Nat.prime_three⟩) hu3 hu1,
      orderOf_eq_prime (hp := ⟨Nat.prime_three⟩) hz3 hz1]
  have heq : zpowers u = zpowers z := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hu_z)
    rw [Nat.card_zpowers, Nat.card_zpowers, hord]
  rwa [← heq] at hv_z

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Perm
