module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Solvable

import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Quasithin.J4M2

namespace NormalTwoGroup

theorem index_subgroupOf_eq_of_card_eq_mul {G : Type*} [Group G] [Finite G] {K Q : Subgroup G}
    (hQK : Q ≤ K) {n : ℕ} (hcard : Nat.card K = n * Nat.card Q) :
    (Q.subgroupOf K).index = n := by
  have h := Subgroup.relIndex_mul_card (H := Q) (K := K)
  rw [inf_of_le_left hQK, hcard] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h

end NormalTwoGroup

theorem normalizes_of_mem_sup_zpowers {G : Type*} [Group G] [Finite G] (Q : Subgroup G) (c : G)
    (hc : ∀ x ∈ Q, c * x * c⁻¹ ∈ Q) :
    ∀ k ∈ Q ⊔ Subgroup.zpowers c, ∀ x ∈ Q, k * x * k⁻¹ ∈ Q := by
  have hmap : Q.map (MulAut.conj c).toMonoidHom = Q :=
    Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨x, hx, rfl⟩; exact hc x hx)
      (by rw [Subgroup.card_map_of_injective (MulAut.conj c).injective])
  have hcn : c ∈ Subgroup.normalizer (Q : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.2 hmap
  exact Subgroup.le_normalizer_iff.1
    (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hcn))

theorem conj_mem_of_normal_two_sylow {G : Type*} [Group G] [Finite G] (M K Q : Subgroup G)
    (hKn : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K) (hQK : Q ≤ K)
    (hQK' : ∀ k ∈ K, ∀ x ∈ Q, k * x * k⁻¹ ∈ Q) (hKcard : Nat.card K = 3 * 2 ^ 13)
    (hQcard : Nat.card Q = 2 ^ 13) : ∀ m ∈ M, ∀ x ∈ Q, m * x * m⁻¹ ∈ Q := by
  intro m hm x hx
  have := (Subgroup.normal_subgroupOf_iff hQK).2 fun x k hx hk => hQK' k hk x hx
  have hidx : (Q.subgroupOf K).index = 3 :=
    NormalTwoGroup.index_subgroupOf_eq_of_card_eq_mul hQK (by rw [hKcard, hQcard])
  have hyK : m * x * m⁻¹ ∈ K := hKn m hm x (hQK hx)
  have hx2 : x ^ 2 ^ 13 = 1 := by
    have h := pow_card_eq_one' (G := Q) (x := ⟨x, hx⟩)
    rw [hQcard] at h
    exact congrArg Subtype.val h
  have hy2 : (m * x * m⁻¹) ^ 2 ^ 13 = 1 := by
    rw [conj_pow, hx2]
    group
  have hy3 : (m * x * m⁻¹) ^ 3 ∈ Q := by
    have h := Subgroup.pow_index_mem (Q.subgroupOf K) (⟨m * x * m⁻¹, hyK⟩ : K)
    rw [hidx] at h
    exact Subgroup.mem_subgroupOf.1 h
  have hy : m * x * m⁻¹ = ((m * x * m⁻¹) ^ 3) ^ 2731 := by
    rw [← pow_mul, show 3 * 2731 = 2 ^ 13 + 1 by norm_num, pow_succ, hy2, one_mul]
  rw [hy]
  exact Q.pow_mem hy3 2731

theorem le_of_normal_two_group {G : Type*} [Group G] [Finite G] (M Q P0 : Subgroup G)
    (hP0M : P0 ≤ M) (hP0card : Nat.card P0 = 2 ^ 21) {m : ℕ} (hMcard : Nat.card M = 2 ^ 21 * m)
    (hm : ¬ 2 ∣ m) (hQM : Q ≤ M) (hQn : ∀ g ∈ M, ∀ x ∈ Q, g * x * g⁻¹ ∈ Q)
    (hQ2 : IsPGroup 2 ↥Q) : Q ≤ P0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfac : (Nat.card M).factorization 2 = 21 := by
    rw [hMcard, Nat.factorization_mul (by norm_num) (by rintro rfl; exact hm (dvd_zero 2)),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd hm]
    simp
  have hP0' : Nat.card (P0.subgroupOf M) = 2 ^ (Nat.card M).factorization 2 := by
    rw [hfac, ← hP0card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP0M).toEquiv
  let S : Sylow 2 M := Sylow.ofCard (P0.subgroupOf M) hP0'
  have hQ' : IsPGroup 2 (Q.subgroupOf M) := hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQM).symm
  have := (Subgroup.normal_subgroupOf_iff hQM).2 fun x g hx hg => hQn g hg x hx
  intro x hx
  have h : (⟨x, hQM hx⟩ : M) ∈ S := hQ'.le_sylow_of_normal S (Subgroup.mem_subgroupOf.2 hx)
  exact Subgroup.mem_subgroupOf.1 h

theorem isSolvable_of_normal_two_group {G : Type*} [Group G] [Finite G] (K Q : Subgroup G)
    (hQK : Q ≤ K) (hQK' : ∀ k ∈ K, ∀ x ∈ Q, k * x * k⁻¹ ∈ Q) (hKcard : Nat.card K = 3 * 2 ^ 13)
    (hQcard : Nat.card Q = 2 ^ 13) : Group.IsSolvable ↥K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := (Subgroup.normal_subgroupOf_iff hQK).2 fun x k hx hk => hQK' k hk x hx
  have hidx : (Q.subgroupOf K).index = 3 :=
    NormalTwoGroup.index_subgroupOf_eq_of_card_eq_mul hQK (by rw [hKcard, hQcard])
  have hNcard : Nat.card (Q.subgroupOf K) = 2 ^ 13 := by
    rw [← hQcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv
  have : Group.IsNilpotent (Q.subgroupOf K) := (IsPGroup.of_card hNcard).isNilpotent
  have : IsCyclic (K ⧸ Q.subgroupOf K) := isCyclic_of_prime_card (p := 3) hidx
  exact Group.isSolvable_of_subgroup_quotient (Q.subgroupOf K)

theorem commutator_eq_of_ker_le {G S : Type*} [Group G] [Group S] (M B0 K : Subgroup G)
    (ρ : ↥M →* S) (hB0M : B0 ≤ M) (hKρ : ∀ m : ↥M, ρ m = 1 ↔ (m : G) ∈ K)
    (hKC : K ≤ ⁅B0, B0⁆)
    (hA : ⁅(B0.subgroupOf M).map ρ, (B0.subgroupOf M).map ρ⁆ = (B0.subgroupOf M).map ρ) :
    ⁅B0, B0⁆ = B0 := by
  refine le_antisymm (Subgroup.commutator_le_self B0) fun x hx => ?_
  have hxB : (⟨x, hB0M hx⟩ : M) ∈ B0.subgroupOf M := hx
  have hρx : ρ ⟨x, hB0M hx⟩ ∈ ⁅(B0.subgroupOf M).map ρ, (B0.subgroupOf M).map ρ⁆ := by
    rw [hA]
    exact Subgroup.mem_map_of_mem ρ hxB
  rw [← Subgroup.map_commutator] at hρx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hρx
  have hyC : (y : G) ∈ ⁅B0, B0⁆ := by
    have h1 := Subgroup.mem_map_of_mem M.subtype hy
    rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hB0M] at h1
  have hker : ρ (y⁻¹ * ⟨x, hB0M hx⟩) = 1 := by
    rw [map_mul, map_inv, hyx, inv_mul_cancel]
  have hK : (y : G)⁻¹ * x ∈ K := (hKρ _).1 hker
  have h2 : x = (y : G) * ((y : G)⁻¹ * x) := by group
  rw [h2]
  exact ⁅B0, B0⁆.mul_mem hyC (hKC hK)

theorem mem_iff_of_map_eq {G S : Type*} [Group G] [Group S] (M B0 K : Subgroup G) (ρ : ↥M →* S)
    (A : Subgroup S) (hKρ : ∀ m : ↥M, ρ m = 1 ↔ (m : G) ∈ K) (hKB0 : K ≤ B0)
    (hmap : (B0.subgroupOf M).map ρ = A) : ∀ m : ↥M, (m : G) ∈ B0 ↔ ρ m ∈ A := by
  intro m
  constructor
  · intro hm
    rw [← hmap]
    exact Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.2 hm)
  · intro hm
    rw [← hmap] at hm
    obtain ⟨b, hb, hbm⟩ := Subgroup.mem_map.1 hm
    have hker : ρ (b⁻¹ * m) = 1 := by
      rw [map_mul, map_inv, hbm, inv_mul_cancel]
    have hK : (b : G)⁻¹ * m ∈ B0 := hKB0 ((hKρ _).1 hker)
    have h2 : (m : G) = (b : G) * ((b : G)⁻¹ * m) := by group
    rw [h2]
    exact B0.mul_mem (Subgroup.mem_subgroupOf.1 hb) hK

theorem card_eq_of_bounds {M S : Type*} [Group M] [Finite M] [Group S] (ρ : M →* S) {a b : ℕ}
    (ha : a ≤ Nat.card ρ.range) (hb : b ≤ Nat.card ρ.ker) (hM : Nat.card M = a * b) :
    Nat.card ρ.range = a ∧ Nat.card ρ.ker = b := by
  have h := Subgroup.card_ker_mul_card_range ρ
  have hpos : 0 < Nat.card M := Nat.card_pos
  rw [hM] at h hpos
  have ha0 : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at hpos)
  have hb0 : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hpos)
  have hr : Nat.card ρ.range = a := by
    refine le_antisymm ?_ ha
    by_contra hlt
    have h1 : a * b < Nat.card ρ.range * b := Nat.mul_lt_mul_of_pos_right (not_le.1 hlt) hb0
    have h2 : Nat.card ρ.range * b ≤ Nat.card ρ.range * Nat.card ρ.ker :=
      Nat.mul_le_mul_left _ hb
    linarith
  refine ⟨hr, ?_⟩
  rw [hr] at h
  exact Nat.eq_of_mul_eq_mul_left ha0 (by linarith)

theorem sup_eq_top_of_map_eq_range {M S : Type*} [Group M] [Group S] (ρ : M →* S) (Y : Subgroup M)
    (hY : Y.map ρ = ρ.range) : Y ⊔ ρ.ker = ⊤ := by
  refine eq_top_iff.2 fun m _ => ?_
  have hm : ρ m ∈ Y.map ρ := by rw [hY]; exact MonoidHom.mem_range.2 ⟨m, rfl⟩
  obtain ⟨y, hy, hym⟩ := Subgroup.mem_map.1 hm
  have hker : y⁻¹ * m ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hym, inv_mul_cancel]
  have h2 : m = y * (y⁻¹ * m) := by group
  rw [h2]
  exact Subgroup.mul_mem_sup hy hker

end CFSG.Quasithin.J4M2
