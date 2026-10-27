module

public import CFSG.Quasithin.Recognition.M12AscD5

public section

namespace CFSG.Quasithin

open Subgroup Equiv

open CFSG.GH74.M12 (Asc03Hyp)

variable {G : Type*} [Group G] {z : G}

theorem two_mul_card_dvd_of_normalizing {N K : Subgroup G} [Finite G] (hKN : K ≤ N) {z : G}
    (hzN : z ∈ N) (hzK : z ∉ K) (hz2 : z * z = 1) (hnorm : ∀ k ∈ K, z * k * z⁻¹ ∈ K) :
    2 * Nat.card K ∣ Nat.card N := by
  let M : Subgroup G := N ⊓ Subgroup.normalizer (K : Set G)
  have hKnorm : K ≤ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer
  have hKM : K ≤ M := le_inf hKN hKnorm
  have hzM : z ∈ M := ⟨hzN, Subgroup.mem_normalizer_fintype (fun n hn => hnorm n hn)⟩
  have hnormal : (K.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 inf_le_right
  let zq : ↥M ⧸ K.subgroupOf M := QuotientGroup.mk ⟨z, hzM⟩
  have hzq1 : zq ≠ 1 := by
    intro h
    have : (⟨z, hzM⟩ : ↥M) ∈ K.subgroupOf M := (QuotientGroup.eq_one_iff _).1 h
    exact hzK this
  have hzq2 : zq ^ 2 = 1 := by
    show (QuotientGroup.mk ⟨z, hzM⟩ : ↥M ⧸ K.subgroupOf M) ^ 2 = 1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have : (⟨z, hzM⟩ : ↥M) ^ 2 = 1 := by
      apply Subtype.ext
      simp [pow_two, hz2]
    rw [this]
    exact one_mem _
  have hord : orderOf zq = 2 := orderOf_eq_prime hzq2 hzq1
  have h2 : 2 ∣ Nat.card (↥M ⧸ K.subgroupOf M) := hord ▸ orderOf_dvd_natCard zq
  have hMcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (K.subgroupOf M)
  have hKcard : Nat.card (K.subgroupOf M) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
  have hMN : Nat.card M ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_left
  rw [hKcard] at hMcard
  have : 2 * Nat.card K ∣ Nat.card M := by
    rw [hMcard]
    exact Nat.mul_dvd_mul_right h2 _ |>.trans (by rw [mul_comm])
  exact this.trans hMN

@[expose] def basisList : List (Perm (Fin 6) × Perm (Fin 6)) :=
  (D6l ×ˢ D6l).filter fun p => p.1 ≠ 1 ∧ p.2 ∉ [1, p.1, p.1 * p.1]

theorem basisList_length : basisList.length = 48 := by decide +kernel

theorem basisList_nodup : basisList.Nodup := by decide +kernel

theorem mem_basisList {a b : Perm (Fin 6)} :
    (a, b) ∈ basisList ↔ a ∈ D6l ∧ b ∈ D6l ∧ a ≠ 1 ∧ b ∉ [1, a, a * a] := by
  simp only [basisList, List.mem_filter, List.mem_product, decide_eq_true_eq]
  tauto

namespace AscCox

variable {m : AscModel z} (c : AscCox m)

theorem card_N_dvd
    [Finite G] (h27 : 27 ∣ Nat.card G) {y : G} (h : OuterData c y) :
    432 ∣ Nat.card (Subgroup.normalizer (c.D : Set G)) := by
  have hz2 : z * z = 1 := c.z_sq
  have h27' : 27 ∣ Nat.card (Subgroup.normalizer (c.D : Set G)) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact Sylow.prime_pow_dvd_card_normalizer (p := 3) (n := 2) (by simpa using h27)
      (by simpa using c.card_D)
  have hK144 : 2 * Nat.card h.K ∣ Nat.card (Subgroup.normalizer (c.D : Set G)) := by
    refine two_mul_card_dvd_of_normalizing h.K_le_normalizer c.z_mem_N ?_ hz2 ?_
    · intro hzK
      exact h.z_notin_L (h.K_le_L hzK)
    · intro k hk
      have hzN := c.z_mem_N
      have hkN := h.K_le_normalizer hk
      exact ⟨h.z_normalizes_L (h.K_le_L hk),
        (Subgroup.normalizer (c.D : Set G)).mul_mem
          ((Subgroup.normalizer (c.D : Set G)).mul_mem hzN hkN)
          ((Subgroup.normalizer (c.D : Set G)).inv_mem hzN)⟩
  rw [h.K_card] at hK144
  omega

end AscCox

end CFSG.Quasithin
