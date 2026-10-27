module

public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin.H13.T614.FStruct

open scoped Pointwise

theorem fstruct614 {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : G}
    (hdN : d ∈ Subgroup.normalizer (A : Set G)) (hd3 : d ^ 3 = 1) (hdA : d ∉ A) :
    (∀ f ∈ A ⊔ Subgroup.zpowers d, ∃ a ∈ A, ∃ i : ℕ, i < 3 ∧ f = a * d ^ i) ∧
    Nat.card ↥(A ⊔ Subgroup.zpowers d) = 3 * Nat.card ↥A ∧
    (∀ f ∈ A ⊔ Subgroup.zpowers d, ∀ g ∈ A ⊔ Subgroup.zpowers d, f * g * (g * f)⁻¹ ∈ A) ∧
    (∀ f ∈ A ⊔ Subgroup.zpowers d, f ^ 3 ∈ A) := by
  have hzN : Subgroup.zpowers d ≤ Subgroup.normalizer (A : Set G) :=
    Subgroup.zpowers_le.mpr hdN
  have hconj : ∀ z ∈ Subgroup.zpowers d, ∀ x ∈ A, z * x * z⁻¹ ∈ A :=
    fun z hz x hx => (Subgroup.mem_normalizer_iff.mp (hzN hz) x).mp hx
  have hdec : ∀ f ∈ A ⊔ Subgroup.zpowers d, ∃ a ∈ A, ∃ k : ℤ, f = a * d ^ k := by
    intro f hf
    have hf' : f ∈ (A : Set G) * (Subgroup.zpowers d : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A (Subgroup.zpowers d) hzN]
      exact hf
    obtain ⟨a, ha, z, hz, haz⟩ := Set.mem_mul.mp hf'
    have hz' : z ∈ Subgroup.zpowers d := hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz'
    exact ⟨a, ha, k, by rw [hk, haz]⟩
  have hred : ∀ k : ℤ, ∃ i : ℕ, i < 3 ∧ d ^ k = d ^ i := by
    intro k
    have hk : d ^ k = d ^ (k % ((3 : ℕ) : ℤ)) := zpow_eq_zpow_emod' k hd3
    have h0 : 0 ≤ k % ((3 : ℕ) : ℤ) := by omega
    have h3 : k % ((3 : ℕ) : ℤ) < 3 := by omega
    obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le h0
    exact ⟨i, by omega, by rw [hk, hi, zpow_natCast]⟩
  have part1 : ∀ f ∈ A ⊔ Subgroup.zpowers d, ∃ a ∈ A, ∃ i : ℕ, i < 3 ∧ f = a * d ^ i := by
    intro f hf
    obtain ⟨a, ha, k, rfl⟩ := hdec f hf
    obtain ⟨i, hi, hk⟩ := hred k
    exact ⟨a, ha, i, hi, by rw [hk]⟩
  have hd1 : d ≠ 1 := fun h => hdA (by rw [h]; exact A.one_mem)
  have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have e4 : (d ^ 2) ^ 2 = d := by
    calc (d ^ 2) ^ 2 = d ^ 3 * d := by group
      _ = d := by rw [hd3, one_mul]
  have hAz : A ⊓ Subgroup.zpowers d = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxA, hxz⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxz
    obtain ⟨i, hi, hki⟩ := hred k
    rw [← hk, hki] at hxA
    rw [Subgroup.mem_bot, ← hk, hki]
    interval_cases i
    · simp
    · exact (hdA (by simpa using hxA)).elim
    · exact (hdA (by rw [← e4]; exact A.pow_mem hxA 2)).elim
  have hrel3 : A.relIndex (Subgroup.zpowers d) = 3 := by
    have h := Subgroup.relIndex_mul_card A (Subgroup.zpowers d)
    rw [hAz, Subgroup.card_bot, Nat.card_zpowers, hord, mul_one] at h
    exact h
  have hsup : A.relIndex (A ⊔ Subgroup.zpowers d) = 3 := by
    rw [sup_comm]
    exact (CFSG.Quasithin.B6.relIndex_sup_eq_of_le_normalizer hzN).trans hrel3
  have hinf : A ⊓ (A ⊔ Subgroup.zpowers d) = A := inf_eq_left.mpr le_sup_left
  have hcard : A.relIndex (A ⊔ Subgroup.zpowers d) * Nat.card ↥(A ⊓ (A ⊔ Subgroup.zpowers d)) =
      Nat.card ↥(A ⊔ Subgroup.zpowers d) :=
    Subgroup.relIndex_mul_card A (A ⊔ Subgroup.zpowers d)
  rw [hsup, hinf] at hcard
  have hcomm : ∀ f ∈ A ⊔ Subgroup.zpowers d, ∀ g ∈ A ⊔ Subgroup.zpowers d,
      f * g * (g * f)⁻¹ ∈ A := by
    intro f hf g hg
    obtain ⟨a, ha, m, rfl⟩ := hdec f hf
    obtain ⟨b, hb, n, rfl⟩ := hdec g hg
    have e : a * d ^ m * (b * d ^ n) * (b * d ^ n * (a * d ^ m))⁻¹
        = a * (d ^ m * b * (d ^ m)⁻¹) * (d ^ n * a * (d ^ n)⁻¹)⁻¹ * b⁻¹ := by
      group
    rw [e]
    have h1 : d ^ m * b * (d ^ m)⁻¹ ∈ A :=
      hconj (d ^ m) (Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩) b hb
    have h2 : d ^ n * a * (d ^ n)⁻¹ ∈ A :=
      hconj (d ^ n) (Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩) a ha
    exact A.mul_mem (A.mul_mem (A.mul_mem ha h1) (A.inv_mem h2)) (A.inv_mem hb)
  have hcube : ∀ f ∈ A ⊔ Subgroup.zpowers d, f ^ 3 ∈ A := by
    intro f hf
    obtain ⟨a, ha, m, rfl⟩ := hdec f hf
    obtain ⟨i, -, hm⟩ := hred m
    rw [hm]
    have hdi : d ^ i ∈ Subgroup.zpowers d := Subgroup.pow_mem _ (Subgroup.mem_zpowers d) i
    have h3 : (d ^ i) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hd3, one_pow]
    have e : (a * d ^ i) ^ 3
        = a * (d ^ i * a * (d ^ i)⁻¹) * ((d ^ i) ^ 2 * a * ((d ^ i) ^ 2)⁻¹) * (d ^ i) ^ 3 := by
      rw [pow_three (a * d ^ i)]
      group
    rw [e, h3, mul_one]
    have h1 : d ^ i * a * (d ^ i)⁻¹ ∈ A := hconj (d ^ i) hdi a ha
    have h2 : (d ^ i) ^ 2 * a * ((d ^ i) ^ 2)⁻¹ ∈ A :=
      hconj ((d ^ i) ^ 2) (Subgroup.pow_mem _ hdi 2) a ha
    exact A.mul_mem (A.mul_mem ha h1) h2
  exact ⟨part1, hcard.symm, hcomm, hcube⟩

end CFSG.Quasithin.H13.T614.FStruct

end
