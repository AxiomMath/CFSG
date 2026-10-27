module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.StandardType

variable {A : Type*} [Group A] [Finite A]

omit [Finite A] in
theorem ggSix_pow_relIndex_mem {K I : Subgroup A} [K.Normal] {d : A} (hd : d ∈ I) :
    d ^ K.relIndex I ∈ K := by
  have h : ((⟨d, hd⟩ : I) : I ⧸ K.subgroupOf I) ^ K.relIndex I = 1 := by
    change _ ^ Nat.card (I ⧸ K.subgroupOf I) = 1
    exact pow_card_eq_one'
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
  simpa using h

omit [Finite A] in
theorem ggSix_mem_of_sq_mem_of_odd_relIndex {K I : Subgroup A} [K.Normal]
    (hodd : Odd (K.relIndex I)) {x : A} (hxI : x ∈ I) (hx2 : x ^ 2 ∈ K) : x ∈ K := by
  obtain ⟨j, hj⟩ := hodd
  have hm := ggSix_pow_relIndex_mem (K := K) hxI
  rw [hj] at hm
  have hx : x = ((x ^ 2) ^ j)⁻¹ * x ^ (2 * j + 1) := by
    rw [← pow_mul, pow_succ]
    group
  rw [hx]
  exact K.mul_mem (K.inv_mem (K.pow_mem hx2 j)) hm

theorem ggSix_exists_conj_involution_of_even {K I C X : Subgroup A} [K.Normal] (hI : I.Normal)
    (hKI : K ≤ I) (hodd : Odd (K.relIndex I)) (hIC : ∀ a : A, ∃ i ∈ I, ∃ c ∈ C, a = i * c)
    (hIC' : I ⊓ C = ⊥) (hKX : K ≤ X) (heven : Even (K.relIndex X)) :
    ∃ s ∈ X, orderOf s = 2 ∧ s ∉ I ∧ ∃ e ∈ I, ∃ c ∈ C, c ^ 2 = 1 ∧ s = e * c * e⁻¹ := by
  obtain ⟨x, hxX, hxK, hx2⟩ : ∃ x ∈ X, x ∉ K ∧ x ^ 2 ∈ K := by
    have h2 : 2 ∣ Nat.card (X ⧸ K.subgroupOf X) := even_iff_two_dvd.mp heven
    obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 2 h2
    obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨x₀, x₀.2, ?_, ?_⟩
    · intro hx₀
      have h1 : ((x₀ : X) : X ⧸ K.subgroupOf X) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hx₀)
      rw [h1, orderOf_one] at hq
      exact absurd hq (by norm_num)
    · have h1 : ((x₀ : X) : X ⧸ K.subgroupOf X) ^ 2 = 1 := hq ▸ pow_orderOf_eq_one _
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
      simpa using h1
  have hxI : x ∉ I := fun hxI => hxK (ggSix_mem_of_sq_mem_of_odd_relIndex hodd hxI hx2)
  obtain ⟨d, hd, c, hc, rfl⟩ := hIC x
  have hcI : c ^ 2 ∈ I := by
    have hdc : d * (c * d * c⁻¹) ∈ I := I.mul_mem hd (hI.conj_mem d hd c)
    have h := I.mul_mem (I.inv_mem hdc) (hKI hx2)
    have heq : (d * (c * d * c⁻¹))⁻¹ * (d * c) ^ 2 = c ^ 2 := by
      rw [pow_two, pow_two]
      group
    rwa [heq] at h
  have hc2 : c ^ 2 = 1 := by
    have h : c ^ 2 ∈ I ⊓ C := ⟨hcI, C.pow_mem hc 2⟩
    rwa [hIC', Subgroup.mem_bot] at h
  obtain ⟨j, hj⟩ := hodd
  set e := d ^ (j + 1) with he
  have heI : e ∈ I := I.pow_mem hd _
  set π := QuotientGroup.mk' K
  have hγ : π c * π c = 1 := by rw [← map_mul, ← pow_two, hc2, map_one]
  have hγinv : (π c)⁻¹ = π c := inv_eq_of_mul_eq_one_right hγ
  have hδγ : π d * π c * (π d * π c) = 1 := by
    rw [← map_mul, ← map_mul, ← pow_two]
    exact (QuotientGroup.eq_one_iff _).mpr hx2
  have hconj : π c * π d * (π c)⁻¹ = (π d)⁻¹ := by
    rw [hγinv]
    calc π c * π d * π c = (π d)⁻¹ * (π d * π c * (π d * π c)) := by group
      _ = (π d)⁻¹ := by rw [hδγ, mul_one]
  have hδm : π d ^ (2 * j + 1) = 1 := by
    rw [← map_pow, ← hj]
    exact (QuotientGroup.eq_one_iff _).mpr (ggSix_pow_relIndex_mem hd)
  have hcomm : π c * (π d ^ (j + 1))⁻¹ = π d ^ (j + 1) * π c := by
    have h1 : π c * π d ^ (j + 1) * (π c)⁻¹ = (π d ^ (j + 1))⁻¹ := by
      rw [← conj_pow, hconj, inv_pow]
    calc π c * (π d ^ (j + 1))⁻¹
        = (π c * π d ^ (j + 1) * (π c)⁻¹)⁻¹ * π c := by group
      _ = π d ^ (j + 1) * π c := by rw [h1, inv_inv]
  have hπs : π (e * c * e⁻¹) = π (d * c) := by
    rw [he, map_mul, map_mul, map_inv, map_pow, map_mul, mul_assoc, hcomm, ← mul_assoc,
      ← pow_add]
    have hpow : π d ^ (j + 1 + (j + 1)) = π d := by
      rw [show j + 1 + (j + 1) = (2 * j + 1) + 1 by ring, pow_succ, hδm, one_mul]
    rw [hpow]
  have hsX : e * c * e⁻¹ ∈ X := by
    have hk : (e * c * e⁻¹) * (d * c)⁻¹ ∈ K := by
      rw [← QuotientGroup.eq_one_iff (N := K)]
      change π ((e * c * e⁻¹) * (d * c)⁻¹) = 1
      rw [map_mul, map_inv, hπs, mul_inv_cancel]
    have := X.mul_mem (hKX hk) hxX
    rwa [inv_mul_cancel_right] at this
  have hsI : e * c * e⁻¹ ∉ I := by
    intro hs
    have hcI' : c ∈ I := by
      have := I.mul_mem (I.mul_mem (I.inv_mem heI) hs) heI
      simpa [mul_assoc] using this
    have hc1 : c ∈ I ⊓ C := ⟨hcI', hc⟩
    rw [hIC', Subgroup.mem_bot] at hc1
    rw [hc1, mul_one] at hxI
    exact hxI hd
  refine ⟨e * c * e⁻¹, hsX, ?_, hsI, e, heI, c, hc, hc2, rfl⟩
  apply orderOf_eq_prime
  · rw [pow_two]
    calc e * c * e⁻¹ * (e * c * e⁻¹) = e * (c * c) * e⁻¹ := by group
      _ = 1 := by rw [← pow_two, hc2, mul_one, mul_inv_cancel]
  · intro h1
    exact hsI (h1 ▸ I.one_mem)

end CFSG.StandardType
