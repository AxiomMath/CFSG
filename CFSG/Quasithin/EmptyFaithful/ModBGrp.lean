module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.ModB

theorem central_mem_of_card_nine {A : Type*} [Group A] [Finite A] (hA : Nat.card A = 72)
    (P : Subgroup A) (hP : Nat.card P = 9) (ζ : A) (hζ : ∀ a : A, ζ * a = a * ζ) (hζ3 : ζ ^ 3 = 1) :
    ζ ∈ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf : (Nat.card A).factorization 3 = 2 := by
    rw [hA]; decide +kernel
  let S : Sylow 3 A := Sylow.ofCard P (by rw [hP, hf]; norm_num)
  have hZn : (Subgroup.zpowers ζ).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have : g * ζ ^ m * g⁻¹ = ζ ^ m := by
      have hc : Commute g (ζ ^ m) := ((Commute.symm (hζ g)) : Commute g ζ).zpow_right m
      rw [hc.eq, mul_inv_cancel_right]
    rw [this]
    exact Subgroup.zpow_mem_zpowers ζ m
  have hZp : IsPGroup 3 (Subgroup.zpowers ζ) := by
    intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [hζ3]
  have := IsPGroup.le_sylow_of_normal hZp S
  exact this (Subgroup.mem_zpowers ζ)


theorem exists_mem_of_central_image {K' : Type*} [Group K'] [Finite K'] {Γ : Type*} [Group Γ]
    (ρ : K' →* Γ) (N M' Y' : Subgroup K') (hN2 : IsPGroup 2 N) (hker : ρ.ker = N)
    (hNM : N ≤ M') (hM15 : M'.index = 15) (hN1080 : N.index = 1080) (hYM : Y' ≤ M')
    (h9 : 9 ∣ Nat.card Y') (z : K') (hz : z ∈ M') (hz3 : ρ z ^ 3 = 1)
    (hzc : ∀ k ∈ M', ρ z * ρ k = ρ k * ρ z) : ∃ y ∈ Y', ρ y = ρ z := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAcard : Nat.card (M'.map ρ) = 72 := by
    have h1 : Nat.card (M'.map ρ) = ρ.ker.relIndex M' := (Subgroup.relIndex_ker M' ρ).symm
    rw [hker] at h1
    have h2 := Subgroup.relIndex_mul_index hNM
    rw [hM15, hN1080] at h2
    omega
  obtain ⟨P0, hP0⟩ := Sylow.exists_subgroup_card_pow_prime (G := Y') 3 (n := 2) (by simpa using h9)
  let P : Subgroup K' := P0.map Y'.subtype
  have hPY : P ≤ Y' := Subgroup.map_subtype_le P0
  have hPcard : Nat.card P = 9 := by
    rw [Subgroup.card_map_of_injective Y'.subtype_injective, hP0]
    norm_num
  have hinj : Function.Injective (ρ.comp P.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
    have hxN : (x : K') ∈ N := by
      rw [← hker]
      exact hx
    obtain ⟨k, hk⟩ := hN2 ⟨(x : K'), hxN⟩
    have hk' : (x : K') ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have h9' : (x : K') ^ 9 = 1 := by
      have := pow_card_eq_one' (G := P) (x := x)
      rw [hPcard] at this
      simpa using congrArg Subtype.val this
    have hd1 : orderOf (x : K') ∣ 9 := orderOf_dvd_of_pow_eq_one h9'
    have hd2 : orderOf (x : K') ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hc : Nat.Coprime 9 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    have := Nat.dvd_gcd hd1 hd2
    rw [hc.gcd_eq_one] at this
    have hx1 : (x : K') = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)
    exact (Subgroup.mem_bot).2 (Subtype.ext hx1)
  have hPA : Nat.card (P.map ρ) = 9 := by
    have := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [MonoidHom.range_comp, Subgroup.range_subtype] at this
    rw [← this, hPcard]
  have hPAle : P.map ρ ≤ M'.map ρ := Subgroup.map_mono (hPY.trans hYM)
  have hPAA : Nat.card ((P.map ρ).subgroupOf (M'.map ρ)) = 9 := by
    rw [← hPA]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPAle).toEquiv
  have hζmem : ρ z ∈ M'.map ρ := Subgroup.mem_map_of_mem ρ hz
  have hcent : ∀ a : ↥(M'.map ρ), (⟨ρ z, hζmem⟩ : ↥(M'.map ρ)) * a = a * ⟨ρ z, hζmem⟩ := by
    intro a
    obtain ⟨m, hm, hma⟩ := Subgroup.mem_map.mp a.2
    apply Subtype.ext
    show ρ z * (a : Γ) = (a : Γ) * ρ z
    rw [← hma]
    exact hzc m hm
  have hz3' : (⟨ρ z, hζmem⟩ : ↥(M'.map ρ)) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
  have : Finite ↥(M'.map ρ) := Nat.finite_of_card_ne_zero (by rw [hAcard]; norm_num)
  have hmem := central_mem_of_card_nine hAcard _ hPAA _ hcent hz3'
  obtain ⟨y, hyP, hy⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hmem)
  exact ⟨y, hPY hyP, hy⟩

end CFSG.Quasithin.ModB
