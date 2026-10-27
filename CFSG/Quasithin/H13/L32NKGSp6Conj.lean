module

public import CFSG.Quasithin.H13.L32NKGSp6S0

public section

namespace CFSG.Quasithin.H13.KGSp6

open CFSG.KGroups.Sp6

theorem factorization_seven_a : (1451520 : ℕ).factorization 7 = 1 := by
  have h : (1451520 : ℕ) = 7 * 207360 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem factorization_seven_b : (12096 : ℕ).factorization 7 = 1 := by
  have h : (12096 : ℕ) = 7 * 1728 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem exists_conj_P0 (h1 : countCheck 64 1451520 = true) {x : Mat6ˣ} (hx : x ∈ SpU)
    (hx7 : orderOf x = 7) : ∃ c ∈ SpU, c * x * c⁻¹ ∈ Subgroup.zpowers s0u := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hfac : (Nat.card SpU).factorization 7 = 1 := by
    rw [card_SpU h1]
    exact factorization_seven_a
  let P : Sylow 7 SpU := Sylow.ofCard (Subgroup.zpowers (⟨x, hx⟩ : SpU)) (by
    rw [Nat.card_zpowers, hfac, Subgroup.orderOf_mk, hx7, pow_one])
  let P0 : Sylow 7 SpU := Sylow.ofCard (Subgroup.zpowers (⟨s0u, s0u_mem⟩ : SpU)) (by
    rw [Nat.card_zpowers, hfac, Subgroup.orderOf_mk, orderOf_s0u, pow_one])
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq SpU P P0
  have hmem : c * (⟨x, hx⟩ : SpU) * c⁻¹ ∈ Subgroup.zpowers (⟨s0u, s0u_mem⟩ : SpU) := by
    have h2 : (c * (⟨x, hx⟩ : SpU) * c⁻¹) ∈ ((c • P : Sylow 7 SpU) : Subgroup SpU) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ (Subgroup.mem_zpowers _)
    rw [hc] at h2
    exact h2
  refine ⟨c, c.2, ?_⟩
  have h3 := Subgroup.mem_map_of_mem SpU.subtype hmem
  rw [MonoidHom.map_zpowers] at h3
  exact h3


theorem exists_conj_sub (h1 : countCheck 64 1451520 = true) {Γ₀ : Subgroup Mat6ˣ} (hΓ : Γ₀ ≤ SpU)
    (hcard : Nat.card Γ₀ = 12096) :
    ∃ c ∈ SpU, Subgroup.zpowers s0u ≤ Γ₀.map (MulAut.conj c).toMonoidHom := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨g, hg7⟩ := exists_prime_orderOf_dvd_card' (G := Γ₀) 7 (by rw [hcard]; norm_num)
  have hg7' : orderOf (g : Mat6ˣ) = 7 := by rw [Subgroup.orderOf_coe]; exact hg7
  obtain ⟨c, hc, hmem⟩ := exists_conj_P0 h1 (hΓ g.2) hg7'
  refine ⟨c, hc, ?_⟩
  have hz : c * (g : Mat6ˣ) * c⁻¹ ∈ Γ₀.map (MulAut.conj c).toMonoidHom :=
    ⟨g, g.2, by simp [MulAut.conj_apply]⟩
  have hzord : orderOf (c * (g : Mat6ˣ) * c⁻¹) = 7 := by
    have := MulEquiv.orderOf_eq (MulAut.conj c) (g : Mat6ˣ)
    rw [MulAut.conj_apply] at this
    rw [this, hg7']
  have hle : Subgroup.zpowers (c * (g : Mat6ˣ) * c⁻¹) ≤ Subgroup.zpowers s0u :=
    Subgroup.zpowers_le.2 hmem
  have heq : Subgroup.zpowers (c * (g : Mat6ˣ) * c⁻¹) = Subgroup.zpowers s0u := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hzord, orderOf_s0u]
  rw [← heq]
  exact Subgroup.zpowers_le.2 hz

end CFSG.Quasithin.H13.KGSp6
