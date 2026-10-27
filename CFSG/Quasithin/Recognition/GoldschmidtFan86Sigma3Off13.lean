module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Off1

public section

namespace CFSG.Quasithin.Fan86.Sigma3

theorem perm3_conj : ∀ σ ρ : Equiv.Perm (Fin 3), ρ ^ 3 = 1 → ρ ≠ 1 →
    σ * ρ * σ⁻¹ = ρ ∨ σ * ρ * σ⁻¹ = ρ⁻¹ := by
  decide

variable {H : Type*} [Group H] [Finite H] {S : Subgroup H}

theorem oQ_pow_three {q : H} (hq : q ∈ oQ H) (h3 : q ^ 3 = 1) : q = 1 := by
  have hk := Classical.choose_spec ((oQ_two (H := H)) ⟨q, hq⟩)
  have hord2 : orderOf q ∣ 2 ^ (Classical.choose ((oQ_two (H := H)) ⟨q, hq⟩)) :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have hord3 : orderOf q ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime (2 ^ (Classical.choose ((oQ_two (H := H)) ⟨q, hq⟩))) 3 :=
    Nat.Coprime.pow_left _ (by decide)
  have := Nat.dvd_gcd hord2 hord3
  rw [hcop] at this
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)

theorem Sig3.zpowers_normal (h : Sig3 H S) {x : H} (hx : orderOf x = 3)
    (hQx : ∀ q ∈ oQ H, x * q = q * x) : (Subgroup.zpowers x).Normal := by
  obtain ⟨ψ, -, hker⟩ := h.exists_hom
  have hker' : ψ.ker = oQ H := hker
  have hxψ : ψ x ≠ 1 := fun h1 => Sig3.not_mem_Q_of_order hx (hker ▸ h1)
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hψ3 : (ψ x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hconj : ∀ g : H, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x⁻¹ := by
    intro g
    rcases perm3_conj (ψ g) (ψ x) hψ3 hxψ with h1 | h1
    · left
      have hq : g * x * g⁻¹ * x⁻¹ ∈ oQ H := by
        rw [← hker', MonoidHom.mem_ker]
        simp only [map_mul, map_inv]
        rw [h1]
        group
      have hc : Commute (g * x * g⁻¹ * x⁻¹) x := (hQx _ hq).symm
      have h3 : (g * x * g⁻¹ * x⁻¹ * x) ^ 3 = 1 := by
        rw [show g * x * g⁻¹ * x⁻¹ * x = g * x * g⁻¹ by group, conj_pow, hx3]
        group
      rw [hc.mul_pow, hx3, mul_one] at h3
      exact mul_inv_eq_one.1 (oQ_pow_three hq h3)
    · right
      have hq : g * x * g⁻¹ * x ∈ oQ H := by
        rw [← hker', MonoidHom.mem_ker]
        simp only [map_mul, map_inv]
        rw [h1]
        group
      have hc0 : Commute (g * x * g⁻¹ * x) x := (hQx _ hq).symm
      have hc : Commute (g * x * g⁻¹ * x) x⁻¹ := hc0.inv_right
      have h3 : (g * x * g⁻¹ * x * x⁻¹) ^ 3 = 1 := by
        rw [show g * x * g⁻¹ * x * x⁻¹ = g * x * g⁻¹ by group, conj_pow, hx3]
        group
      rw [hc.mul_pow, inv_pow, hx3, inv_one, mul_one] at h3
      exact mul_eq_one_iff_eq_inv.1 (oQ_pow_three hq h3)
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
  rw [← conj_zpow]
  rcases hconj g with e | e
  · rw [e]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) m
  · rw [e]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)) m

end CFSG.Quasithin.Fan86.Sigma3
