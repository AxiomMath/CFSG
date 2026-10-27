module

public import CFSG.Quasithin.EmptyFaithful.S143FH

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

section OddFix

variable {W : Type*} [CommGroup W] {X L₁ L₂ : Subgroup (MulAut W)} {t₀ : MulAut W}

theorem eq_one_of_odd_fix (h : OfourStruct X L₁ L₂ t₀) {α : MulAut W} (hαX : α ∈ X)
    (hαN : α ∉ L₁ ⊔ L₂) {y : MulAut W} (hyX : y ∈ X) (hyα : α * y = y * α)
    (hodd : Odd (orderOf y)) {w : W} (hw : w ≠ 1) (hyw : y w = w) : y = 1 := by
  have hconj := conjAut_swap_of_not_mem_sup h hαX hαN
  have hyN : y ∈ L₁ ⊔ L₂ := h.odd_mem_sup hyX hodd
  obtain ⟨l, hl, hyl⟩ := exists_eq_delta h hconj hyN hyα
  have hl' : α * l * α⁻¹ ∈ L₂ := conj_mem_of_conjAut hconj.1 hl
  obtain ⟨a₁, ha₁, a₂, ha₂, hya, ha₁3, ha₂3⟩ := h.odd_decomp hyN hodd
  have hl1 : l = a₁ := (S1417.eq_of_mul_eq_of_inf_eq_bot h.Linf hl ha₁ hl' ha₂ (hyl.symm.trans hya)).1
  have hl2 : α * l * α⁻¹ = a₂ :=
    (S1417.eq_of_mul_eq_of_inf_eq_bot h.Linf hl ha₁ hl' ha₂ (hyl.symm.trans hya)).2
  have hodd3 : Odd (3 : ℕ) := by decide
  have hlodd : Odd (orderOf l) := by
    rw [hl1]; exact Odd.of_dvd_nat hodd3 (orderOf_dvd_of_pow_eq_one ha₁3)
  have hl'odd : Odd (orderOf (α * l * α⁻¹)) := by
    rw [hl2]; exact Odd.of_dvd_nat hodd3 (orderOf_dvd_of_pow_eq_one ha₂3)
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := h.exists_decomp_W w
  have e1 : (α * l * α⁻¹) u₁ = u₁ := h.L₂_fix₁ hl' hu₁
  have e2 : l u₂ = u₂ := h.L₁_fix₂ hl hu₂
  have hfix : (l * (α * l * α⁻¹)) (u₁ * u₂) = u₁ * u₂ := by rw [← hyl]; exact hyw
  have hlu₁ : l u₁ ∈ commV L₁ := commV_stable L₁ hl hu₁
  have hl'u₂ : (α * l * α⁻¹) u₂ ∈ commV L₂ := commV_stable L₂ hl' hu₂
  have hexp : (l * (α * l * α⁻¹)) (u₁ * u₂) = (l u₁) * ((α * l * α⁻¹) u₂) := by
    rw [MulAut.mul_apply, map_mul, e1, map_mul, h.L₁_fix₂ hl hl'u₂]
  rw [hexp] at hfix
  obtain ⟨hf1, hf2⟩ := S1417.eq_of_mul_eq_of_inf_eq_bot h.inf hlu₁ hu₁ hl'u₂ hu₂ hfix
  by_cases hu₁1 : u₁ = 1
  · have hu₂1 : u₂ ≠ 1 := by
      intro hu₂1; apply hw; rw [hu₁1, hu₂1, mul_one]
    have hl'1 : α * l * α⁻¹ = 1 :=
      S1417.eq_one_of_odd_of_fixed h.nat₂ (fun l' hl'' u hu => commV_stable L₂ hl'' hu) hl' hl'odd
        hu₂ hu₂1 hf2
    have hl1' : l = 1 := by
      calc l = α⁻¹ * (α * l * α⁻¹) * α := by group
        _ = 1 := by rw [hl'1]; group
    rw [hyl, hl'1, mul_one]
    exact hl1'
  · have hl1' : l = 1 :=
      S1417.eq_one_of_odd_of_fixed h.nat₁ (fun l' hl'' u hu => commV_stable L₁ hl'' hu) hl hlodd
        hu₁ hu₁1 hf1
    have hl'1 : α * l * α⁻¹ = 1 := by rw [hl1']; group
    rw [hyl, hl'1, mul_one]
    exact hl1'

end OddFix

theorem exists_orderOf_three {Γ : Type*} [Group Γ]
    (e : Γ ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 3)) : ∃ ω : Γ, orderOf ω = 3 := by
  have hrot : orderOf (finRotate 3) = 3 := orderOf_eq_prime (by decide) (by decide)
  exact ⟨e.symm (1, finRotate 3), by
    rw [MulEquiv.orderOf_eq, Prod.orderOf, orderOf_one, hrot]; rfl⟩

end S143

end CFSG.Quasithin
