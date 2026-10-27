module

public import CFSG.Quasithin.EmptyFaithful.S146zNFinR

public section

namespace CFSG.Quasithin.A6Fin

open Equiv Equiv.Perm CFSG.Quasithin CFSG.Quasithin.A6Mod

variable {W : Type} [CommGroup W] [Finite W] {ρ : A6 →* MulAut W}

theorem fixSub_eq_range (hsq : ∀ w : W, w * w = 1) (γ : MulAut W) (hγ : γ * γ = 1)
    (hc : Nat.card (fixSub γ) * Nat.card (fixSub γ) = Nat.card W) :
    ∀ v ∈ fixSub γ, ∃ w : W, γ w * w⁻¹ = v := by
  let φ : W →* W := MonoidHom.mk' (fun w => γ w * w⁻¹) (fun a b => by
    simp only [map_mul, mul_inv_rev]
    rw [mul_comm b⁻¹ a⁻¹]
    simp only [mul_assoc, mul_comm, mul_left_comm])
  have hker : φ.ker = fixSub γ := by
    ext w
    rw [MonoidHom.mem_ker, mem_fixSub]
    show γ w * w⁻¹ = 1 ↔ γ w = w
    exact mul_inv_eq_one
  have hrange : φ.range ≤ fixSub γ := by
    rintro _ ⟨w, rfl⟩
    rw [mem_fixSub]
    show γ (γ w * w⁻¹) = γ w * w⁻¹
    have h2 : γ (γ w) = w := by
      have := congrArg (fun f : MulAut W => f w) hγ
      simpa using this
    rw [map_mul, h2, map_inv]
    have hinv : ∀ x : W, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hsq x)
    rw [hinv (γ w), hinv w]
    exact mul_comm _ _
  have hcard := Subgroup.card_ker_mul_card_range φ
  rw [hker, ← hc] at hcard
  have hpos : 0 < Nat.card (fixSub γ) := Nat.card_pos
  have hr : Nat.card φ.range = Nat.card (fixSub γ) := Nat.eq_of_mul_eq_mul_left hpos hcard
  have heq : φ.range = fixSub γ :=
    Subgroup.eq_of_le_of_card_ge hrange (by rw [hr])
  intro v hv
  rw [← heq] at hv
  obtain ⟨w, hw⟩ := hv
  exact ⟨w, hw⟩

omit [Finite W] in
theorem fixSub_map_conj (c k : A6) :
    (fixSub (ρ c)).map (ρ k).toMonoidHom = fixSub (ρ (k * c * k⁻¹)) := by
  ext w
  rw [Subgroup.mem_map, mem_fixSub]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [mem_fixSub] at hv
    show ρ (k * c * k⁻¹) (ρ k v) = ρ k v
    rw [map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hv]
  · intro hw
    refine ⟨(ρ k)⁻¹ w, ?_, MulAut.apply_inv_self W (ρ k) w⟩
    rw [mem_fixSub]
    have h1 : ρ k (ρ c ((ρ k)⁻¹ w)) = w := by
      have := hw
      rw [map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply] at this
      exact this
    have h2 : ρ c ((ρ k)⁻¹ w) = (ρ k)⁻¹ w := by
      have := congrArg (fun x => (ρ k)⁻¹ x) h1
      simpa using this
    exact h2

theorem Setup.card_fixSub_invol (h : Setup ρ) {g : A6} (hg1 : g ≠ 1) (hg2 : g * g = 1) :
    Nat.card (fixSub (ρ g)) = 4 := by
  have := fc_invol g hg1 hg2 (ρ := ρ)
  rw [h.fc_x0A6] at this
  exact this

theorem Setup.eqv_of_quad (h : Setup ρ) {c d : A6} (hc1 : c ≠ 1) (hc2 : c * c = 1) (hd1 : d ≠ 1)
    (hd2 : d * d = 1) (hq : A6QuadPair (ρ c) (ρ d)) : fixSub (ρ c) = fixSub (ρ d) := by
  have h4d := h.card_fixSub_invol hd1 hd2
  have h4c := h.card_fixSub_invol hc1 hc2
  have hsub : fixSub (ρ d) ≤ fixSub (ρ c) := by
    intro v hv
    obtain ⟨w, hw⟩ := fixSub_eq_range h.sq (ρ d) (by rw [← map_mul, hd2, map_one])
      (by rw [h4d, h.card]) v hv
    rw [mem_fixSub]
    have h1 := hq w
    rw [hw] at h1
    exact mul_inv_eq_one.mp h1
  exact (Subgroup.eq_of_le_of_card_ge hsub (by rw [h4c, h4d])).symm

theorem Setup.eqv_mul (h : Setup ρ) {c d : A6} (hcd : c ≠ d) (hc1 : c ≠ 1) (hc2 : c * c = 1)
    (hd2 : d * d = 1) (hcomm : c * d = d * c) (heq : fixSub (ρ c) = fixSub (ρ d)) :
    fixSub (ρ c) = fixSub (ρ (c * d)) := by
  have hcd2 : (c * d) * (c * d) = 1 := by
    calc (c * d) * (c * d) = c * (d * c) * d := by group
      _ = c * (c * d) * d := by rw [hcomm]
      _ = (c * c) * (d * d) := by group
      _ = 1 := by rw [hc2, hd2]; group
  have hcd1 : c * d ≠ 1 := by
    intro e
    apply hcd
    have : c = d⁻¹ := mul_eq_one_iff_eq_inv.mp e
    rw [this]
    exact inv_eq_of_mul_eq_one_right hd2
  have h4 := h.card_fixSub_invol hcd1 hcd2
  have h4c := h.card_fixSub_invol hc1 hc2
  have hsub : fixSub (ρ c) ≤ fixSub (ρ (c * d)) := by
    intro v hv
    have hv' : v ∈ fixSub (ρ d) := heq ▸ hv
    rw [mem_fixSub] at hv hv' ⊢
    rw [map_mul]
    show ρ c (ρ d v) = v
    rw [hv', hv]
  exact Subgroup.eq_of_le_of_card_ge hsub (by rw [h4, h4c])

omit [Finite W] in
theorem fixSub_eq_conj {c d : A6} (k : A6) (heq : fixSub (ρ c) = fixSub (ρ d)) :
    fixSub (ρ (k * c * k⁻¹)) = fixSub (ρ (k * d * k⁻¹)) := by
  rw [← fixSub_map_conj c k, ← fixSub_map_conj d k, heq]

end CFSG.Quasithin.A6Fin
