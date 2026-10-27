module

public import CFSG.Quasithin.Recognition.F112Crit.HallIndex

public section

namespace CFSG.Quasithin.F112Crit

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem exists_mul_centralizer_of_comm_mem {W W₁ X : Subgroup G} (hW : IsPGroup 2 W)
    (hX : Odd (Nat.card X)) (hW₁W : W₁ ≤ W) (hXW : X ≤ normalizer (W : Set G))
    (hXW₁ : X ≤ normalizer (W₁ : Set G)) {w : G} (hw : w ∈ W)
    (hcomm : ∀ x ∈ X, w * x * w⁻¹ * x⁻¹ ∈ W₁) :
    ∃ n ∈ W₁, ∃ c ∈ W, (∀ x ∈ X, c * x = x * c) ∧ w = n * c := by
  have hWX : W ⊓ X = ⊥ := by
    obtain ⟨k, hk⟩ := hW.exists_card_eq
    refine inf_eq_bot_of_coprime ?_
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hX)
  have hXW₁' : X ⊓ W₁ = ⊥ := by
    rw [inf_comm]
    exact eq_bot_mono (inf_le_inf_right X hW₁W) hWX
  have hHN : X ⊔ W₁ ≤ normalizer (W₁ : Set G) := sup_le hXW₁ le_normalizer
  have hidx : W₁.relIndex (X ⊔ W₁) = Nat.card X := by
    have h1 := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hXW₁
    have h2 := CFSG.QuasithinUnique.C5.card_eq_card_mul_relIndex (le_sup_right : W₁ ≤ X ⊔ W₁)
    rw [hXW₁', Subgroup.card_bot, mul_one, h2, mul_comm (Nat.card X)] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  set Y : Subgroup G := X.map (MulAut.conj w).toMonoidHom with hY
  have hYH : Y ≤ X ⊔ W₁ := by
    rintro _ ⟨x, hx, rfl⟩
    have e : (MulAut.conj w).toMonoidHom x = (w * x * w⁻¹ * x⁻¹) * x := by
      simp [MulAut.conj_apply]
    rw [e]
    exact mul_mem (mem_sup_right (hcomm x hx)) (mem_sup_left hx)
  have hYc : Nat.card Y = Nat.card X :=
    Subgroup.card_map_of_injective (MulAut.conj w).injective
  obtain ⟨c, hcH, hc⟩ := exists_conj_hall_of_normal_two (le_sup_right : W₁ ≤ X ⊔ W₁) hHN
    (hW.to_le hW₁W) (hidx ▸ hX) (le_sup_left : X ≤ X ⊔ W₁) hYH hidx.symm (hYc.trans hidx.symm)
  have hcH' : c⁻¹ ∈ ((X ⊔ W₁ : Subgroup G) : Set G) := inv_mem hcH
  rw [coe_mul_of_left_le_normalizer_right X W₁ hXW₁] at hcH'
  obtain ⟨x₁, hx₁, n₁, hn₁, hxn⟩ := hcH'
  replace hxn : x₁ * n₁ = c⁻¹ := hxn
  replace hx₁ : x₁ ∈ X := hx₁
  replace hn₁ : n₁ ∈ W₁ := hn₁
  have hd : ∀ x ∈ X, (n₁ * w) * x * (n₁ * w)⁻¹ ∈ X := by
    intro x hx
    have hmem : w * x * w⁻¹ ∈ Y := ⟨x, hx, by simp [MulAut.conj_apply]⟩
    have h1 := (hc _).mp hmem
    have hc' : c = (x₁ * n₁)⁻¹ := by rw [hxn, inv_inv]
    rw [hc', inv_inv] at h1
    have h2 : x₁⁻¹ * (x₁ * n₁ * (w * x * w⁻¹) * (x₁ * n₁)⁻¹) * x₁ ∈ X :=
      mul_mem (mul_mem (inv_mem hx₁) h1) hx₁
    have e : x₁⁻¹ * (x₁ * n₁ * (w * x * w⁻¹) * (x₁ * n₁)⁻¹) * x₁ =
        (n₁ * w) * x * (n₁ * w)⁻¹ := by group
    rwa [e] at h2
  have hdW : n₁ * w ∈ W := mul_mem (hW₁W hn₁) hw
  refine ⟨n₁⁻¹, inv_mem hn₁, n₁ * w, hdW, fun x hx => ?_, by group⟩
  have hcX : (n₁ * w) * x * (n₁ * w)⁻¹ * x⁻¹ ∈ X := mul_mem (hd x hx) (inv_mem hx)
  have hcW : (n₁ * w) * x * (n₁ * w)⁻¹ * x⁻¹ ∈ W := by
    have h1 : x * (n₁ * w)⁻¹ * x⁻¹ ∈ W :=
      (mem_normalizer_iff.mp (hXW hx) _).mp (inv_mem hdW)
    have e : (n₁ * w) * x * (n₁ * w)⁻¹ * x⁻¹ = (n₁ * w) * (x * (n₁ * w)⁻¹ * x⁻¹) := by group
    rw [e]
    exact mul_mem hdW h1
  have h1 : (n₁ * w) * x * (n₁ * w)⁻¹ * x⁻¹ = 1 := by
    have h : (n₁ * w) * x * (n₁ * w)⁻¹ * x⁻¹ ∈ W ⊓ X := ⟨hcW, hcX⟩
    rw [hWX] at h
    exact (mem_bot.mp h)
  calc (n₁ * w) * x = ((n₁ * w) * x * (n₁ * w)⁻¹ * x⁻¹) * (x * (n₁ * w)) := by group
    _ = x * (n₁ * w) := by rw [h1, one_mul]

theorem mem_of_pow_two_pow_mem_of_two_elt {A N : Subgroup G}
    (h2 : ∀ g ∈ A, ∀ k : ℕ, g ^ 2 ^ k = 1 → g ∈ N) {g : G} (hg : g ∈ A) {m : ℕ}
    (hm : g ^ 2 ^ m ∈ N) : g ∈ N := by
  obtain ⟨b, s, hs, hbs⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hgs : g ^ s ∈ N := h2 _ (A.pow_mem hg s) b (by
    rw [← pow_mul, mul_comm, ← hbs, pow_orderOf_eq_one])
  have hcop : Nat.Coprime s (2 ^ m) := Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hs)
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, (s : ℤ) * u + ((2 ^ m : ℕ) : ℤ) * v = 1 := by
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    exact ⟨u, v, by push_cast at huv ⊢; linarith⟩
  have hy : g = (g ^ s) ^ u * (g ^ 2 ^ m) ^ v := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
    push_cast at huv ⊢
    rw [huv, zpow_one]
  rw [hy]
  exact N.mul_mem (N.zpow_mem hgs u) (N.zpow_mem hm v)

end CFSG.Quasithin.F112Crit

end
