module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.Heisenberg

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

theorem outer_index_ge_of_order_eleven {U : Type} [CommGroup U] [Finite U]
    (hU : ∀ w : U, w * w = 1) {Y S : Type} [Group Y] [Group S] (L : Subgroup Y) (F : Y →* S)
    (ρ : Y →* MulAut U) (hρ : ∀ y ∈ L, ρ y = 1 → y = 1)
    (hker : ∀ y ∈ L, F y = 1 → y ^ 3 = 1) {t l : Y} (ht2 : t * t = 1)
    (hyL : t * (l * t * l⁻¹) ∈ L) (h11 : orderOf (F (t * (l * t * l⁻¹))) = 11) :
    2 ^ 5 ≤ (fixV (Subgroup.zpowers (ρ t))).index := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  set d : ℕ := (fixV (Subgroup.zpowers (ρ t))).index with hd
  let t' : Y := l * t * l⁻¹
  let y : Y := t * t'
  let x : Y := y ^ 3
  have hyL' : y ∈ L := hyL
  have hordy : orderOf (F y) = 11 := h11
  have ht'2 : t' * t' = 1 := by
    change (l * t * l⁻¹) * (l * t * l⁻¹) = 1
    calc (l * t * l⁻¹) * (l * t * l⁻¹) = l * (t * t) * l⁻¹ := by group
      _ = 1 := by rw [ht2, mul_one, mul_inv_cancel]
  have hFy11 : (F y) ^ 11 = 1 := by rw [← hordy]; exact pow_orderOf_eq_one _
  have hy33 : y ^ 33 = 1 := by
    have hker11 : F (y ^ 11) = 1 := by rw [map_pow, hFy11]
    have h := hker (y ^ 11) (L.pow_mem hyL' 11) hker11
    rw [← pow_mul] at h
    norm_num at h
    exact h
  have hx11 : x ^ 11 = 1 := by
    have h : x ^ 11 = y ^ 33 := by
      change (y ^ 3) ^ 11 = y ^ 33
      rw [← pow_mul]
    rw [h, hy33]
  have hx1 : x ≠ 1 := by
    intro hx
    have hFx : F x = 1 := by rw [hx, map_one]
    have hxeq : F x = (F y) ^ 3 := by
      change F (y ^ 3) = (F y) ^ 3
      rw [map_pow]
    have h3 : (F y) ^ 3 = 1 := by rw [← hxeq]; exact hFx
    have hdvd : 11 ∣ 3 := by
      have := orderOf_dvd_iff_pow_eq_one.2 h3
      rwa [hordy] at this
    norm_num at hdvd
  have hxord : orderOf x = 11 := by
    exact orderOf_eq_prime hx11 hx1
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have ht'_inv : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht'2
  have hty : t * y * t⁻¹ = y⁻¹ := by
    have hL : t * y * t⁻¹ = t' * t := by
      change t * (t * t') * t⁻¹ = t' * t
      calc t * (t * t') * t⁻¹ = (t * t) * t' * t⁻¹ := by group
        _ = t' * t⁻¹ := by rw [ht2, one_mul]
        _ = t' * t := by rw [ht_inv]
    have hR : y⁻¹ = t' * t := by
      change (t * t')⁻¹ = t' * t
      rw [mul_inv_rev, ht'_inv, ht_inv]
    rw [hL, hR]
  have htx : t * x * t⁻¹ = x⁻¹ := by
    change t * y ^ 3 * t⁻¹ = (y ^ 3)⁻¹
    rw [← conj_pow, hty, inv_pow]
  have hxL : x ∈ L := L.pow_mem hyL' 3
  have ht2A : ρ t * ρ t = 1 := by rw [← map_mul, ht2, map_one]
  have hx11A : (ρ x) ^ 11 = 1 := by rw [← map_pow, hx11, map_one]
  have hx1A : ρ x ≠ 1 := fun h => hx1 (hρ x hxL h)
  have hxordA : orderOf (ρ x) = 11 := by
    exact orderOf_eq_prime hx11A hx1A
  have htxA : ρ t * ρ x * (ρ t)⁻¹ = (ρ x)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, htx, map_inv]
  have h10 : 2 ^ 10 ≤ (fixV (Subgroup.zpowers (ρ x))).index := by
    have h := CFSG.QuasithinUnique.Setup.X1.two_pow_orderOf_le_index_fixV hU
      (p := 11) (by norm_num) (g := ρ x) hxordA
    rwa [CFSG.QuasithinUnique.Setup.X1.orderOf_two_zmod_11] at h
  have hsq : (fixV (Subgroup.zpowers (ρ x))).index ≤ d ^ 2 :=
    index_fixV_le_sq_of_inverts (W := U) (p := 11) (by norm_num) hx11A ht2A htxA
  have h5 : 2 ^ 5 ≤ d := by
    by_contra hcon
    have hdlt : d < 2 ^ 5 := not_le.1 hcon
    have hlt : d ^ 2 < (2 ^ 5) ^ 2 := Nat.pow_lt_pow_left hdlt (by norm_num)
    have heq : (2 ^ 5) ^ 2 = 2 ^ 10 := by rw [← pow_mul]
    rw [heq] at hlt
    exact absurd hlt (not_lt.2 (h10.trans hsq))
  exact h5

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
