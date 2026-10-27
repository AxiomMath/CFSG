module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveBar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

section Decomposition

variable {G : Type} [Group G]

theorem exists_two_part_odd_part [Finite G] (c : G) :
    ∃ w y : G, w ∈ Subgroup.zpowers c ∧ y ∈ Subgroup.zpowers c ∧ c = w * y ∧
      (∃ k : ℕ, w ^ 2 ^ k = 1) ∧ Odd (orderOf y) := by
  have hN : orderOf c ≠ 0 := (orderOf_pos c).ne'
  obtain ⟨k, m, hm_odd, hNm⟩ := Nat.exists_eq_two_pow_mul_odd hN
  have hcop2 : Nat.Coprime 2 m := Nat.coprime_two_left.mpr hm_odd
  have hicop : IsCoprime ((2 ^ k : ℕ) : ℤ) (m : ℤ) := by
    simpa using hcop2.isCoprime.pow_left (m := k)
  obtain ⟨s, t, hst⟩ := hicop
  set W : ℤ := t * (m : ℤ) with hW
  set Y : ℤ := s * ((2 ^ k : ℕ) : ℤ) with hY
  have hcN : c ^ ((orderOf c : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast, pow_orderOf_eq_one]
  have hexpW : W * ((2 ^ k : ℕ) : ℤ) = t * ((orderOf c : ℕ) : ℤ) := by
    rw [hW, hNm]
    push_cast
    ring
  have hexpY : Y * (m : ℤ) = s * ((orderOf c : ℕ) : ℤ) := by
    rw [hY, hNm]
    push_cast
    ring
  refine ⟨c ^ W, c ^ Y, Subgroup.zpow_mem_zpowers c W, Subgroup.zpow_mem_zpowers c Y,
    ?_, ?_, ?_⟩
  · rw [← zpow_add, show W + Y = 1 by linarith, zpow_one]
  · refine ⟨k, ?_⟩
    rw [← zpow_natCast (c ^ W) (2 ^ k), ← zpow_mul]
    rw [hexpW, zpow_mul', hcN, one_zpow]
  · have hy_m : (c ^ Y) ^ m = 1 := by
      rw [← zpow_natCast (c ^ Y) m, ← zpow_mul]
      rw [hexpY, zpow_mul', hcN, one_zpow]
    exact hm_odd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hy_m)

theorem conj_inv_of_mem_zpowers {a c z : G} (hac : a * c * a⁻¹ = c⁻¹)
    (hz : z ∈ Subgroup.zpowers c) : a * z * a⁻¹ = z⁻¹ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [← hk, ← conj_zpow, hac, inv_zpow]

end Decomposition

section PartTwo

variable {G : Type} [Group G] [Finite G] {A M : Subgroup G} {n : ℕ}

theorem Setting12Two.mul_conj_not_mem (h : Setting12Two A M n) {a g : G} (ha : a ∈ A)
    (haK : a ∉ CFSG.Quasithin.kerIn M ⊤) (hg : g ∉ M) (ha2 : a * a = 1) :
    a * (g * a * g⁻¹) ∉ M := by
  intro hmem
  have haM : a ∈ M := h.A_le_M ha
  have hgaM : g * a * g⁻¹ ∈ M := by
    have h1 : a⁻¹ * (a * (g * a * g⁻¹)) ∈ M := M.mul_mem (M.inv_mem haM) hmem
    rwa [show a⁻¹ * (a * (g * a * g⁻¹)) = g * a * g⁻¹ by group] at h1
  have hxMg : g * a * g⁻¹ ∈ M.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨a, haM, by simp [MulAut.conj_apply]⟩
  have hx2 : ∃ k : ℕ, (g * a * g⁻¹) ^ 2 ^ k = 1 := by
    refine ⟨1, ?_⟩
    have h21 : (2 : ℕ) ^ 1 = 2 := by norm_num
    rw [h21, conj_pow, show a ^ 2 = 1 by rw [pow_two, ha2]]
    simp
  have hxK := h.mem_ker_of_mem_inf_conj hg hgaM hxMg hx2
  have hN : (CFSG.Quasithin.kerIn M ⊤).Normal := kerIn_top_normal12 M
  have hconj := hN.conj_mem (g * a * g⁻¹) hxK g⁻¹
  exact haK (by simpa [mul_assoc] using hconj)

theorem Setting12Two.mem_of_sq_mem (h : Setting12Two A M n) {a w : G} (ha : a ∈ A)
    (haK : a ∉ CFSG.Quasithin.kerIn M ⊤) (ha2 : a * a = 1) (hw : ∃ k : ℕ, w ^ 2 ^ k = 1)
    (hinv : a * w * a⁻¹ = w⁻¹) (hsq : w ^ 2 ∈ M) : w ∈ M := by
  by_contra hwM
  have haM : a ∈ M := h.A_le_M ha
  have hw2K : w ^ 2 ∈ CFSG.Quasithin.kerIn M ⊤ := by
    refine h.mem_ker_of_mem_inf_conj (g := w) hwM hsq ?_ ?_
    · refine Subgroup.mem_map.mpr ⟨w ^ 2, hsq, ?_⟩
      show w * w ^ 2 * w⁻¹ = w ^ 2
      group
    · obtain ⟨k, hk⟩ := hw
      exact ⟨k, by rw [pow_right_comm, hk, one_pow]⟩
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have haw_a : a * w * a = w⁻¹ := by simpa [ha_inv] using hinv
  have haw : a * w = w⁻¹ * a := by
    calc a * w = a * w * (a * a) := by rw [ha2, mul_one]
      _ = (a * w * a) * a := by group
      _ = w⁻¹ * a := by rw [haw_a]
  set t : G := a * w with ht
  have ht2 : t * t = 1 := by
    calc t * t = (a * w * a) * w := by rw [ht]; group
      _ = w⁻¹ * w := by rw [haw_a]
      _ = 1 := inv_mul_cancel w
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htat : t * a * t⁻¹ = a * w ^ 2 := by
    calc t * a * t⁻¹ = t * a * t := by rw [htinv]
      _ = (a * w) * a * (a * w) := by rw [ht]
      _ = a * w * (a * a) * w := by group
      _ = a * w ^ 2 := by rw [ha2, mul_one, pow_two, mul_assoc]
  have htM : t ∉ M := by
    intro htmem
    apply hwM
    have h1 : a⁻¹ * t ∈ M := M.mul_mem (M.inv_mem haM) htmem
    rwa [show a⁻¹ * t = w by rw [ht]; group] at h1
  have haw2M : a * w ^ 2 ∈ M := M.mul_mem haM (CFSG.Quasithin.kerIn_le hw2K)
  have hmem_t : a * w ^ 2 ∈ M.map (MulAut.conj t).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨a, haM, by simp [MulAut.conj_apply, htat]⟩
  have hx2 : ∃ k : ℕ, (a * w ^ 2) ^ 2 ^ k = 1 := by
    refine ⟨1, ?_⟩
    have h21 : (2 : ℕ) ^ 1 = 2 := by norm_num
    rw [h21, show a * w ^ 2 = t * a * t⁻¹ from htat.symm, conj_pow,
      show a ^ 2 = 1 by rw [pow_two, ha2]]
    simp
  have haw2K : a * w ^ 2 ∈ CFSG.Quasithin.kerIn M ⊤ :=
    h.mem_ker_of_mem_inf_conj htM haw2M hmem_t hx2
  have haK' : a ∈ CFSG.Quasithin.kerIn M ⊤ := by
    have h1 : (a * w ^ 2) * (w ^ 2)⁻¹ ∈ CFSG.Quasithin.kerIn M ⊤ :=
      (CFSG.Quasithin.kerIn M ⊤).mul_mem haw2K ((CFSG.Quasithin.kerIn M ⊤).inv_mem hw2K)
    rwa [show (a * w ^ 2) * (w ^ 2)⁻¹ = a by group] at h1
  exact haK haK'

theorem Setting12Two.mem_of_two_element (h : Setting12Two A M n) {a w : G} (ha : a ∈ A)
    (haK : a ∉ CFSG.Quasithin.kerIn M ⊤) (ha2 : a * a = 1) (hw : ∃ k : ℕ, w ^ 2 ^ k = 1)
    (hinv : a * w * a⁻¹ = w⁻¹) : w ∈ M := by
  have key : ∀ k : ℕ, ∀ w : G, w ^ 2 ^ k = 1 → a * w * a⁻¹ = w⁻¹ → w ∈ M := by
    intro k
    induction k with
    | zero =>
        intro w hw1 _
        rw [pow_zero, pow_one] at hw1
        rw [hw1]
        exact M.one_mem
    | succ k ih =>
        intro w hw1 hinv1
        have hw2 : (w ^ 2) ^ 2 ^ k = 1 := by
          rw [← pow_mul]
          rw [show 2 * 2 ^ k = 2 ^ (k + 1) by rw [pow_succ, mul_comm], hw1]
        have hinv2 : a * w ^ 2 * a⁻¹ = (w ^ 2)⁻¹ := by
          rw [← conj_pow, hinv1, inv_pow]
        exact h.mem_of_sq_mem ha haK ha2 ⟨k + 1, hw1⟩ hinv1 (ih (w ^ 2) hw2 hinv2)
  obtain ⟨k, hk⟩ := hw
  exact key k w hk hinv

theorem Setting12Two.exists_inverted_odd (h : Setting12Two A M n) (hA : IsElemAbelian 2 A)
    {a g : G} (ha : a ∈ A) (haK : a ∉ CFSG.Quasithin.kerIn M ⊤) (hg : g ∉ M) :
    ∃ w y : G, a * (g * a * g⁻¹) = w * y ∧ w ∈ Subgroup.zpowers (a * (g * a * g⁻¹)) ∧
      y ∈ Subgroup.zpowers (a * (g * a * g⁻¹)) ∧ (∃ k : ℕ, w ^ 2 ^ k = 1) ∧
      Odd (orderOf y) ∧ y ∉ M ∧ a * y * a⁻¹ = y⁻¹ := by
  have ha2 : a * a = 1 := by simpa [pow_two] using hA.2 a ha
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have ha'2 : (g * a * g⁻¹) * (g * a * g⁻¹) = 1 := by
    rw [← pow_two, conj_pow, show a ^ 2 = 1 by rw [pow_two, ha2]]
    simp
  have ha'_inv : (g * a * g⁻¹)⁻¹ = g * a * g⁻¹ := inv_eq_of_mul_eq_one_right ha'2
  set c : G := a * (g * a * g⁻¹) with hc
  have hc_inv : a * c * a⁻¹ = c⁻¹ := by
    rw [hc, ha_inv, mul_inv_rev, ha'_inv, ha_inv]
    calc a * (a * (g * a * g⁻¹)) * a = (a * a) * ((g * a * g⁻¹) * a) := by group
      _ = (g * a * g⁻¹) * a := by rw [ha2, one_mul]
  obtain ⟨w, y, hwzp, hyzp, hcwy, hw2, hyodd⟩ := exists_two_part_odd_part c
  have hwinv : a * w * a⁻¹ = w⁻¹ := conj_inv_of_mem_zpowers hc_inv hwzp
  have hyinv : a * y * a⁻¹ = y⁻¹ := conj_inv_of_mem_zpowers hc_inv hyzp
  have hwM : w ∈ M := h.mem_of_two_element ha haK ha2 hw2 hwinv
  have hcM : c ∉ M := by
    rw [hc]
    exact h.mul_conj_not_mem ha haK hg ha2
  have hyM : y ∉ M := by
    intro hyMem
    apply hcM
    rw [hcwy]
    exact M.mul_mem hwM hyMem
  exact ⟨w, y, hcwy, hwzp, hyzp, hw2, hyodd, hyM, hyinv⟩

end PartTwo

end CFSG.LocalAnalysis.WeakClosure81
