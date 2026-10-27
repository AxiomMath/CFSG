module

public import CFSG.LocalAnalysis.StandardType.GGHalfGlueRel
public import CFSG.LocalAnalysis.StandardType.GGHalfGlueDet
public import CFSG.LocalAnalysis.StandardType.GGHalfNoTwist

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

private theorem zpowers_zpow_eq_of_three {G : Type} [Group G] {g : G} (hg : g ^ 3 = 1) {k : ℤ}
    (hk : ¬ (3 : ℤ) ∣ k) : Subgroup.zpowers (g ^ k) = Subgroup.zpowers g := by
  have hg3 : g ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, _root_.zpow_natCast]
    exact hg
  have hk3 : k % 3 = 1 ∨ k % 3 = 2 := by
    have h0 : k % 3 ≠ 0 := fun h0 => hk (Int.dvd_of_emod_eq_zero h0)
    omega
  have hred : g ^ k = g ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
    rw [_root_.zpow_add, _root_.zpow_mul, hg3, _root_.one_zpow, mul_one]
  rcases hk3 with h | h
  · have hk1 : g ^ k = g := by rw [hred, h, _root_.zpow_one]
    rw [hk1]
  · have hk2 : g ^ k = g⁻¹ := by
      rw [hred, h]
      apply eq_inv_of_mul_eq_one_left
      rw [← hg]
      group
    rw [hk2, Subgroup.zpowers_inv]

private theorem zpow_eq_one_of_three_dvd {G : Type} [Group G] {g : G} (hg : g ^ 3 = 1) {k : ℤ}
    (hk : (3 : ℤ) ∣ k) : g ^ k = 1 := by
  have hg3 : g ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, _root_.zpow_natCast]
    exact hg
  obtain ⟨t, ht⟩ := hk
  rw [ht, _root_.zpow_mul, hg3, _root_.one_zpow]

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {m : ℕ} {y : G}
  {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
  (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂)

include h

private theorem zpowers_data :
    ∃ i j a b : ℤ, y = x ^ i * vElt φ₁ ^ j ∧ wElt φ₂ = x ^ a * vElt φ₁ ^ b ∧
      (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ b ∧ ¬ (3 : ℤ) ∣ j ∧ ¬ (3 : ℤ) ∣ a := by
  obtain ⟨hcomm, hexp, hxB, hyB, -, -, -, -, -, -⟩ := h.basic
  obtain ⟨i, j, hy⟩ := h.exists_eq_x_pow_mul_v_pow hyB h.y_comm_J
  obtain ⟨a, b, hw⟩ := h.exists_eq_x_pow_mul_v_pow h.wElt_mem h.w_comm_J
  have hj : ¬ (3 : ℤ) ∣ j := h.not_dvd_of_y_eq hy
  have hD : ¬ (3 : ℤ) ∣ i * b - j * a := h.not_dvd_det hy hw
  have hm : 1 ≤ m := by have := h.nbr.2.2.1; omega
  have hp3 : p = 3 := h.nbr.2.1
  have hNoTr : GGNoTransvection 3 Bs := by
    have h' := h.noTr
    rwa [hp3] at h'
  have R3y : endT₂ φ₂ * (x ^ i * vElt φ₁ ^ j) * (endT₂ φ₂)⁻¹ = x ^ i * vElt φ₁ ^ j := by
    rw [← hy]; exact h.sk_y
  have R4y : hElt φ₂ * (x ^ i * vElt φ₁ ^ j) * (hElt φ₂)⁻¹ = x ^ i * vElt φ₁ ^ j := by
    rw [← hy]; exact h.h_y
  have R3w : endT₂ φ₂ * (x ^ a * vElt φ₁ ^ b) * (endT₂ φ₂)⁻¹ = (x ^ a * vElt φ₁ ^ b)⁻¹ := by
    rw [← hw]; exact h.sk_w
  have R4u : hElt φ₂ * uElt φ₂ * (hElt φ₂)⁻¹ = x ^ a * vElt φ₁ ^ b := by
    rw [← hw]; exact h.h_u
  have R4w : hElt φ₂ * (x ^ a * vElt φ₁ ^ b) * (hElt φ₂)⁻¹ = uElt φ₂ := by
    rw [← hw]; exact h.h_w
  obtain ⟨h3i, h3b⟩ := no_twist_core (Bs := Bs) (x := x) (v := vElt φ₁) (u := uElt φ₂)
    (Z := zSet φ₁) (s₀ := sZero φ₁) (g := gElt φ₁) (sk := endT₂ φ₂) (h := hElt φ₂)
    (i := i) (j := j) (a := a) (b := b)
    hcomm hexp hNoTr hxB h.vElt_mem h.uElt_mem (fun p' q' r' hpqr => h.independent hpqr)
    h.zSet_le h.bs_le_closure h.s0_mem_normalizer (h.gElt_mem_normalizer hm) h.sk_mem_normalizer
    (h.hElt_mem_normalizer hm) h.zSet_fix h.s0_x h.s0_u h.s0_v h.g_x h.g_v h.g_u
    R3y h.sk_u R3w R4y R4u R4w hj hD
  have h3a : ¬ (3 : ℤ) ∣ a := by
    intro ha
    apply hD
    have h1 : (3 : ℤ) ∣ i * b := Dvd.dvd.mul_right h3i b
    have h2 : (3 : ℤ) ∣ j * a := Dvd.dvd.mul_left ha j
    exact dvd_sub h1 h2
  exact ⟨i, j, a, b, hy, hw, h3i, h3b, hj, h3a⟩

theorem zpowers_y :
    Subgroup.zpowers y = Subgroup.zpowers (φ₁ (omegaBlock (m + 1 + 1) ⟨0, by omega⟩)) := by
  obtain ⟨i, j, -, -, hy, -, h3i, -, hj, -⟩ := zpowers_data h
  obtain ⟨-, hexp, hxB, -, -, -, -, -, -, -⟩ := h.basic
  have hxipow : x ^ i = 1 := zpow_eq_one_of_three_dvd (hexp x hxB) h3i
  have hyv : y = vElt φ₁ ^ j := by rw [hy, hxipow, one_mul]
  show Subgroup.zpowers y = Subgroup.zpowers (vElt φ₁)
  rw [hyv]
  exact zpowers_zpow_eq_of_three (hexp _ h.vElt_mem) hj

theorem zpowers_x :
    Subgroup.zpowers x = Subgroup.zpowers (φ₂ (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩)) := by
  obtain ⟨i, j, a, b, hy, hw, h3i, h3b, hj, h3a⟩ := zpowers_data h
  obtain ⟨-, hexp, hxB, -, -, -, -, -, -, -⟩ := h.basic
  have hvb : vElt φ₁ ^ b = 1 := zpow_eq_one_of_three_dvd (hexp _ h.vElt_mem) h3b
  have hwx : wElt φ₂ = x ^ a := by rw [hw, hvb, mul_one]
  show Subgroup.zpowers x = Subgroup.zpowers (wElt φ₂)
  rw [hwx]
  exact (zpowers_zpow_eq_of_three (hexp x hxB) h3a).symm

end GGHalfCtx

end CFSG.StandardType

end
