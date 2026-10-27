module

public import CFSG.RankThree.PartOne.SEITZ2.G2F2Gam

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ6
  CFSG.RankThree.PartOne.CTP
open scoped commutatorElement Matrix

variable {K : Type} [Field K]

local notation "SL2" => Matrix.SpecialLinearGroup (Fin 2) K

variable [CharP K 2]

theorem c0_eq_zero_of_actsAs_one {c : ℕ → K} (h : ActsAs (ordProd c) 1) : c 0 = 0 := by
  have h1 := h ![0, 1]
  simp only [dvv, dv, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at h1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, xp_zero, one_mul] at h1
  rw [conj_x3] at h1
  have h2 : xp 3 1 * xp 7 (c 0 * 1) = xp 3 1 * 1 := h1.trans (mul_one _).symm
  have h3 := mul_left_cancel h2
  simpa using xp_inj (p := 7) (by norm_num) (h3.trans (xp_zero 7).symm)

omit [CharP K 2] in
theorem mk6_zero (a0 a1 a4 a8 a3 a7 : K) : mk6 a0 a1 a4 a8 a3 a7 0 = a0 := by simp [mk6]

omit [CharP K 2] in
theorem mk6_one (a0 a1 a4 a8 a3 a7 : K) : mk6 a0 a1 a4 a8 a3 a7 1 = a1 := by simp [mk6]

omit [CharP K 2] in
theorem mk6_three (a0 a1 a4 a8 a3 a7 : K) : mk6 a0 a1 a4 a8 a3 a7 3 = a3 := by simp [mk6]

omit [CharP K 2] in
theorem ordProd_mk6_eq (a4 a8 a3 a7 : K) :
    xp 4 a4 * (xp 8 a8 * (xp 3 a3 * xp 7 a7)) = ordProd (mk6 0 0 a4 a8 a3 a7) := by
  rw [ordProd_mk6]
  simp only [xp_zero, one_mul, mul_assoc]

theorem seven_of_c1 {t₁ t₂ μ : K} {c : ℕ → K} (hn : ordProd c ∈ Gam t₁ t₂ μ) :
    xp 7 (c 1 ^ 3) ∈ Gam t₁ t₂ μ := by
  have h0 := x0_mem_Gam t₁ t₂ μ
  have hn1 : xp 0 1 * (ordProd c * xp 0 1 * (ordProd c)⁻¹) ∈ Gam t₁ t₂ μ :=
    mul_mem h0 (mul_mem (mul_mem hn h0) (inv_mem hn))
  rw [comm0, ordProd_mk6_eq] at hn1
  have hn2 := mul_mem h0 (mul_mem (mul_mem hn1 h0) (inv_mem hn1))
  rw [comm0] at hn2
  simpa [mk6, xp_zero] using hn2

theorem seven_of_c3 {t₁ t₂ μ : K} {c : ℕ → K} (hc1 : c 1 = 0) (hn : ordProd c ∈ Gam t₁ t₂ μ) :
    xp 7 (c 3) ∈ Gam t₁ t₂ μ := by
  have h0 := x0_mem_Gam t₁ t₂ μ
  have hn1 : xp 0 1 * (ordProd c * xp 0 1 * (ordProd c)⁻¹) ∈ Gam t₁ t₂ μ :=
    mul_mem h0 (mul_mem (mul_mem hn h0) (inv_mem hn))
  rw [comm0, hc1] at hn1
  simpa [xp_zero] using hn1

theorem comm_b2 (t₂ : K) (c : ℕ → K) (hc1 : c 1 = 0) (hc3 : c 3 = 0) :
    (xp 4 1 * xp 0 t₂) * ordProd c * (xp 4 1 * xp 0 t₂)⁻¹ * (ordProd c)⁻¹ = xp 7 (c 8) := by
  rw [ordProd_inv]
  unfold ordProd
  rw [hc1, hc3, mul_inv_rev, xp_inv, xp_inv]
  simp only [xp_zero]
  g2coll
  have e0 : t₂ + c 0 + t₂ + c 0 = 0 := by char2
  have e4 : (1 : K) + c 4 + 1 + c 4 = 0 := by char2
  have e7 : c 4 * c 8 + (c 8 + c 7 + (c 4 * c 8 + c 7)) = c 8 := by char2
  rw [e0, e4, e7, xp_zero, xp_zero, one_mul, one_mul]

theorem seven_of_c8 {t₁ t₂ μ : K} {c : ℕ → K} (hc1 : c 1 = 0) (hc3 : c 3 = 0)
    (hn : ordProd c ∈ Gam t₁ t₂ μ) : xp 7 (c 8) ∈ Gam t₁ t₂ μ := by
  have := mul_mem (mul_mem (mul_mem (b2_mem_Gam t₁ t₂ μ) hn)
    (inv_mem (b2_mem_Gam t₁ t₂ μ))) (inv_mem hn)
  rwa [comm_b2 t₂ c hc1 hc3] at this

theorem comm2 (c₄ c₇ μ : K) :
    xp 2 μ * (xp 4 c₄ * xp 7 c₇) * (xp 2 μ)⁻¹ * (xp 4 c₄ * xp 7 c₇)⁻¹ =
      ordProd (mk6 0 (c₄ * μ) 0 (c₄ ^ 2 * μ) (c₄ ^ 3 * μ ^ 2 + c₇ * μ) (c₄ ^ 3 * μ)) := by
  have hn : xp 4 c₄ * xp 7 c₇ = nB K * (xp 1 c₄ * xp 3 c₇) * (nB K)⁻¹ := by
    rw [conj_mul_eq, nB_x1, nB_x3]
  have e : xp 2 μ * (xp 4 c₄ * xp 7 c₇) * (xp 2 μ)⁻¹ * (xp 4 c₄ * xp 7 c₇)⁻¹ =
      nB K * (xp 0 μ * (xp 1 c₄ * xp 3 c₇) * (xp 0 μ)⁻¹ * (xp 1 c₄ * xp 3 c₇)⁻¹) *
        (nB K)⁻¹ := by
    rw [hn, ← nB_x0 μ]
    group
  have hn' : xp 1 c₄ * xp 3 c₇ = ordProd (mk6 0 c₄ 0 0 c₇ 0) := by
    rw [ordProd_mk6]
    simp only [xp_zero, one_mul, mul_one]
  have e2 : xp 0 μ * (xp 1 c₄ * xp 3 c₇) * (xp 0 μ)⁻¹ * (xp 1 c₄ * xp 3 c₇)⁻¹ =
      xp 0 μ * (ordProd (mk6 0 c₄ 0 0 c₇ 0) * xp 0 μ * (ordProd (mk6 0 c₄ 0 0 c₇ 0))⁻¹) := by
    rw [hn', xp_inv]
    simp only [mul_assoc]
  rw [e, e2, comm0]
  simp only [mk6_zero, mk6_one, mk6_three, zero_mul, zero_add]
  simp only [conj_mul_eq, nB_x4, nB_x8, nB_x3, nB_x7]
  rw [ordProd_mk6]
  simp only [xp_zero, one_mul, mul_one, mul_assoc]
  rw [(commute_37 _ _).eq]

theorem seven_of_nontriv {t₁ t₂ μ : K} (hμ : μ ≠ 0) {n : adjointGroup .G2 K}
    (hn : n ∈ Gam t₁ t₂ μ) (hUg : n ∈ Ug K) (hact : ActsAs n 1) (hne : n ≠ 1) :
    ∃ e : K, e ≠ 0 ∧ xp 7 e ∈ Gam t₁ t₂ μ := by
  obtain ⟨c, rfl⟩ := exists_ordProd hUg
  have hc0 := c0_eq_zero_of_actsAs_one hact
  by_cases h1 : c 1 = 0
  swap
  · exact ⟨c 1 ^ 3, pow_ne_zero 3 h1, seven_of_c1 hn⟩
  by_cases h3 : c 3 = 0
  swap
  · exact ⟨c 3, h3, seven_of_c3 h1 hn⟩
  by_cases h8 : c 8 = 0
  swap
  · exact ⟨c 8, h8, seven_of_c8 h1 h3 hn⟩
  have hform : ordProd c = xp 4 (c 4) * xp 7 (c 7) := by
    simp only [ordProd, hc0, h1, h3, h8, xp_zero, one_mul, mul_one]
  by_cases h4 : c 4 = 0
  · refine ⟨c 7, fun h7 => hne ?_, ?_⟩
    · rw [hform, h4, h7, xp_zero, xp_zero, mul_one]
    · rw [hform, h4, xp_zero, one_mul] at hn
      exact hn
  · rw [hform] at hn
    have hm := mul_mem (mul_mem (mul_mem (x2_mem_Gam t₁ t₂ μ) hn)
      (inv_mem (x2_mem_Gam t₁ t₂ μ))) (inv_mem hn)
    rw [comm2] at hm
    have h7 := seven_of_c1 hm
    simp only [mk6_one] at h7
    exact ⟨(c 4 * μ) ^ 3, pow_ne_zero 3 (mul_ne_zero h4 hμ), h7⟩

theorem gamma_full [Finite K] {k : Subfield K} (hk : Nat.card k = 2)
    {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (hK : Nat.card K = Nat.card k ^ d) {t₁ t₂ μ : K}
    (hμ : μ ≠ 0) (ht : ¬ (t₁ ∈ k ∧ t₂ ∈ k)) (a : K) : xp 7 a ∈ Gam t₁ t₂ μ := by
  obtain ⟨n, hn, hUg, hact, hne⟩ := exists_nontriv hk hd hd2 hK hμ ht
  obtain ⟨e, he, he7⟩ := seven_of_nontriv hμ hn hUg hact hne
  by_cases ha : a = 0
  · rw [ha, xp_zero]
    exact one_mem _
  have hs : a / e ≠ 0 := div_ne_zero ha he
  obtain ⟨g, hg, hgA⟩ := (mem_lev (H := Gam t₁ t₂ μ) (A := dg (a / e) hs)).1
    (lev_eq_top hk hd hd2 hK hμ ht ▸ Subgroup.mem_top _)
  have key : g * xp 7 e * g⁻¹ = xp 7 a := by
    have h' := hgA ![e, 0]
    rw [dg_mulVec] at h'
    simp only [dvv, dv, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, xp_zero, mul_one,
      div_mul_cancel₀ a he] at h'
    exact h'
  rw [← key]
  exact mul_mem (mul_mem hg he7) (inv_mem hg)

end CFSG.RankThree.PartOne.SEITZ2
