module

public import CFSG.RankThree.PartOne.SEITZ8.D4TwoGam

public section

namespace CFSG.RankThree.PartOne.SEITZ8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ7 CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.CTP
open scoped commutatorElement Matrix

variable {K : Type} [Field K] {σ : K →+* K} [CharP K 2]

local notation "SL2F" => Matrix.SpecialLinearGroup (Fin 2) (fixedField σ)

omit [CharP K 2] in
theorem xH_inj {a b : K} (h : xH a = xH b) : a = b :=
  xPar_injective (F := rootOperatorFamily d4) (K := K) (isRoot_d4 (by norm_num : 22 < 24)) h

theorem comm0 (hσ : ∀ c, σ (σ (σ c)) = c) (c : ℕ → K) {d : K} (hd : σ d = d) :
    xB d * (ordT σ c * xB d * (ordT σ c)⁻¹) =
      xAB σ (d * c 1) * xAAB σ (d * c 1 * σ (c 1)) *
        xN (d * (c 1 * σ (c 1) * σ (σ (c 1)))) *
        xH (c 0 * d * (c 1 * σ (c 1) * σ (σ (c 1))) + d ^ 2 * (c 1 * σ (c 1) * σ (σ (c 1))) +
          d * c 3) := by
  have hBB : xB d * xB d = 1 := xd_mul_self 2 d
  rw [conj_xB σ hσ c d hd]
  calc _ = (xB d * xB d) * xAB σ (d * c 1) * xAAB σ (d * c 1 * σ (c 1)) *
        xN (d * (c 1 * σ (c 1) * σ (σ (c 1)))) *
        xH (c 0 * d * (c 1 * σ (c 1) * σ (σ (c 1))) + d ^ 2 * (c 1 * σ (c 1) * σ (σ (c 1))) +
          d * c 3) := by group
    _ = _ := by rw [hBB, one_mul]

theorem comm_xB_ordT (hσ : ∀ c, σ (σ (σ c)) = c) (c : ℕ → K) :
    xB 1 * (ordT σ c * xB 1 * (ordT σ c)⁻¹) =
      ordT σ (mkT 0 0 (c 1) (c 1 * σ (c 1)) (c 1 * σ (c 1) * σ (σ (c 1)))
        (c 0 * (c 1 * σ (c 1) * σ (σ (c 1))) + (c 1 * σ (c 1) * σ (σ (c 1))) + c 3)) := by
  rw [comm0 hσ c (map_one σ), ordT_mkT]
  simp only [xB, xA, map_zero, xd_zero, one_mul, mul_one, one_pow]

omit [CharP K 2] in
theorem ordT_xH (e : K) : ordT σ (mkT 0 0 0 0 0 e) = xH e := by
  rw [ordT_mkT]
  simp only [xB, xA, xAB, xAAB, xN, map_zero, xd_zero, one_mul]

section Seven

variable {k : Subfield K} {τ : K → fixedField σ} {t₁ μ : fixedField σ}
  (hσ : ∀ c, σ (σ (σ c)) = c)
include hσ

omit hσ in
theorem c0_eq_zero_of_actsAs_one {c : ℕ → K} (h : ActsAs (ordT σ c) (1 : SL2F)) : c 0 = 0 := by
  have h1 := h ![0, 1]
  simp only [dvv, dv, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at h1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ZeroMemClass.coe_zero,
    OneMemClass.coe_one, xH, xd_zero, one_mul] at h1
  have h2 := conj_xN σ c 1
  simp only [xN] at h1 h2
  rw [h1] at h2
  have h3 : xd 22 (c 0 * 1) = xd 22 0 := by
    have := mul_left_cancel (a := xd 19 (1 : K)) (h2.symm.trans (mul_one _).symm)
    rw [xd_zero]
    exact this
  simpa using xH_inj h3

theorem seven_of_c1 {c : ℕ → K} (hn : ordT σ c ∈ Gam σ k τ t₁ μ) :
    xH (c 1 * σ (c 1) * σ (σ (c 1))) ∈ Gam σ k τ t₁ μ := by
  have h0 : xB (1 : K) ∈ Gam σ k τ t₁ μ := xB1_mem_Gam
  have hn1 : xB 1 * (ordT σ c * xB 1 * (ordT σ c)⁻¹) ∈ Gam σ k τ t₁ μ :=
    mul_mem h0 (mul_mem (mul_mem hn h0) (inv_mem hn))
  rw [comm_xB_ordT hσ] at hn1
  have hn2 := mul_mem h0 (mul_mem (mul_mem hn1 h0) (inv_mem hn1))
  rw [comm_xB_ordT hσ] at hn2
  simpa [mkT, ordT_xH] using hn2

theorem seven_of_c3 {c : ℕ → K} (hc1 : c 1 = 0) (hn : ordT σ c ∈ Gam σ k τ t₁ μ) :
    xH (c 3) ∈ Gam σ k τ t₁ μ := by
  have h0 : xB (1 : K) ∈ Gam σ k τ t₁ μ := xB1_mem_Gam
  have hn1 : xB 1 * (ordT σ c * xB 1 * (ordT σ c)⁻¹) ∈ Gam σ k τ t₁ μ :=
    mul_mem h0 (mul_mem (mul_mem hn h0) (inv_mem hn))
  rw [comm_xB_ordT hσ, hc1] at hn1
  simp only [map_zero, mul_zero, zero_add, add_zero] at hn1
  rwa [ordT_xH] at hn1

omit hσ in
theorem comm_b2 (κ t : K) (c : ℕ → K) (hc1 : c 1 = 0) (hc3 : c 3 = 0) :
    (xAB σ κ * xB t) * ordT σ c * (xAB σ κ * xB t)⁻¹ * (ordT σ c)⁻¹ =
      xH (κ * σ (c 8) + σ κ * σ (σ (c 8)) + σ (σ κ) * c 8) := by
  unfold ordT xA xAB xAAB xB xN xH
  rw [hc1, hc3]
  simp only [mul_inv_rev, xd_inv, map_zero, xd_zero, mul_one]
  d4coll
  d4fin

omit hσ [CharP K 2] in
theorem exists_kappa (hσ : ∀ c, σ (σ (σ c)) = c) (hne : ∃ a, σ a ≠ a)
    (hspan : ∀ x : K, x ∈ AddSubgroup.closure {y | ∃ e : K, σ e = e ∧ ∃ a ∈ k, y = e * a})
    {r : K} (hr : r ≠ 0) : ∃ κ ∈ k, κ * σ r + σ κ * σ (σ r) + σ (σ κ) * r ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have key : ∀ x : K, x * σ r + σ x * σ (σ r) + σ (σ x) * r = 0 := by
    intro x
    refine AddSubgroup.closure_induction
      (p := fun x _ => x * σ r + σ x * σ (σ r) + σ (σ x) * r = 0) ?_ ?_ ?_ ?_ (hspan x)
    · rintro y ⟨e, he, a, ha, rfl⟩
      have h := hcon a ha
      calc _ = e * (a * σ r + σ a * σ (σ r) + σ (σ a) * r) := by
            simp only [map_mul, he]
            ring
        _ = 0 := by rw [h, mul_zero]
    · simp
    · intro x y _ _ hx hy
      simp only [map_add]
      linear_combination hx + hy
    · intro x _ hx
      simp only [map_neg]
      linear_combination -hx
  exact hr (trace_form_eq_zero σ hσ hne key)

theorem seven_of_c8 (hne : ∃ a, σ a ≠ a)
    (hspan : ∀ x : K, x ∈ AddSubgroup.closure {y | ∃ e : K, σ e = e ∧ ∃ a ∈ k, y = e * a})
    {c : ℕ → K} (hc1 : c 1 = 0) (hc3 : c 3 = 0) (hc8 : c 8 ≠ 0)
    (hn : ordT σ c ∈ Gam σ k τ t₁ μ) :
    ∃ e : fixedField σ, e ≠ 0 ∧ xH (e : K) ∈ Gam σ k τ t₁ μ := by
  obtain ⟨κ, hκ, hT⟩ := exists_kappa hσ hne hspan hc8
  have hb : xAB σ κ * xB (τ κ : K) ∈ Gam σ k τ t₁ μ := b2_mem_Gam hκ
  have h := mul_mem (mul_mem (mul_mem hb hn) (inv_mem hb)) (inv_mem hn)
  rw [comm_b2 κ (τ κ : K) c hc1 hc3] at h
  have hfix : σ (κ * σ (c 8) + σ κ * σ (σ (c 8)) + σ (σ κ) * c 8) =
      κ * σ (c 8) + σ κ * σ (σ (c 8)) + σ (σ κ) * c 8 := by
    simp only [map_add, map_mul, hσ]
    ring
  exact ⟨⟨_, hfix⟩, fun h0 => hT (congrArg Subtype.val h0), h⟩

omit hσ in
theorem comm2 (hσ : ∀ c, σ (σ (σ c)) = c) (c₄ c₇ : K) {μ : K} (hμ : σ μ = μ) :
    xd 8 μ * (xAB σ c₄ * xH c₇) * (xd 8 μ)⁻¹ * (xAB σ c₄ * xH c₇)⁻¹ =
      ordT σ (mkT 0 (μ * c₄) 0 (μ * c₄ * σ c₄)
        (μ ^ 2 * (c₄ * σ c₄ * σ (σ c₄)) + μ * c₇) (μ * (c₄ * σ c₄ * σ (σ c₄)))) := by
  have hm : xAB σ c₄ * xH c₇ = nB K * (xA σ c₄ * xN c₇) * (nB K)⁻¹ := by
    rw [conj_mul_eq, nB_xA, nB_xN]
  have hc : xA σ c₄ * xN c₇ = ordT σ (mkT 0 c₄ 0 0 c₇ 0) := by
    rw [ordT_mkT]
    simp only [xB, xAB, xAAB, xH, map_zero, xd_zero, one_mul, mul_one]
  have e : xd 8 μ * (xAB σ c₄ * xH c₇) * (xd 8 μ)⁻¹ * (xAB σ c₄ * xH c₇)⁻¹ =
      nB K * (xB μ * (ordT σ (mkT 0 c₄ 0 0 c₇ 0) * xB μ * (ordT σ (mkT 0 c₄ 0 0 c₇ 0))⁻¹)) *
        (nB K)⁻¹ := by
    have h1 : xd 8 μ * (xAB σ c₄ * xH c₇) * (xd 8 μ)⁻¹ * (xAB σ c₄ * xH c₇)⁻¹ =
        nB K * (xB μ * (xA σ c₄ * xN c₇) * (xB μ)⁻¹ * (xA σ c₄ * xN c₇)⁻¹) * (nB K)⁻¹ := by
      rw [hm, ← nB_xB μ]
      group
    rw [h1, xB_inv' μ, ← hc]
    group
  rw [e, comm0 hσ _ hμ, ordT_mkT]
  simp only [mkT]
  rw [conj_mul_eq, conj_mul_eq, conj_mul_eq, nB_xAB, nB_xAAB, nB_xN, nB_xH]
  simp only [xB, xAB, map_zero, xd_zero, one_mul]
  unfold xA xAAB xN xH
  d4coll
  d4fin

omit [CharP K 2] in
theorem nm_fixed (a : K) :
    σ (a * σ a * σ (σ a)) = a * σ a * σ (σ a) := by
  simp only [map_mul, hσ]
  ring

theorem seven_of_nontriv (hne : ∃ a, σ a ≠ a)
    (hspan : ∀ x : K, x ∈ AddSubgroup.closure {y | ∃ e : K, σ e = e ∧ ∃ a ∈ k, y = e * a})
    (hμ : μ ≠ 0) {n : adjointGroup d4 K} (hn : n ∈ Gam σ k τ t₁ μ) (hU : n ∈ Uhat σ)
    (hact : ActsAs n (1 : SL2F)) (hne1 : n ≠ 1) :
    ∃ e : fixedField σ, e ≠ 0 ∧ xH (e : K) ∈ Gam σ k τ t₁ μ := by
  obtain ⟨c, -, hc3σ, hc7σ, rfl⟩ := exists_ordT hσ hU
  have hc0 := c0_eq_zero_of_actsAs_one hact
  have hnm : ∀ a : K, a ≠ 0 → a * σ a * σ (σ a) ≠ 0 := fun a ha =>
    mul_ne_zero (mul_ne_zero ha ((map_ne_zero σ).2 ha)) ((map_ne_zero σ).2 ((map_ne_zero σ).2 ha))
  by_cases h1 : c 1 = 0
  swap
  · exact ⟨⟨_, nm_fixed hσ (c 1)⟩, fun h => hnm _ h1 (congrArg Subtype.val h), seven_of_c1 hσ hn⟩
  by_cases h3 : c 3 = 0
  swap
  · exact ⟨⟨c 3, hc3σ⟩, fun h => h3 (congrArg Subtype.val h), seven_of_c3 hσ h1 hn⟩
  by_cases h8 : c 8 = 0
  swap
  · exact seven_of_c8 hσ hne hspan h1 h3 h8 hn
  have hform : ordT σ c = xAB σ (c 4) * xH (c 7) := by
    simp only [ordT, hc0, h1, h3, h8, xB, xA, xAAB, xN, map_zero, xd_zero, one_mul, mul_one]
  by_cases h4 : c 4 = 0
  · have hform' : ordT σ c = xH (c 7) := by
      rw [hform, h4]
      simp [xAB, xd_zero]
    refine ⟨⟨c 7, hc7σ⟩, fun h7 => hne1 ?_, by rwa [hform'] at hn⟩
    rw [hform']
    have h7' : c 7 = 0 := congrArg Subtype.val h7
    rw [h7']
    simp [xH, xd_zero]
  · rw [hform] at hn
    have hx8 : xd 8 (μ : K) ∈ Gam σ k τ t₁ μ := x8_mem_Gam
    have hm := mul_mem (mul_mem (mul_mem hx8 hn) (inv_mem hx8)) (inv_mem hn)
    rw [comm2 hσ (c 4) (c 7) μ.2] at hm
    have h7 := seven_of_c1 hσ hm
    have hc1' : (mkT (0 : K) ((μ : K) * c 4) 0 ((μ : K) * c 4 * σ (c 4))
        ((μ : K) ^ 2 * (c 4 * σ (c 4) * σ (σ (c 4))) + (μ : K) * c 7)
        ((μ : K) * (c 4 * σ (c 4) * σ (σ (c 4))))) 1 = (μ : K) * c 4 := by simp [mkT]
    rw [hc1'] at h7
    have hμc : (μ : K) * c 4 ≠ 0 := mul_ne_zero (fun h => hμ (Subtype.ext h)) h4
    exact ⟨⟨_, nm_fixed hσ ((μ : K) * c 4)⟩, fun h => hnm _ hμc (congrArg Subtype.val h), h7⟩

end Seven

section GammaFull

variable {k : Subfield K} {τ : K → fixedField σ} {t₁ μ : fixedField σ}
  [Finite K] (hσ : ∀ c, σ (σ (σ c)) = c)
  {k₂ : Subfield (fixedField σ)}
include hσ

theorem gamma_full (hne : ∃ a, σ a ≠ a)
    (hspan : ∀ x : K, x ∈ AddSubgroup.closure {y | ∃ e : K, σ e = e ∧ ∃ a ∈ k, y = e * a})
    (hk₂ : Nat.card k₂ = 2) {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    (hF : Nat.card (fixedField σ) = Nat.card k₂ ^ d) (hμ : μ ≠ 0)
    (ht : ¬ (t₁ ∈ k₂ ∧ ∀ κ ∈ k, τ κ ∈ k₂)) (a : fixedField σ) :
    xH (a : K) ∈ Gam σ k τ t₁ μ := by
  obtain ⟨n, hn, hUg, hact, hne1⟩ := exists_nontriv hσ hk₂ hd hd2 hF hμ ht
  obtain ⟨e, he, he7⟩ := seven_of_nontriv hσ hne hspan hμ hn hUg hact hne1
  by_cases ha : a = 0
  · rw [ha]
    simp only [ZeroMemClass.coe_zero, xH, xd_zero]
    exact one_mem _
  have hs : a / e ≠ 0 := div_ne_zero ha he
  obtain ⟨g, hg, hgA⟩ := (mem_lev (H := Gam σ k τ t₁ μ) (A := dgm (a / e) hs)).1
    (lev_eq_top hσ hk₂ hd hd2 hF hμ ht ▸ Subgroup.mem_top _)
  have key : g * xH (e : K) * g⁻¹ = xH (a : K) := by
    have h' := hgA ![e, 0]
    rw [dgm_mulVec] at h'
    simp only [dvv, dv, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, ZeroMemClass.coe_zero,
      xN, xd_zero, mul_one, div_mul_cancel₀ a he] at h'
    exact h'
  rw [← key]
  exact mul_mem (mul_mem hg he7) (inv_mem hg)

end GammaFull

end CFSG.RankThree.PartOne.SEITZ8
