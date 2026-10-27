module

public import CFSG.Quasithin.EmptyFaithful.S153OfourFacts

public section

namespace CFSG.Quasithin

namespace Gap6

open S1417

section Fixed

variable {W : Type*} [CommGroup W] {X L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W}

theorem _root_.CFSG.Quasithin.OfourStruct.fix_free₂ (h : OfourStruct X L₁ L₂ t) {ℓ : MulAut W}
    (hℓ : ℓ ∈ L₂) (h3 : ℓ ^ 3 = 1) (h1 : ℓ ≠ 1) {b : W} (hb : b ∈ commV L₂) (hfix : ℓ b = b) :
    b = 1 := by
  by_contra hb1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho : orderOf ℓ = 3 := orderOf_eq_prime h3 h1
  exact h1 (eq_one_of_odd_of_fixed h.nat₂ (fun l hl u hu => commV_stable L₂ hl hu) hℓ
    (by rw [ho]; decide) hb hb1 hfix)

theorem _root_.CFSG.Quasithin.OfourStruct.norm_eq_one₂ (h : OfourStruct X L₁ L₂ t) {ℓ : MulAut W}
    (hℓ : ℓ ∈ L₂) (h3 : ℓ ^ 3 = 1) (h1 : ℓ ≠ 1) {b : W} (hb : b ∈ commV L₂) :
    b * ℓ b * ℓ (ℓ b) = 1 := by
  have hb1 : ℓ b ∈ commV L₂ := commV_stable L₂ hℓ hb
  have hb2 : ℓ (ℓ b) ∈ commV L₂ := commV_stable L₂ hℓ hb1
  have hcube : ℓ (ℓ (ℓ b)) = b := by
    have := congrArg (fun φ : MulAut W => φ b) h3
    simpa [pow_succ, MulAut.mul_apply] using this
  refine h.fix_free₂ hℓ h3 h1 ((commV L₂).mul_mem ((commV L₂).mul_mem hb hb1) hb2) ?_
  rw [map_mul, map_mul, hcube, mul_comm _ b, ← mul_assoc]

theorem _root_.CFSG.Quasithin.OfourStruct.mem_commV₁_of_fix (h : OfourStruct X L₁ L₂ t)
    {ℓ : MulAut W} (hℓ : ℓ ∈ L₂) (h3 : ℓ ^ 3 = 1) (h1 : ℓ ≠ 1) {w : W} (hw : ℓ w = w) :
    w ∈ commV L₁ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_decomp_W w
  have hla : ℓ a = a := h.L₂_fix₁ hℓ ha
  rw [map_mul, hla] at hw
  have hlb : ℓ b = b := mul_left_cancel hw
  have hb1 : b = 1 := h.fix_free₂ hℓ h3 h1 hb hlb
  rw [hb1, mul_one]
  exact ha

theorem _root_.CFSG.Quasithin.OfourStruct.mem_commV₂_of_norm (h : OfourStruct X L₁ L₂ t)
    (hW : ∀ w : W, w * w = 1) {ℓ : MulAut W} (hℓ : ℓ ∈ L₂) (h3 : ℓ ^ 3 = 1) (h1 : ℓ ≠ 1) {w : W}
    (hw : w * ℓ w * ℓ (ℓ w) = 1) : w ∈ commV L₂ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_decomp_W w
  have hla : ℓ a = a := h.L₂_fix₁ hℓ ha
  have hnb := h.norm_eq_one₂ hℓ h3 h1 hb
  have e : a * b * ℓ (a * b) * ℓ (ℓ (a * b)) = (a * a * a) * (b * ℓ b * ℓ (ℓ b)) := by
    rw [map_mul, map_mul, hla, hla]
    simp only [mul_assoc, mul_comm, mul_left_comm]
  rw [e, hnb, mul_one, hW a, one_mul] at hw
  rw [hw, one_mul]
  exact hb

end Fixed

section Main

variable {W M Γ : Type*} [CommGroup W] [CommGroup M] [Group Γ]

theorem apply_mul_inv_mem_commV
    (hM : ∀ m : M, m * m = 1) (ι : W →* M) (hι : Function.Injective ι)
    (α : Γ →* MulAut M) (ρ : Γ →* MulAut W)
    (hρα : ∀ g w, ι (ρ g w) = α g (ι w))
    (hgen : ∀ g m, α g m * m⁻¹ ∈ ι.range)
    (hker : ∀ g, ρ g = 1 → α g = 1)
    {L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W} (hO : OfourStruct ρ.range L₁ L₂ t)
    {g : Γ} (hg : ρ g ∈ L₁) (m : M) :
    ∃ a ∈ commV L₁, α g m * m⁻¹ = ι a := by
  have hW : ∀ w : W, w * w = 1 := fun w => hι (by rw [map_mul, map_one]; exact hM _)
  obtain ⟨ℓ, hℓL, hℓ3, hℓ1⟩ := exists_orderThree hO.nat₂
  obtain ⟨y, hy⟩ : ℓ ∈ ρ.range := hO.L₂_le hℓL
  have hy3 : ∀ m : M, α y (α y (α y m)) = m := by
    intro m
    have h1 : ρ (y ^ 3) = 1 := by rw [map_pow, hy, hℓ3]
    have h2 := hker _ h1
    have := congrArg (fun φ : MulAut M => φ m) h2
    simpa [map_pow, pow_succ, MulAut.mul_apply] using this
  set m1 : M := α y m with hm1
  set m2 : M := α y m1 with hm2
  set n : M := m * m1 * m2 with hn
  set c : M := m1 * m2 with hc
  have hinv : ∀ x : M, x⁻¹ * x⁻¹ = 1 := fun x => by rw [← mul_inv_rev, hM x, inv_one]
  have hmn : m = n * c := by
    have : n * c = m * (m1 * m1) * (m2 * m2) := by
      simp only [hn, hc, mul_comm, mul_left_comm]
    rw [this, hM m1, hM m2, mul_one, mul_one]
  have hnfix : α y n = n := by
    have : α y n = m1 * m2 * m := by
      rw [hn, map_mul, map_mul, ← hm1, ← hm2, hy3]
    rw [this, hn]
    simp only [mul_comm, mul_left_comm]
  have hcrange : c ∈ ι.range := by
    have e : c = (m1 * m⁻¹) * (m2 * m⁻¹) := by
      have : (m1 * m⁻¹) * (m2 * m⁻¹) = m1 * m2 * (m⁻¹ * m⁻¹) := by
        simp only [mul_assoc, mul_comm, mul_left_comm]
      rw [this, hinv, mul_one]
    rw [e]
    refine ι.range.mul_mem (hgen y m) ?_
    have : m2 = α (y * y) m := by rw [hm2, hm1, map_mul, MulAut.mul_apply]
    rw [this]
    exact hgen (y * y) m
  obtain ⟨wc, hwc⟩ := hcrange
  have hcnorm : c * α y c * α y (α y c) = 1 := by
    have e1 : α y c = m2 * m := by rw [hc, map_mul, ← hm2, hy3]
    have e2 : α y (α y c) = m * m1 := by rw [e1, map_mul, hy3, ← hm1]
    rw [e2, e1, hc]
    have : m1 * m2 * (m2 * m) * (m * m1) = (m * m) * (m1 * m1) * (m2 * m2) := by
      simp only [mul_assoc, mul_comm, mul_left_comm]
    rw [this, hM m, hM m1, hM m2, one_mul, one_mul]
  have hℓwc : ι (ℓ wc) = α y c := by
    have := hρα y wc
    rw [hy, hwc] at this
    exact this
  have hℓℓwc : ι (ℓ (ℓ wc)) = α y (α y c) := by
    have := hρα y (ℓ wc)
    rw [hy, hℓwc] at this
    exact this
  have hwcB : wc ∈ commV L₂ := by
    refine hO.mem_commV₂_of_norm hW hℓL hℓ3 hℓ1 (hι ?_)
    rw [map_mul, map_mul, map_one, hwc, hℓwc, hℓℓwc]
    exact hcnorm
  have hgc : α g c = c := by
    rw [← hwc, ← hρα, hO.L₁_fix₂ hg hwcB]
  have hgm : α g m * m⁻¹ = α g n * n⁻¹ := by
    have h1 : α g m = α g n * c := by
      conv_lhs => rw [hmn]
      rw [map_mul, hgc]
    have e : α g n * c * (n * c)⁻¹ = α g n * n⁻¹ * (c * c⁻¹) := by
      simp only [mul_inv, mul_assoc, mul_comm, mul_left_comm]
    rw [h1]
    conv_lhs => rw [hmn]
    rw [e, mul_inv_cancel, mul_one]
  obtain ⟨wd, hwd⟩ := hgen g n
  have hcomm : α (y * g) = α (g * y) := by
    have h1 : ρ (y * g * (g * y)⁻¹) = 1 := by
      simp only [map_mul, map_inv, hy]
      rw [hO.comm (ρ g) hg ℓ hℓL, mul_inv_cancel]
    have h2 := hker _ h1
    rw [map_mul, map_inv] at h2
    exact mul_inv_eq_one.mp h2
  have hyd : α y (α g n * n⁻¹) = α g n * n⁻¹ := by
    have e : α y (α g n) = α g n := by
      have := congrArg (fun φ : MulAut M => φ n) hcomm
      simp only [map_mul, MulAut.mul_apply] at this
      rw [this, hnfix]
    rw [map_mul, map_inv, e, hnfix]
  have hwdfix : ℓ wd = wd := by
    apply hι
    have := hρα y wd
    rw [hy, hwd, hyd] at this
    rw [this, hwd]
  refine ⟨wd, hO.mem_commV₁_of_fix hℓL hℓ3 hℓ1 hwdfix, ?_⟩
  rw [hgm, hwd]

end Main

end Gap6

end CFSG.Quasithin
