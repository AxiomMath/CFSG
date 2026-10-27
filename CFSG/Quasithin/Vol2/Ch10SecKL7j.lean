module

public import CFSG.Quasithin.Vol2.Ch10SecKL7i
public import CFSG.Quasithin.Vol2.Ch10SecKL7h

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KL7

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

variable {W : Type} [CommGroup W]

namespace Hyp

variable {Mb L₁ L₂ R : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W} {τ : MulAut W}
variable (h : Hyp Mb L₁ L₂ W₁ W₂ τ) (hR : RHyp Mb L₁ L₂ R)
include h hR

theorem eq_one_of_odd {a b c : MulAut W} (ha : a ∈ L₁) (hb : b ∈ L₂) (hc : c ∈ CM Mb L₁ L₂)
    {m : ℕ} (hm : Odd m) (hxm : (a * b * c) ^ m = 1)
    (hcd : rkIdx (fixV (Subgroup.zpowers (a * b * c))) ≤ 4) : a * b * c = 1 := by
  obtain ⟨c₁⟩ := h.coord
  obtain ⟨c₂⟩ := h.swap.coord
  have hW := h.card_W
  rw [h.decomp_pow ha hb hc] at hxm
  obtain ⟨ham, hbm, hcm⟩ :=
    h.decomp_eq_one (pow_mem ha m) (pow_mem hb m) (pow_mem hc m) hxm
  by_cases hc1 : c = 1
  · subst hc1
    rw [mul_one] at hcd ⊢
    set γ₁ := c₁.π.symm ⟨a, ha⟩
    set γ₂ := c₂.π.symm ⟨b, hb⟩
    have hab : a * b = ((c₁.π γ₁ : ↥L₁) : MulAut W) * ((c₂.π γ₂ : ↥L₂) : MulAut W) := by
      rw [c₁.coe_π_symm, c₂.coe_π_symm]
    rw [hab, h.rkIdx_L₀ c₁ c₂] at hcd
    have hodd₁ : Odd (orderOf γ₁) :=
      hm.of_dvd_nat (by rw [c₁.orderOf_π_symm]; exact orderOf_dvd_of_pow_eq_one ham)
    have hodd₂ : Odd (orderOf γ₂) :=
      hm.of_dvd_nat (by rw [c₂.orderOf_π_symm]; exact orderOf_dvd_of_pow_eq_one hbm)
    have hγ₁ : γ₁ = 1 := by
      by_contra hne
      have := cdM_ge_two hne hodd₁
      omega
    have hγ₂ : γ₂ = 1 := by
      by_contra hne
      have := cdM_ge_two hne hodd₂
      omega
    rw [hab, hγ₁, hγ₂, map_one, map_one]
    rfl
  · exfalso
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hcR : c ∈ R := hR.odd c hc (hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hcm))
    have hc5 : orderOf c = 5 := orderOf_eq_prime (hR.pow5 c hcR) hc1
    have hr : orderOf (a * b) ∣ 168 :=
      (Commute.orderOf_mul_dvd_lcm (h.comm' ha hb)).trans
        (Nat.lcm_dvd (c₁.orderOf_dvd ha) (c₂.orderOf_dvd hb))
    have hxr : (a * b * c) ^ orderOf (a * b) = c ^ orderOf (a * b) := by
      have hcomm : Commute a b := h.comm' ha hb
      rw [h.decomp_pow ha hb hc, ← hcomm.mul_pow, pow_orderOf_eq_one, one_mul]
    have hcr1 : c ^ orderOf (a * b) ≠ 1 := by
      intro h0
      have h5 := orderOf_dvd_of_pow_eq_one h0
      rw [hc5] at h5
      have := h5.trans hr
      norm_num at this
    have h12 := RHyp.le_rkIdx h hR (pow_mem hcR _) hcr1
    have hle := rkIdx_fixV_pow_le hW (a * b * c) (orderOf (a * b))
    rw [hxr] at hle
    omega

theorem eq_one_of_two {a b c : MulAut W} (ha : a ∈ L₁) (hb : b ∈ L₂) (hc : c ∈ CM Mb L₁ L₂)
    {e : ℕ} (hxe : (a * b * c) ^ 2 ^ e = 1)
    (hcd : rkIdx (fixV (Subgroup.zpowers (a * b * c))) ≤ 4) : c = 1 := by
  have hW := h.card_W
  by_contra hc1
  rw [h.decomp_pow ha hb hc] at hxe
  have hce : c ^ 2 ^ e = 1 :=
    (h.decomp_eq_one (pow_mem ha _) (pow_mem hb _) (pow_mem hc _) hxe).2.2
  obtain ⟨z, hzR, hz⟩ : ∃ z ∈ R, c * z ≠ z * c := by
    by_contra hall
    exact hc1 (RHyp.eq_one h hR hc hce fun r hr => by
      by_contra hne
      exact hall ⟨r, hr, hne⟩)
  have hw : c * z * c⁻¹ ∈ R := hR.normal c hc.1 z hzR
  obtain ⟨-, hwa, hwb⟩ := Hyp.mem_C_iff.1 (hR.le hw)
  have hxz : a * b * c * z * (a * b * c)⁻¹ = c * z * c⁻¹ := by
    have e1 := hwa a ha
    have e2 := hwb b hb
    calc a * b * c * z * (a * b * c)⁻¹ = a * (b * (c * z * c⁻¹)) * b⁻¹ * a⁻¹ := by group
      _ = a * ((c * z * c⁻¹) * b) * b⁻¹ * a⁻¹ := by rw [e2]
      _ = a * (c * z * c⁻¹) * a⁻¹ := by group
      _ = (c * z * c⁻¹) * a * a⁻¹ := by rw [e1]
      _ = c * z * c⁻¹ := by group
  have hyR : c * z * c⁻¹ * z⁻¹ ∈ R := mul_mem hw (R.inv_mem hzR)
  have hy1 : c * z * c⁻¹ * z⁻¹ ≠ 1 := by
    intro h0
    apply hz
    calc c * z = c * z * c⁻¹ * z⁻¹ * (z * c) := by group
      _ = z * c := by rw [h0, one_mul]
  have h12 := RHyp.le_rkIdx h hR hyR hy1
  have hy : c * z * c⁻¹ * z⁻¹ = (a * b * c) * (z * (a * b * c)⁻¹ * z⁻¹) := by
    rw [← hxz]
    group
  have h1 := rkIdx_fixV_mul_le hW (a * b * c) (z * (a * b * c)⁻¹ * z⁻¹)
  rw [← hy, rkIdx_fixV_conj, rkIdx_fixV_inv] at h1
  omega

theorem classify {x : MulAut W} (hx : x ∈ Mb) (hx1 : x ≠ 1)
    (hcd : rkIdx (fixV (Subgroup.zpowers x)) ≤ 4) :
    x ^ 2 = 1 ∧ rkIdx (fixV (Subgroup.zpowers x)) = 4 ∧
      ((x ∈ L₁ ∧ W₂ ≤ fixV (Subgroup.zpowers x)) ∨ (x ∈ L₂ ∧ W₁ ≤ fixV (Subgroup.zpowers x))) := by
  have := h.finite_aut
  obtain ⟨c₁⟩ := h.coord
  obtain ⟨c₂⟩ := h.swap.coord
  have hW := h.card_W
  have hK : L₁.map (MulAut.conj x).toMonoidHom = L₁ := by
    rcases h.map_conj_eq hx with h1 | h1
    · exact h1
    · exact absurd (h.le_rkIdx_of_swap hx h1) (by omega)
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := h.exists_decomp hx hK
  obtain ⟨e, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (a * b * c)).ne'
  have hm1 : m = 1 := by
    by_contra hm1
    have hx'm : ((a * b * c) ^ 2 ^ e) ^ m = 1 := by rw [← pow_mul, ← hn, pow_orderOf_eq_one]
    have hx'1 : (a * b * c) ^ 2 ^ e ≠ 1 := by
      intro h0
      have h2 := orderOf_dvd_of_pow_eq_one h0
      rw [hn] at h2
      have h3 : m ∣ 1 := Nat.dvd_of_mul_dvd_mul_left (pow_pos two_pos e) (by simpa using h2)
      exact hm1 (Nat.dvd_one.1 h3)
    rw [h.decomp_pow ha hb hc] at hx'm hx'1
    have hcd' : rkIdx (fixV (Subgroup.zpowers (a ^ 2 ^ e * b ^ 2 ^ e * c ^ 2 ^ e))) ≤ 4 := by
      rw [← h.decomp_pow ha hb hc]
      exact (rkIdx_fixV_pow_le hW _ _).trans hcd
    exact hx'1 (h.eq_one_of_odd hR (pow_mem ha _) (pow_mem hb _) (pow_mem hc _) hm hx'm hcd')
  subst hm1
  rw [mul_one] at hn
  have hxe : (a * b * c) ^ 2 ^ e = 1 := by rw [← hn, pow_orderOf_eq_one]
  have hc1 : c = 1 := h.eq_one_of_two hR ha hb hc hxe hcd
  subst hc1
  rw [mul_one] at hcd hx1 ⊢
  set γ₁ := c₁.π.symm ⟨a, ha⟩
  set γ₂ := c₂.π.symm ⟨b, hb⟩
  have hab : a * b = ((c₁.π γ₁ : ↥L₁) : MulAut W) * ((c₂.π γ₂ : ↥L₂) : MulAut W) := by
    rw [c₁.coe_π_symm, c₂.coe_π_symm]
  have hcdab := h.rkIdx_L₀ c₁ c₂ γ₁ γ₂
  rw [← hab] at hcdab
  rw [hcdab] at hcd ⊢
  have ha' : a = ((c₁.π γ₁ : ↥L₁) : MulAut W) := (c₁.coe_π_symm ha).symm
  have hb' : b = ((c₂.π γ₂ : ↥L₂) : MulAut W) := (c₂.coe_π_symm hb).symm
  rcases (show (cdM γ₁ = 0 ∧ cdM γ₂ = 0) ∨ (cdM γ₁ = 1 ∧ cdM γ₂ = 0) ∨
      (cdM γ₁ = 0 ∧ cdM γ₂ = 1) by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exfalso
    apply hx1
    rw [hab, eq_one_of_cdM_eq_zero γ₁ h1, eq_one_of_cdM_eq_zero γ₂ h2, map_one, map_one]
    rfl
  · have hb1 : b = 1 := by rw [hb', eq_one_of_cdM_eq_zero γ₂ h2, map_one]; rfl
    subst hb1
    rw [mul_one]
    refine ⟨?_, by omega, Or.inl ⟨ha, fun w hw => mem_fixV_zp.2 (h.fix₁ a ha w hw)⟩⟩
    rw [ha', ← Subgroup.coe_pow, ← map_pow, sq_eq_one_of_cdM_eq_one γ₁ h1, map_one]
    rfl
  · have ha1 : a = 1 := by rw [ha', eq_one_of_cdM_eq_zero γ₁ h1, map_one]; rfl
    subst ha1
    rw [one_mul]
    refine ⟨?_, by omega, Or.inr ⟨hb, fun w hw => mem_fixV_zp.2 (h.fix₂ b hb w hw)⟩⟩
    rw [hb', ← Subgroup.coe_pow, ← map_pow, sq_eq_one_of_cdM_eq_one γ₂ h2, map_one]
    rfl

end Hyp

end CFSG.Quasithin.Vol2.Ch10.SecB.KL7
