module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Cox2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Cox1
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8R14

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42

theorem A6_order_check : ∀ g : alternatingGroup (Fin 6), g ^ 4 = 1 ∨ g ^ 3 = 1 ∨ g ^ 5 = 1 := by
  decide +kernel

theorem xd_sq : (xA * dA) * (xA * dA) = 1 :=
  eq_of_repL_eq (repL_mul (repL_mul repL_x repL_dA) (repL_mul repL_x repL_dA)) (repL_one 45)
    (by decide +kernel)

theorem isConj_of_odd_pow {H : Type*} [Group H] {s t : H} (hs : s * s = 1) (ht : t * t = 1)
    {k : ℕ} (hk : Odd k) (hw : (s * t) ^ k = 1) : IsConj s t := by
  obtain ⟨m, rfl⟩ := hk
  set w := s * t with hwdef
  have hsws : s * w * s⁻¹ = w⁻¹ := by
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
    rw [hsinv, hwdef]
    have : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    calc s * (s * t) * s = (s * s) * t * s := by group
      _ = t * s := by rw [hs, one_mul]
      _ = (s * t)⁻¹ := by rw [mul_inv_rev, ‹t⁻¹ = t›, hsinv]
  have hpow : ∀ j : ℕ, s * w ^ j * s⁻¹ = (w ^ j)⁻¹ := by
    intro j
    calc s * w ^ j * s⁻¹ = (s * w * s⁻¹) ^ j := by rw [conj_pow]
      _ = (w⁻¹) ^ j := by rw [hsws]
      _ = (w ^ j)⁻¹ := by rw [inv_pow]
  refine isConj_iff.2 ⟨w ^ m, ?_⟩
  have h1 : w ^ m * s * (w ^ m)⁻¹ = w ^ m * (s * (w ^ m)⁻¹ * s⁻¹) * s := by group
  have h2 : s * (w ^ m)⁻¹ * s⁻¹ = w ^ m := by
    have := hpow m
    have h3 : s * (w ^ m)⁻¹ * s⁻¹ = (s * w ^ m * s⁻¹)⁻¹ := by group
    rw [h3, this, inv_inv]
  rw [h1, h2]
  have h4 : w ^ m * w ^ m = w⁻¹ := by
    have : w ^ (2 * m + 1) = 1 := hw
    rw [← pow_add]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    convert this using 2
    ring
  calc w ^ m * w ^ m * s = w⁻¹ * s := by rw [h4]
    _ = t := by
      rw [hwdef, mul_inv_rev]
      have : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
      have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
      rw [this, hsinv]
      calc t * s * s = t * (s * s) := by group
        _ = t := by rw [hs, mul_one]

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section Cox

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G}

@[expose] def cxSP : ↥P1h := ⟨cxS, cxS_mem_P1h⟩

@[expose] def cxTP : ↥P2h := ⟨cxT, cxT_mem_P2h⟩

theorem w_mem_oddCl :
    c.iso.toG1 cxSP * c.iso.toG2 cxTP ∈ oddCl (cenOf (c.iso.toG fhB)) := by
  obtain ⟨α, hα, u, hu, hsdec⟩ := cxS_dec
  obtain ⟨u₁, hu₁, i, hi, u₂, hu₂, htdec⟩ := cxT_dec
  have hcs : cxS = xA * (α * u) := by
    calc cxS = xA * (xA * cxS) := by rw [← mul_assoc, xA_sq, one_mul]
      _ = xA * (α * u) := by rw [hsdec]
  have hct : cxT = (xA * dA) * (u₁ * bA ^ i * u₂) := by
    calc cxT = ((xA * dA) * (xA * dA)) * cxT := by rw [xd_sq, one_mul]
      _ = (xA * dA) * (xA * dA * cxT) := by group
      _ = (xA * dA) * (u₁ * bA ^ i * u₂) := by rw [htdec]
  have hαP : α ∈ P1h := (Alt1h_le_C1 hα).1
  set αP : ↥P1h := ⟨α, hαP⟩ with hαPdef
  set uB : ↥Bh := ⟨u, Uh_le_Bh hu⟩ with huB
  set u₁B : ↥Bh := ⟨u₁, Uh_le_Bh hu₁⟩ with hu₁B
  set u₂B : ↥Bh := ⟨u₂, Uh_le_Bh hu₂⟩ with hu₂B
  have e1 : cxSP = Subgroup.inclusion Bh_le_P1h xB * (αP * Subgroup.inclusion Bh_le_P1h uB) :=
    Subtype.ext hcs
  have e2 : cxTP = Subgroup.inclusion Bh_le_P2h (xB * dB) *
      (Subgroup.inclusion Bh_le_P2h u₁B * bP2 ^ i * Subgroup.inclusion Bh_le_P2h u₂B) :=
    Subtype.ext hct
  have hxz : c.iso.toG xB = z := c.iso.toG_xB c.z2 c.z1 c.zc
  have hs' : c.iso.toG1 cxSP = z * (c.iso.toG1 αP * c.iso.toG uB) := by
    rw [e1, map_mul, map_mul, c.iso.toG1_inclusion, c.iso.toG1_inclusion, hxz]
  have ht' : c.iso.toG2 cxTP =
      (z * dG c) * (c.iso.toG u₁B * b2G c ^ i * c.iso.toG u₂B) := by
    rw [e2]
    simp only [map_mul, map_pow, c.iso.toG2_inclusion, hxz]
    rfl
  have hαM : c.iso.toG1 αP ∈ M₁ := toG1_mem c αP
  have huM : c.iso.toG uB ∈ M₁ := ((c.iso.imgG_le Uh) (c.iso.mem_imgG.2 ⟨uB, hu, rfl⟩)).1
  have hzcomm : ∀ g ∈ M₁, g * z = z * g := fun g hg => by
    have : g ∈ cenOf z := by rw [c.cenOf_z]; exact hg
    exact Subgroup.mem_centralizer_singleton_iff.1 this
  have hz2 : z * z = 1 := by rw [← pow_two]; exact c.z2
  have hw : c.iso.toG1 cxSP * c.iso.toG2 cxTP =
      (c.iso.toG1 αP * c.iso.toG uB) * dG c *
        (c.iso.toG u₁B * b2G c ^ i * c.iso.toG u₂B) := by
    have hc1 : (c.iso.toG1 αP * c.iso.toG uB) * z = z * (c.iso.toG1 αP * c.iso.toG uB) :=
      hzcomm _ (M₁.mul_mem hαM huM)
    rw [hs', ht']
    set P := c.iso.toG1 αP * c.iso.toG uB with hP
    set A := c.iso.toG u₁B * b2G c ^ i * c.iso.toG u₂B with hA
    calc z * P * (z * dG c * A) = (z * P) * z * dG c * A := by group
      _ = (P * z) * z * dG c * A := by rw [hc1]
      _ = P * (z * z) * dG c * A := by group
      _ = P * dG c * A := by rw [hz2, mul_one]
  rw [hw]
  have hUO : ∀ g ∈ UG c, g ∈ oddCl (cenOf (c.iso.toG fhB)) := fun g hg => UG_le_oddCl c hg
  have hαO : c.iso.toG1 αP ∈ oddCl (cenOf (c.iso.toG fhB)) := by
    have : c.iso.toG1 αP ∈ B1G c := (mem_B1G_iff c).2 ⟨αP, hα, rfl⟩
    rw [B1G_eq_oddCl] at this
    exact oddCl_mono (E1G_le_cen c) this
  have hb2O : b2G c ∈ oddCl (cenOf (c.iso.toG fhB)) :=
    mem_oddCl_of_pow_three (Subgroup.mem_centralizer_singleton_iff.2 (b2G_comm_F c)) (b2G_cube c)
  have hmemU : ∀ v : ↥Bh, (v : Ah) ∈ Uh → c.iso.toG v ∈ oddCl (cenOf (c.iso.toG fhB)) :=
    fun v hv => hUO _ (c.iso.mem_imgG.2 ⟨v, hv, rfl⟩)
  refine mul_mem (mul_mem (mul_mem hαO (hmemU uB hu)) (hUO _ (dG_mem_UG c))) ?_
  exact mul_mem (mul_mem (hmemU u₁B hu₁) ((oddCl _).pow_mem hb2O i)) (hmemU u₂B hu₂)

theorem coxRel_of_A6 (h : F55Ctx c R) {Q : Subgroup ↥(cenOf (c.iso.toG fhB))}
    (hQc : Q = Subgroup.closure {x : ↥(cenOf (c.iso.toG fhB)) | Odd (orderOf x)})
    (e : ↥Q ≃* alternatingGroup (Fin 6)) :
    (c.iso.toG1 cxSP * c.iso.toG2 cxTP) ^ 4 = 1 := by
  have hs2 : c.iso.toG1 cxSP * c.iso.toG1 cxSP = 1 := by
    rw [← map_mul, show cxSP * cxSP = 1 from Subtype.ext cxS_sq, map_one]
  have ht2 : c.iso.toG2 cxTP * c.iso.toG2 cxTP = 1 := by
    rw [← map_mul, show cxTP * cxTP = 1 from Subtype.ext cxT_sq, map_one]
  have hs : IsConj (c.iso.toG1 cxSP) z := conj_z_of_nfix13 c h (Subtype.ext cxS_sq) nfix_sA
  have ht : IsConj (c.iso.toG2 cxTP) (c.iso.toG fhB) :=
    conj_F_of_nfix5 c h (Subtype.ext cxT_sq) nfix_tA
  set w := c.iso.toG1 cxSP * c.iso.toG2 cxTP with hw
  obtain ⟨hwc, hwq⟩ := oddCl_subtype (H := cenOf (c.iso.toG fhB)) (w_mem_oddCl c)
  have hwQ : (⟨w, hwc⟩ : ↥(cenOf (c.iso.toG fhB))) ∈ Q := by rw [hQc]; exact hwq
  set q : ↥Q := ⟨⟨w, hwc⟩, hwQ⟩ with hq
  have hpow : ∀ n : ℕ, e q ^ n = 1 → w ^ n = 1 := by
    intro n hn
    have h1 : q ^ n = 1 := e.injective (by rw [map_pow, hn, map_one])
    have h2 := congrArg (fun x : ↥Q => ((x : ↥(cenOf (c.iso.toG fhB))) : G)) h1
    simpa using h2
  have hnc : ∀ k : ℕ, Odd k → w ^ k = 1 → False := by
    intro k hk hwk
    have hconj := isConj_of_odd_pow hs2 ht2 hk hwk
    exact h.hnc ((hs.symm.trans hconj).trans ht).symm
  rcases A6_order_check (e q) with h4 | h3 | h5
  · exact hpow 4 h4
  · exact (hnc 3 (by decide) (hpow 3 h3)).elim
  · exact (hnc 5 (by decide) (hpow 5 h5)).elim

end Cox

end CFSG.Quasithin.H13.F431.U42Aut
