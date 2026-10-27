module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Q1
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8R14
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Rec

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section Recog

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G}

theorem dG_sq : dG c * dG c = 1 := by
  have : dB * dB = 1 := Subtype.ext dA_sq
  rw [dG, ← AutIso.toG_mul, this, AutIso.toG_one]

theorem Q_recog
    (h : F55Ctx c R) {Q : Subgroup ↥(cenOf (c.iso.toG fhB))} (hQi : Q.index = 8)
    (hQR : R.subgroupOf (cenOf (c.iso.toG fhB)) ⊓ Q =
      (UG c).subgroupOf (cenOf (c.iso.toG fhB)))
    (hQc : Q = Subgroup.closure {x : ↥(cenOf (c.iso.toG fhB)) | Odd (orderOf x)}) :
    Nonempty (↥Q ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      Nonempty (↥Q ≃* alternatingGroup (Fin 6)) := by
  have hRX : R ≤ cenOf (c.iso.toG fhB) := h.hR.1
  have hUX : UG c ≤ cenOf (c.iso.toG fhB) := UG_le_cen c
  set m := (R.subgroupOf (cenOf (c.iso.toG fhB))).index with hm
  have hcR : Nat.card ↥(R.subgroupOf (cenOf (c.iso.toG fhB))) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRX).toEquiv, h.hR64]
    norm_num
  have hX : Nat.card ↥(cenOf (c.iso.toG fhB)) = 64 * m := by
    have := Subgroup.card_mul_index (R.subgroupOf (cenOf (c.iso.toG fhB)))
    rw [hcR] at this
    exact this.symm
  have hm2 : Odd m := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h.hR.2.2)
  have hQcard : Nat.card ↥Q = 8 * m := by
    have := Subgroup.card_mul_index Q
    rw [hQi, hX] at this
    omega
  have hdU : dG c ∈ UG c := dG_mem_UG c
  have hdX : dG c ∈ cenOf (c.iso.toG fhB) := hUX hdU
  set d' : ↥(cenOf (c.iso.toG fhB)) := ⟨dG c, hdX⟩ with hd'
  have hUQ : (UG c).subgroupOf (cenOf (c.iso.toG fhB)) ≤ Q := by
    rw [← hQR]
    exact inf_le_right
  have hU8 : Nat.card ↥((UG c).subgroupOf (cenOf (c.iso.toG fhB))) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUX).toEquiv, card_UG c]
  have hd2 : d' ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using dG_sq c)
  have hd1 : d' ≠ 1 := fun h1 => dG_ne_one c (congrArg Subtype.val h1)
  have hdc : ∀ x ∈ (UG c).subgroupOf (cenOf (c.iso.toG fhB)), x * d' = d' * x := by
    intro x hx
    have hxR : (x : G) ∈ R := UG_le_R c h hx
    have := dG_central c h hxR
    refine Subtype.ext ?_
    calc (x : G) * dG c = ((x : G) * dG c * (x : G)⁻¹) * x := by group
      _ = dG c * x := by rw [this]
  have hcen : ∀ x ∈ Q, x * d' = d' * x → x ∈ (UG c).subgroupOf (cenOf (c.iso.toG fhB)) := by
    intro x hxQ hxd
    have hxR : (x : G) ∈ R := cen_d_le_R c h x x.2 (congrArg Subtype.val hxd)
    rw [← hQR]
    exact ⟨hxR, hxQ⟩
  have hconj : ∀ y ∈ (UG c).subgroupOf (cenOf (c.iso.toG fhB)), y ^ 2 = 1 → y ≠ 1 →
      ∃ q ∈ Q, q * d' * q⁻¹ = y := by
    intro y hy hy2 hy1
    have hy2' : (y : G) * y = 1 := by simpa [pow_two] using congrArg Subtype.val hy2
    have hy1' : (y : G) ≠ 1 := fun h1 => hy1 (Subtype.ext h1)
    obtain ⟨x, hx, hxy0⟩ := U_fusion c hy hy2' hy1'
    have hxy : x * (y : G) * x⁻¹ = dG c := hxy0
    obtain ⟨hxc, hxQ⟩ := oddCl_subtype (H := cenOf (c.iso.toG fhB)) hx
    refine ⟨⟨x, hxc⟩⁻¹, ?_, ?_⟩
    · rw [hQc]
      exact (Subgroup.closure _).inv_mem hxQ
    · refine Subtype.ext ?_
      calc ((⟨x, hxc⟩⁻¹ : ↥(cenOf (c.iso.toG fhB))) : G) * dG c *
            ((⟨x, hxc⟩⁻¹ : ↥(cenOf (c.iso.toG fhB))) : G)⁻¹ = x⁻¹ * dG c * x := by simp
        _ = x⁻¹ * (x * (y : G) * x⁻¹) * x := by rw [hxy]
        _ = y := by group
  obtain ⟨hUD⟩ := UG_equiv_D8 c
  have hUD' : Nonempty (↥((UG c).subgroupOf (cenOf (c.iso.toG fhB))) ≃* DihedralGroup 4) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hUX).trans hUD⟩
  exact psl3_two_or_alt_six_of_sylow Q ((UG c).subgroupOf (cenOf (c.iso.toG fhB))) d' m hQcard
    hm2 hUQ hU8 hdU hd2 hd1 hdc hcen hconj hUD'

end Recog

end CFSG.Quasithin.H13.F431.U42Aut
