module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8R13
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Cr3

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

theorem oddCl_subtype {G : Type*} [Group G] {H : Subgroup G} {y : G} (hy : y ∈ oddCl H) :
    ∃ hy' : y ∈ H, (⟨y, hy'⟩ : ↥H) ∈ Subgroup.closure {x : ↥H | Odd (orderOf x)} := by
  unfold oddCl at hy
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    refine ⟨hx.1, Subgroup.subset_closure ?_⟩
    have h1 : orderOf (⟨x, hx.1⟩ : ↥H) = orderOf x := Subgroup.orderOf_mk x hx.1
    show Odd (orderOf (⟨x, hx.1⟩ : ↥H))
    rw [h1]
    exact hx.2
  | one => exact ⟨H.one_mem, (Subgroup.closure _).one_mem⟩
  | mul x y _ _ hx hy =>
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    exact ⟨H.mul_mem hx1 hy1, (Subgroup.closure _).mul_mem hx2 hy2⟩
  | inv x _ hx =>
    obtain ⟨hx1, hx2⟩ := hx
    exact ⟨H.inv_mem hx1, (Subgroup.closure _).inv_mem hx2⟩

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

omit [Finite G] in
theorem Erho_le_R (R : Subgroup G) (ρ : G) : Erho R ρ ≤ R := inf_le_left

section Wrap

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G} {ρ : G}

theorem UG_le_cen : UG c ≤ cenOf (c.iso.toG fhB) := (UG_le_TfG c).trans (TfG_le_cen c)

theorem exists_Q (h : F55Ctx c R) (hr : RhoCtx c R ρ) :
    ∃ Q : Subgroup ↥(cenOf (c.iso.toG fhB)), Q.Normal ∧ Q.index = 8 ∧
      R.subgroupOf (cenOf (c.iso.toG fhB)) ⊓ Q = (UG c).subgroupOf (cenOf (c.iso.toG fhB)) ∧
      Q = Subgroup.closure {x : ↥(cenOf (c.iso.toG fhB)) | Odd (orderOf x)} := by
  set F := c.iso.toG fhB with hF
  have hRX : R ≤ cenOf F := h.hR.1
  have hTX : TfG c ≤ cenOf F := TfG_le_cen c
  have hEX : Erho R ρ ≤ cenOf F := (Erho_le_R R ρ).trans hRX
  have hUX : UG c ≤ cenOf F := UG_le_cen c
  set m := (R.subgroupOf (cenOf F)).index with hm
  have hcR : Nat.card ↥(R.subgroupOf (cenOf F)) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRX).toEquiv, h.hR64]
    norm_num
  have hX : Nat.card ↥(cenOf F) = 64 * m := by
    have := Subgroup.card_mul_index (R.subgroupOf (cenOf F))
    rw [hcR] at this
    exact this.symm
  have hm2 : Odd m := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h.hR.2.2)
  have hR2 : IsPGroup 2 ↥(R.subgroupOf (cenOf F)) :=
    IsPGroup.of_card (n := 6) (by rw [hcR]; norm_num)
  have hTi : ((TfG c).subgroupOf (cenOf F)).relIndex (R.subgroupOf (cenOf F)) = 2 := by
    rw [Subgroup.relIndex_subgroupOf hRX]
    exact Tf_relIndex c h.hTR h.hR64
  have hEi : ((Erho R ρ).subgroupOf (cenOf F)).relIndex (R.subgroupOf (cenOf F)) = 2 := by
    rw [Subgroup.relIndex_subgroupOf hRX]
    exact (hr.card_Erho h).2
  have hFmem : F ∈ cenOf F := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hρX : ρ ∈ cenOf F := hRX hr.mem.1
  have hzX : z ∈ cenOf F := hRX (z_mem_R c h)
  set f' : ↥(cenOf F) := ⟨F, hFmem⟩ with hf'
  set ρ' : ↥(cenOf F) := ⟨ρ, hρX⟩ with hρ'
  set z' : ↥(cenOf F) := ⟨z, hzX⟩ with hz'
  have hfc : ∀ x : ↥(cenOf F), x * f' = f' * x := fun x =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 x.2)
  have hf2 : f' ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using F_sq c.iso)
  have hρR : ρ' ∈ R.subgroupOf (cenOf F) := hr.mem.1
  have hρ2 : ρ' ^ 2 = f' := Subtype.ext (by simpa [pow_two] using hr.sq)
  have hzR : z' ∈ R.subgroupOf (cenOf F) := z_mem_R c h
  have hz2 : z' ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using c.z2)
  have hρz : ρ' * z' * ρ'⁻¹ = f' * z' := Subtype.ext (hr.conj_z h)
  have hUR : (UG c).subgroupOf (cenOf F) ≤ R.subgroupOf (cenOf F) := fun u hu => UG_le_R c h hu
  have hU8 : Nat.card ↥((UG c).subgroupOf (cenOf F)) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUX).toEquiv, card_UG c]
  have hfU : f' ∉ (UG c).subgroupOf (cenOf F) := F_not_mem_UG c
  have hUodd : (UG c).subgroupOf (cenOf F) ≤
      Subgroup.closure {x : ↥(cenOf F) | Odd (orderOf x)} := by
    intro u hu
    obtain ⟨hu', hu''⟩ := oddCl_subtype (H := cenOf F) (UG_le_oddCl c hu)
    exact hu''
  have nf1 : ∀ a : ↥(cenOf F), a⁻¹ * ρ' * a ∉ (TfG c).subgroupOf (cenOf F) := by
    intro a ha
    have ha' : (a : G)⁻¹ * ρ * a ∈ TfG c := ha
    apply TfG_sq_ne_F c ha'
    have haF : (a : G) * F = F * a := Subgroup.mem_centralizer_singleton_iff.1 a.2
    calc (a : G)⁻¹ * ρ * a * ((a : G)⁻¹ * ρ * a) = (a : G)⁻¹ * (ρ * ρ) * a := by group
      _ = (a : G)⁻¹ * F * a := by rw [hr.sq]
      _ = F := by
        calc (a : G)⁻¹ * F * a = (a : G)⁻¹ * (F * a) := by group
          _ = (a : G)⁻¹ * (a * F) := by rw [haF]
          _ = F := by group
  have hzF : z ≠ F := by
    intro hzF
    exact h.hnc (isConj_iff.2 ⟨1, by rw [one_mul, inv_one, mul_one]; exact hzF.symm⟩)
  have hb1z : b1G c * z = z * b1G c := by
    have : b1G c ∈ cenOf z := by rw [c.cenOf_z]; exact (B1G_le_E1G c (b1G_mem_B1G c)).1
    exact Subgroup.mem_centralizer_singleton_iff.1 this
  have nf2 : ∀ a : ↥(cenOf F), a⁻¹ * z' * a ∉ (Erho R ρ).subgroupOf (cenOf F) := by
    intro a ha
    exact nf_core c h hr (w := z) (by simpa [pow_two] using c.z2) c.z1 hzF hb1z a.2 ha
  have hρT : ρ ∉ TfG c := hr.not_mem_Tf
  have hzT : z ∈ TfG c := z_mem_TfG c
  have hF2 : F * F = 1 := F_sq c.iso
  have hz2' : z * z = 1 := by simpa [pow_two] using c.z2
  have hzFc : z * F = F * z := Subgroup.mem_centralizer_singleton_iff.1 hzT.2
  have hFT : F ∈ TfG c :=
    ⟨c.iso.mem_imgG.2 ⟨fhB, fhatA_mem_That, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hρz2 : (ρ * z) * (ρ * z) = 1 := by
    have h1 := hr.conj_z h
    calc (ρ * z) * (ρ * z) = (ρ * z * ρ⁻¹) * (ρ * ρ) * z := by group
      _ = (F * z) * F * z := by rw [h1, hr.sq]
      _ = F * (z * F) * z := by group
      _ = F * (F * z) * z := by rw [hzFc]
      _ = (F * F) * (z * z) := by group
      _ = 1 := by rw [hF2, hz2', one_mul]
  have hρz1 : ρ * z ≠ 1 := by
    intro h1
    apply hρT
    have : ρ = z⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact (TfG c).inv_mem hzT
  have hρzF : ρ * z ≠ F := by
    intro h1
    apply hρT
    have : ρ = F * z⁻¹ := by
      calc ρ = (ρ * z) * z⁻¹ := by group
        _ = F * z⁻¹ := by rw [h1]
    rw [this]
    exact (TfG c).mul_mem hFT ((TfG c).inv_mem hzT)
  have hρb : b1G c * ρ = ρ * b1G c := Subgroup.mem_centralizer_iff.1 hr.mem.2 (b1G c)
    (b1G_mem_B1G c)
  have hb1ρz : b1G c * (ρ * z) = (ρ * z) * b1G c := by
    calc b1G c * (ρ * z) = (b1G c * ρ) * z := by group
      _ = (ρ * b1G c) * z := by rw [hρb]
      _ = ρ * (b1G c * z) := by group
      _ = ρ * (z * b1G c) := by rw [hb1z]
      _ = (ρ * z) * b1G c := by group
  have nf3 : ∀ a : ↥(cenOf F), a⁻¹ * (ρ' * z') * a ∉ (Erho R ρ).subgroupOf (cenOf F) := by
    intro a ha
    exact nf_core c h hr (w := ρ * z) hρz2 hρz1 hρzF hb1ρz a.2 ha
  exact exists_normal_index_eight (R.subgroupOf (cenOf F)) ((TfG c).subgroupOf (cenOf F))
    ((Erho R ρ).subgroupOf (cenOf F)) ((UG c).subgroupOf (cenOf F)) f' ρ' z' m hX hm2 hR2 hcR
    hTi hEi hfc hf2 hρR hρ2 hzR hz2 hρz hUR hU8 hfU hUodd nf1 nf2 nf3

end Wrap

end CFSG.Quasithin.H13.F431.U42Aut
