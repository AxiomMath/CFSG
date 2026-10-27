module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8R10
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8T6

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section Alg

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G} {ρ : G}

theorem F_mem_TfG : c.iso.toG fhB ∈ TfG c :=
  ⟨c.iso.mem_imgG.2 ⟨fhB, fhatA_mem_That, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

theorem F_mem_Eg : c.iso.toG fhB ∈ Eg c := TfG_le_Eg c (F_mem_TfG c)

theorem z_mem_Eg : z ∈ Eg c := TfG_le_Eg c (z_mem_TfG c)

theorem UG_le_Eg : UG c ≤ Eg c := (UG_le_TfG c).trans (TfG_le_Eg c)

theorem zF_comm : z * c.iso.toG fhB = c.iso.toG fhB * z :=
  Subgroup.mem_centralizer_singleton_iff.1 (z_mem_TfG c).2

theorem z_mul_rho (h : F55Ctx c R) (hr : RhoCtx c R ρ) :
    z * ρ = ρ * z * c.iso.toG fhB := by
  set F := c.iso.toG fhB with hF
  have hρF : ρ * F = F * ρ := Subgroup.mem_centralizer_singleton_iff.1 (h.hR.1 hr.mem.1)
  have hzF : z * F = F * z := zF_comm c
  have hA : ρ * z = F * z * ρ := by
    have := hr.conj_z h
    calc ρ * z = (ρ * z * ρ⁻¹) * ρ := by group
      _ = F * z * ρ := by rw [this]
  have hF2 : F * F = 1 := F_sq c.iso
  calc z * ρ = (F * F) * (z * ρ) := by rw [hF2]; group
    _ = F * (F * z * ρ) := by group
    _ = F * (ρ * z) := by rw [← hA]
    _ = (F * ρ) * z := by group
    _ = (ρ * F) * z := by rw [hρF]
    _ = ρ * (F * z) := by group
    _ = ρ * (z * F) := by rw [hzF]
    _ = ρ * z * F := by group

theorem rho_mul_z (h : F55Ctx c R) (hr : RhoCtx c R ρ) :
    ρ * z = z * ρ * c.iso.toG fhB := by
  have h1 := z_mul_rho c h hr
  have hF2 : c.iso.toG fhB * c.iso.toG fhB = 1 := F_sq c.iso
  calc ρ * z = ρ * z * (c.iso.toG fhB * c.iso.toG fhB) := by rw [hF2]; group
    _ = (ρ * z * c.iso.toG fhB) * c.iso.toG fhB := by group
    _ = z * ρ * c.iso.toG fhB := by rw [← h1]

theorem r_sq (h : F55Ctx c R) (hr : RhoCtx c R ρ) : (z * ρ) * (z * ρ) = 1 := by
  set F := c.iso.toG fhB with hF
  have hρF : ρ * F = F * ρ := Subgroup.mem_centralizer_singleton_iff.1 (h.hR.1 hr.mem.1)
  have hz2 : z * z = 1 := by simpa [pow_two] using c.z2
  have h1 := rho_mul_z c h hr
  calc (z * ρ) * (z * ρ) = z * (ρ * z) * ρ := by group
    _ = z * (z * ρ * F) * ρ := by rw [h1]
    _ = (z * z) * ρ * (F * ρ) := by group
    _ = ρ * (F * ρ) := by rw [hz2]; group
    _ = F * (ρ * ρ) := by
        calc ρ * (F * ρ) = (ρ * F) * ρ := by group
          _ = (F * ρ) * ρ := by rw [hρF]
          _ = F * (ρ * ρ) := by group
    _ = 1 := by rw [hr.sq]; exact F_sq c.iso

theorem z_conj_r (h : F55Ctx c R) (hr : RhoCtx c R ρ) :
    z * (z * ρ) * z⁻¹ = (z * ρ) * c.iso.toG fhB := by
  have hz2 : z * z = 1 := by simpa [pow_two] using c.z2
  have h1 := rho_mul_z c h hr
  calc z * (z * ρ) * z⁻¹ = (z * z) * ρ * z⁻¹ := by group
    _ = ρ * z⁻¹ := by rw [hz2]; group
    _ = ρ * z := by
        have : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
        rw [this]
    _ = (z * ρ) * c.iso.toG fhB := h1

end Alg

section Index

variable (c : AutCtx G M₁ M₂ z)

theorem mul_mem_Eg_iff (hE : Nat.card ↥(Eg c) = 1440)
    (hX : Nat.card ↥(cenOf (c.iso.toG fhB)) = 2880) {a b : G}
    (ha : a ∈ cenOf (c.iso.toG fhB)) (hb : b ∈ cenOf (c.iso.toG fhB)) :
    a * b ∈ Eg c ↔ (a ∈ Eg c ↔ b ∈ Eg c) := by
  have hidx : ((Eg c).subgroupOf (cenOf (c.iso.toG fhB))).index = 2 := by
    have h1 := Subgroup.card_mul_index ((Eg c).subgroupOf (cenOf (c.iso.toG fhB)))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Eg_le_cen c)).toEquiv, hE, hX] at h1
    omega
  have := Subgroup.mul_mem_iff_of_index_two hidx
    (a := (⟨a, ha⟩ : ↥(cenOf (c.iso.toG fhB)))) (b := ⟨b, hb⟩)
  simpa [Subgroup.mem_subgroupOf] using this

end Index

end CFSG.Quasithin.H13.F431.U42Aut
