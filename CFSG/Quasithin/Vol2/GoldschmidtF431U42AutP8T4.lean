module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8R8
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8T1
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8T2

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section Transport

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G}

omit [Finite G] in
theorem isConj_conj_self (g y : G) : IsConj (g * y * g⁻¹) y :=
  isConj_iff.2 ⟨g⁻¹, by group⟩

theorem u_conj_z (h : F55Ctx c R) : IsConj (c.iso.toG fhB * dG c) z := by
  obtain ⟨k, hk, hkL, hzk⟩ := exists_kU
  have hkA : ivA k = fhatA * dA := by
    have h1 := (ivA_spec hk).2
    have h2 : RepL (invL k) ((fhatA * dA : Ah) : P45) := by
      rw [hkL]
      exact repL_mul repL_fhat repL_dA
    exact Subtype.ext (eq_of_repL h1 h2)
  have hk' : ivG c k = c.iso.toG fhB * dG c := by
    have e : ((fhB * dB : ↥Bh) : Ah) = fhatA * dA := Subgroup.coe_mul Bh fhB dB
    have hb : ivB k = fhB * dB := Subtype.ext ((ivB_coe hk).trans (hkA.trans e.symm))
    rw [ivG, dG, ← AutIso.toG_mul, hb]
  rw [← hk']
  exact (ivG_conj_z_iff c h hk).2 hzk

theorem mem_R_of_cen (h : F55Ctx c R) {x : G} (hxF : x * c.iso.toG fhB = c.iso.toG fhB * x)
    (hxu : x * (c.iso.toG fhB * dG c) = (c.iso.toG fhB * dG c) * x) : x ∈ R := by
  refine cen_d_le_R c h x (Subgroup.mem_centralizer_singleton_iff.2 hxF) ?_
  have : c.iso.toG fhB * (x * dG c) = c.iso.toG fhB * (dG c * x) := by
    calc c.iso.toG fhB * (x * dG c) = (c.iso.toG fhB * x) * dG c := by group
      _ = (x * c.iso.toG fhB) * dG c := by rw [← hxF]
      _ = x * (c.iso.toG fhB * dG c) := by group
      _ = (c.iso.toG fhB * dG c) * x := hxu
      _ = c.iso.toG fhB * (dG c * x) := by group
  exact mul_left_cancel this

theorem exists_gR (h : F55Ctx c R) :
    ∃ g : G, g * (c.iso.toG fhB * dG c) * g⁻¹ = z ∧ ∀ x ∈ R, g * x * g⁻¹ ∈ c.iso.imgG That := by
  obtain ⟨g₀, hg₀⟩ := isConj_iff.1 (u_conj_z c h)
  set F := c.iso.toG fhB with hF
  have hRF : ∀ x ∈ R, x * F = F * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.1 (h.hR.1 hx)
  have hKM : B6.conjSub g₀ R ≤ M₁ := by
    intro y hy
    have hx : g₀⁻¹ * y * g₀ ∈ R := B6.mem_conjSub.1 hy
    have hxu : (g₀⁻¹ * y * g₀) * (F * dG c) = (F * dG c) * (g₀⁻¹ * y * g₀) := by
      have h1 : (g₀⁻¹ * y * g₀) * F = F * (g₀⁻¹ * y * g₀) := hRF _ hx
      have h2 : (g₀⁻¹ * y * g₀) * dG c = dG c * (g₀⁻¹ * y * g₀) := by
        have := dG_central c h hx
        calc (g₀⁻¹ * y * g₀) * dG c
            = ((g₀⁻¹ * y * g₀) * dG c * (g₀⁻¹ * y * g₀)⁻¹) * (g₀⁻¹ * y * g₀) := by group
          _ = dG c * (g₀⁻¹ * y * g₀) := by rw [this]
      calc (g₀⁻¹ * y * g₀) * (F * dG c) = ((g₀⁻¹ * y * g₀) * F) * dG c := by group
        _ = (F * (g₀⁻¹ * y * g₀)) * dG c := by rw [h1]
        _ = F * ((g₀⁻¹ * y * g₀) * dG c) := by group
        _ = F * (dG c * (g₀⁻¹ * y * g₀)) := by rw [h2]
        _ = (F * dG c) * (g₀⁻¹ * y * g₀) := by group
    have hyz : y * z = z * y := by
      have e1 : y * (g₀ * (F * dG c) * g₀⁻¹) = (g₀ * (F * dG c) * g₀⁻¹) * y := by
        calc y * (g₀ * (F * dG c) * g₀⁻¹)
            = g₀ * ((g₀⁻¹ * y * g₀) * (F * dG c)) * g₀⁻¹ := by group
          _ = g₀ * ((F * dG c) * (g₀⁻¹ * y * g₀)) * g₀⁻¹ := by rw [hxu]
          _ = (g₀ * (F * dG c) * g₀⁻¹) * y := by group
      rwa [hg₀] at e1
    rw [← c.cenOf_z]
    exact Subgroup.mem_centralizer_singleton_iff.2 hyz
  have hKp : IsPGroup 2 (B6.conjSub g₀ R) :=
    IsPGroup.of_card (n := 6) (by rw [conjSub_card, h.hR64])
  obtain ⟨m, hmM, hmle⟩ := F7.isSylowTwoOf_exists_conj_le (isSylowTwoOf_T₀_M₁ c h.hT₀G) hKM hKp
  have hmz : m⁻¹ * z * m = z := by
    have hm : m ∈ cenOf z := by rw [c.cenOf_z]; exact hmM
    have := Subgroup.mem_centralizer_singleton_iff.1 hm
    calc m⁻¹ * z * m = m⁻¹ * (z * m) := by group
      _ = m⁻¹ * (m * z) := by rw [this]
      _ = z := by group
  refine ⟨m⁻¹ * g₀, ?_, ?_⟩
  · calc m⁻¹ * g₀ * (F * dG c) * (m⁻¹ * g₀)⁻¹ = m⁻¹ * (g₀ * (F * dG c) * g₀⁻¹) * m := by group
      _ = z := by rw [hg₀, hmz]
  · intro x hx
    have h1 : g₀ * x * g₀⁻¹ ∈ B6.conjSub g₀ R :=
      B6.mem_conjSub.2 (by have : g₀⁻¹ * (g₀ * x * g₀⁻¹) * g₀ = x := by group
                           rw [this]; exact hx)
    have h3 : m⁻¹ * (g₀ * x * g₀⁻¹) * m ∈ c.iso.imgG That := B6.mem_conjSub.1 (hmle h1)
    have : m⁻¹ * g₀ * x * (m⁻¹ * g₀)⁻¹ = m⁻¹ * (g₀ * x * g₀⁻¹) * m := by group
    rw [this]
    exact h3

theorem mem_R_of_T₀ (h : F55Ctx c R) {g : G} (hgu : g * (c.iso.toG fhB * dG c) * g⁻¹ = z)
    {y : G} (hy : y ∈ c.iso.imgG That)
    (hyF : y * (g * c.iso.toG fhB * g⁻¹) = (g * c.iso.toG fhB * g⁻¹) * y) : g⁻¹ * y * g ∈ R := by
  set F := c.iso.toG fhB with hF
  have hyM : y ∈ M₁ := (c.iso.imgG_le That hy).1
  have hyz : y * z = z * y := by
    have hm : y ∈ cenOf z := by rw [c.cenOf_z]; exact hyM
    exact Subgroup.mem_centralizer_singleton_iff.1 hm
  have hxF : (g⁻¹ * y * g) * F = F * (g⁻¹ * y * g) := by
    calc (g⁻¹ * y * g) * F = g⁻¹ * (y * (g * F * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * F * g⁻¹) * y) * g := by rw [hyF]
      _ = F * (g⁻¹ * y * g) := by group
  have hxu : (g⁻¹ * y * g) * (F * dG c) = (F * dG c) * (g⁻¹ * y * g) := by
    calc (g⁻¹ * y * g) * (F * dG c) = g⁻¹ * (y * (g * (F * dG c) * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * (F * dG c) * g⁻¹) * y) * g := by rw [hgu, hyz]
      _ = (F * dG c) * (g⁻¹ * y * g) := by group
  exact mem_R_of_cen c h hxF hxu

end Transport

end CFSG.Quasithin.H13.F431.U42Aut
