module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8R12
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8R10

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

theorem oddCl_mono {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K) : oddCl H ≤ oddCl K :=
  Subgroup.closure_mono fun _ hy => ⟨h hy.1, hy.2⟩

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section Nf

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G}

theorem b1G_ne_one : b1G c ≠ 1 := by
  intro h
  have h1 : b1P = 1 := c.iso.toG1_injective (by rw [b1G] at h; rw [h, map_one])
  have h2 : b1A = 1 := congrArg (fun x : ↥P1h => (x : Ah)) h1
  have hrl : RepL b1L ((b1A : Ah) : P45) := repL_b1A
  rw [h2] at hrl
  exact b1_check.2.2.2.1 (repL_unique hrl (repL_one 45))

theorem UG_le_oddCl : UG c ≤ oddCl (cenOf (c.iso.toG fhB)) := by
  intro u hu
  obtain ⟨b, hb, rfl⟩ := c.iso.mem_imgG.1 hu
  obtain ⟨k, hk, l, hl, hbkl⟩ := Uh_prod b hb
  have hkb : (k : Ah) ∈ Bh := Kl1h_le_Bh hk
  have hlb : (l : Ah) ∈ Bh := B1h_le_Bh hl
  have hbe : b = ⟨k, hkb⟩ * ⟨l, hlb⟩ := Subtype.ext hbkl
  rw [hbe, AutIso.toG_mul]
  refine mul_mem ?_ ?_
  · have h1 : c.iso.toG ⟨k, hkb⟩ ∈ B1G c :=
      V1G_le_B1G c (c.iso.mem_imgG.2 ⟨⟨k, hkb⟩, hk, rfl⟩)
    rw [B1G_eq_oddCl] at h1
    exact oddCl_mono (E1G_le_cen c) h1
  · obtain ⟨κ, hκ, hl'⟩ := B1h_comm l hl
    have hκb : (κ : Ah) ∈ Bh := B1h_le_Bh hκ
    have hκf : κ * fhatA = fhatA * κ := A2h_comm (B1h_le_A2h hκ) F_mem_A2h
    set x := c.iso.toG ⟨κ, hκb⟩ with hx
    have hxF : x * c.iso.toG fhB = c.iso.toG fhB * x := by
      rw [hx, ← AutIso.toG_mul, ← AutIso.toG_mul]
      exact congrArg c.iso.toG (Subtype.ext hκf)
    have e : c.iso.toG ⟨l, hlb⟩ = b2G c * (x * (b2G c)⁻¹ * x⁻¹) := by
      have hP : Subgroup.inclusion Bh_le_P2h ⟨l, hlb⟩ =
          bP2 * Subgroup.inclusion Bh_le_P2h ⟨κ, hκb⟩ * bP2⁻¹ *
            (Subgroup.inclusion Bh_le_P2h ⟨κ, hκb⟩)⁻¹ := Subtype.ext hl'
      have := congrArg c.iso.toG2 hP
      rw [c.iso.toG2_inclusion, map_mul, map_mul, map_mul, map_inv, map_inv,
        c.iso.toG2_inclusion] at this
      rw [this, b2G, hx]
      group
    rw [e]
    refine mul_mem (mem_oddCl_of_pow_three ?_ (b2G_cube c)) (mem_oddCl_of_pow_three ?_ ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (b2G_comm_F c)
    · have hb2 : b2G c ∈ cenOf (c.iso.toG fhB) :=
        Subgroup.mem_centralizer_singleton_iff.2 (b2G_comm_F c)
      have hxc : x ∈ cenOf (c.iso.toG fhB) := Subgroup.mem_centralizer_singleton_iff.2 hxF
      exact (cenOf _).mul_mem ((cenOf _).mul_mem hxc ((cenOf _).inv_mem hb2))
        ((cenOf _).inv_mem hxc)
    · rw [conj_pow, inv_pow, b2G_cube c]
      group

theorem nf_core (h : F55Ctx c R) {ρ : G} (hr : RhoCtx c R ρ) {w : G} (hw2 : w * w = 1)
    (hw1 : w ≠ 1) (hwF : w ≠ c.iso.toG fhB) (hb : b1G c * w = w * b1G c) {a : G}
    (ha : a ∈ cenOf (c.iso.toG fhB)) : a⁻¹ * w * a ∉ Erho R ρ := by
  intro hy
  set F := c.iso.toG fhB with hF
  have haF : a * F = F * a := Subgroup.mem_centralizer_singleton_iff.1 ha
  have hyy : a⁻¹ * w * a * (a⁻¹ * w * a) = 1 := by
    calc a⁻¹ * w * a * (a⁻¹ * w * a) = a⁻¹ * (w * w) * a := by group
      _ = 1 := by rw [hw2]; group
  obtain ⟨u, hu, hu2, hyu⟩ := hr.E_invol h hy hyy
  by_cases hu1 : u = 1
  · subst hu1
    rcases hyu with h1 | h1
    · apply hw1
      calc w = a * (a⁻¹ * w * a) * a⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · apply hwF
      calc w = a * (a⁻¹ * w * a) * a⁻¹ := by group
        _ = a * (F * 1) * a⁻¹ := by rw [h1]
        _ = F := by
          calc a * (F * 1) * a⁻¹ = (a * F) * a⁻¹ := by group
            _ = (F * a) * a⁻¹ := by rw [haF]
            _ = F := by group
  · obtain ⟨x, hx0, hxu⟩ := U_fusion c hu hu2 hu1
    have hx : x ∈ cenOf F := oddCl_le _ hx0
    have hxF : x * F = F * x := Subgroup.mem_centralizer_singleton_iff.1 hx
    set g := x * a⁻¹ with hg
    have hgc : g ∈ cenOf F := (cenOf F).mul_mem hx ((cenOf F).inv_mem ha)
    have hgF : g * F = F * g := Subgroup.mem_centralizer_singleton_iff.1 hgc
    have hgw : g * w * g⁻¹ = dG c ∨ g * w * g⁻¹ = F * dG c := by
      have e : g * w * g⁻¹ = x * (a⁻¹ * w * a) * x⁻¹ := by rw [hg]; group
      rcases hyu with h1 | h1
      · left
        rw [e, h1, hxu]
      · right
        rw [e, h1]
        calc x * (F * u) * x⁻¹ = (x * F) * u * x⁻¹ := by group
          _ = F * x * u * x⁻¹ := by rw [hxF]
          _ = F * (x * u * x⁻¹) := by group
          _ = F * dG c := by rw [hxu]
    have hb1F : b1G c * F = F * b1G c := b1G_comm_F c
    have hb1c : b1G c ∈ cenOf F := Subgroup.mem_centralizer_singleton_iff.2 hb1F
    have hb' : g * b1G c * g⁻¹ ∈ cenOf F :=
      (cenOf F).mul_mem ((cenOf F).mul_mem hgc hb1c) ((cenOf F).inv_mem hgc)
    have hcomm : (g * b1G c * g⁻¹) * (g * w * g⁻¹) = (g * w * g⁻¹) * (g * b1G c * g⁻¹) := by
      calc (g * b1G c * g⁻¹) * (g * w * g⁻¹) = g * (b1G c * w) * g⁻¹ := by group
        _ = g * (w * b1G c) * g⁻¹ := by rw [hb]
        _ = (g * w * g⁻¹) * (g * b1G c * g⁻¹) := by group
    have hbd : (g * b1G c * g⁻¹) * dG c = dG c * (g * b1G c * g⁻¹) := by
      have hbF : (g * b1G c * g⁻¹) * F = F * (g * b1G c * g⁻¹) :=
        Subgroup.mem_centralizer_singleton_iff.1 hb'
      rcases hgw with h1 | h1
      · rw [h1] at hcomm
        exact hcomm
      · rw [h1] at hcomm
        have h2 : F * ((g * b1G c * g⁻¹) * dG c) = F * (dG c * (g * b1G c * g⁻¹)) := by
          calc F * ((g * b1G c * g⁻¹) * dG c) = (F * (g * b1G c * g⁻¹)) * dG c := by group
            _ = ((g * b1G c * g⁻¹) * F) * dG c := by rw [hbF]
            _ = (g * b1G c * g⁻¹) * (F * dG c) := by group
            _ = (F * dG c) * (g * b1G c * g⁻¹) := hcomm
            _ = F * (dG c * (g * b1G c * g⁻¹)) := by group
        exact mul_left_cancel h2
    have hbR : g * b1G c * g⁻¹ ∈ R := cen_d_le_R c h _ hb' hbd
    have hb3 : (g * b1G c * g⁻¹) ^ 3 = 1 := by
      rw [conj_pow, b1G_cube c]
      group
    have hb1 : g * b1G c * g⁻¹ ≠ 1 := by
      intro h1
      apply b1G_ne_one c
      calc b1G c = g⁻¹ * (g * b1G c * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    have hord : orderOf (g * b1G c * g⁻¹) = 3 := orderOf_eq_prime hb3 hb1
    have hdvd := Subgroup.orderOf_dvd_natCard R hbR
    rw [hord, h.hR64] at hdvd
    norm_num at hdvd

end Nf

end CFSG.Quasithin.H13.F431.U42Aut
