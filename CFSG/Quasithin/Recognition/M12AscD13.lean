module

public import Certificates.Certificate17018


public section

namespace CFSG.Quasithin

open Subgroup Equiv

open CFSG.GH74.M12 (Asc03Hyp)

variable {G : Type*} [Group G] {z : G}

theorem W1_ok : ∀ σ ∈ W1, Equiv.Perm.sign σ = 1 ∧ NormDb σ = true :=
  Certificates.certificate17018.1

theorem W2_ok : ∀ σ ∈ W2, Equiv.Perm.sign σ = 1 ∧ NormEb σ = true :=
  Certificates.certificate17018.2.1

set_option maxRecDepth 100000 in
theorem KP_D : ∀ σ : Perm (Fin 6), Equiv.Perm.sign σ = 1 → NormDb σ = true → InKP (actD σ) :=
  Certificates.certificate17018.2.2.1

set_option maxRecDepth 100000 in
theorem KP_E : ∀ σ : Perm (Fin 6), Equiv.Perm.sign σ = 1 → NormEb σ = true → InKP (actE σ) :=
  Certificates.certificate17018.2.2.2.1

set_option maxRecDepth 100000 in
theorem KP_mem1 : ∀ σ ∈ W1, (actD σ).1 ∈ D6l ∧ (actD σ).2 ∈ D6l ∧
    (actD σ).1 * ((actD σ).2 * (actD σ).2) ∈ D6l :=
  Certificates.certificate17018.2.2.2.2.1

set_option maxRecDepth 100000 in
theorem KP_mem2 : ∀ σ ∈ W2, (actE σ).1 ∈ D6l ∧ (actE σ).2 ∈ D6l ∧
    (actE σ).1 * ((actE σ).2 * (actE σ).2) ∈ D6l :=
  Certificates.certificate17018.2.2.2.2.2.1

set_option maxRecDepth 100000 in
theorem KP_conj1 : ∀ σ ∈ W1,
    InKP (fAct x6 bv (actD σ).1, fAct x6 bv ((actD σ).1 * ((actD σ).2 * (actD σ).2))) :=
  Certificates.certificate17018.2.2.2.2.2.2.1

set_option maxRecDepth 100000 in
theorem KP_conj2 : ∀ σ ∈ W2,
    InKP (fAct x6 bv (actE σ).1, fAct x6 bv ((actE σ).1 * ((actE σ).2 * (actE σ).2))) :=
  Certificates.certificate17018.2.2.2.2.2.2.2.1

set_option maxRecDepth 100000 in
theorem KP_not_v : ¬ InKP (x6, bv) :=
  Certificates.certificate17018.2.2.2.2.2.2.2.2.1

theorem KP_mem {p : Perm (Fin 6) × Perm (Fin 6)} (hp : InKP p) :
    p.1 ∈ D6l ∧ p.2 ∈ D6l ∧ p.1 * (p.2 * p.2) ∈ D6l := by
  rcases hp with ⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩
  · exact KP_mem1 σ hσ
  · exact KP_mem2 σ hσ

theorem KP_conj {p : Perm (Fin 6) × Perm (Fin 6)} (hp : InKP p) :
    InKP (fAct x6 bv p.1, fAct x6 bv (p.1 * (p.2 * p.2))) := by
  rcases hp with ⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩
  · exact KP_conj1 σ hσ
  · exact KP_conj2 σ hσ

theorem outerAlpha_x6 : outerAlpha x6 = ax6 := by
  unfold x6 ax6
  rw [map_mul]
  exact congrArg₂ (· * ·) (outerAlpha_gen 4) (outerAlpha_gen 3)

theorem outerAlpha_x16 : outerAlpha x16 = ax16 := by
  unfold x16 ax16
  rw [map_mul]
  exact congrArg₂ (· * ·) (outerAlpha_gen 1) (outerAlpha_gen 0)

theorem D6_sign_norm : ∀ d ∈ D6l, Equiv.Perm.sign d = 1 ∧ NormDb d = true :=
  Certificates.certificate17018.2.2.2.2.2.2.2.2.2

namespace OuterData

variable {m : AscModel z} {c : AscCox m} {y : G}

theorem act_rho_x6 (σ : Perm (Fin 6)) :
    c.ρ σ * c.ρ x6 * (c.ρ σ)⁻¹ = c.ρ (actD σ).1 := by
  simp only [actD, map_mul, map_inv]

theorem act_rho_x16 (σ : Perm (Fin 6)) :
    c.ρ σ * c.ρ x16 * (c.ρ σ)⁻¹ = c.ρ (actD σ).2 := by
  simp only [actD, map_mul, map_inv]

theorem act_rhoy_x6 (h : OuterData c y) (σ : Perm (Fin 6)) :
    (c.ρ σ * y) * c.ρ x6 * (c.ρ σ * y)⁻¹ = c.ρ (actE σ).1 := by
  have := h.conj_rho x6
  rw [outerAlpha_x6] at this
  calc (c.ρ σ * y) * c.ρ x6 * (c.ρ σ * y)⁻¹ = c.ρ σ * (y * c.ρ x6 * y⁻¹) * (c.ρ σ)⁻¹ := by group
    _ = c.ρ (actE σ).1 := by rw [this]; simp only [actE, map_mul, map_inv]

theorem act_rhoy_x16 (h : OuterData c y) (σ : Perm (Fin 6)) :
    (c.ρ σ * y) * c.ρ x16 * (c.ρ σ * y)⁻¹ = c.ρ (actE σ).2 := by
  have := h.conj_rho x16
  rw [outerAlpha_x16] at this
  calc (c.ρ σ * y) * c.ρ x16 * (c.ρ σ * y)⁻¹ = c.ρ σ * (y * c.ρ x16 * y⁻¹) * (c.ρ σ)⁻¹ := by group
    _ = c.ρ (actE σ).2 := by rw [this]; simp only [actE, map_mul, map_inv]

theorem D_le_K
    (h : OuterData c y) : c.D ≤ h.K := by
  intro g hg
  obtain ⟨d, hd, rfl⟩ := (AscCox.mem_D c).1 hg
  have := D6_sign_norm d hd
  exact (h.rho_mem_K d).2 this

theorem K_act
    (h : OuterData c y) {k : G} (hk : k ∈ h.K) :
    ∃ p, InKP p ∧ k * c.ρ x6 * k⁻¹ = c.ρ p.1 ∧ k * c.ρ x16 * k⁻¹ = c.ρ p.2 := by
  obtain ⟨hkL, hkN⟩ := hk
  obtain ⟨σ, hσ, rfl | rfl⟩ := hkL
  · have hN := (c.rho_mem_normalizer σ).1 hkN
    exact ⟨actD σ, KP_D σ hσ hN, act_rho_x6 σ, act_rho_x16 σ⟩
  · have hN := (h.rhoy_mem_normalizer σ).1 hkN
    exact ⟨actE σ, KP_E σ hσ hN, h.act_rhoy_x6 σ, h.act_rhoy_x16 σ⟩

theorem K_real
    (h : OuterData c y) {p : Perm (Fin 6) × Perm (Fin 6)} (hp : InKP p) :
    ∃ k ∈ h.K, k * c.ρ x6 * k⁻¹ = c.ρ p.1 ∧ k * c.ρ x16 * k⁻¹ = c.ρ p.2 := by
  rcases hp with ⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩
  · obtain ⟨hs, hN⟩ := W1_ok σ hσ
    exact ⟨c.ρ σ, (h.rho_mem_K σ).2 ⟨hs, hN⟩, act_rho_x6 σ, act_rho_x16 σ⟩
  · obtain ⟨hs, hN⟩ := W2_ok σ hσ
    exact ⟨c.ρ σ * y, (h.rhoy_mem_K σ).2 ⟨hs, hN⟩, h.act_rhoy_x6 σ, h.act_rhoy_x16 σ⟩

end OuterData

namespace AscCox

variable {m : AscModel z} (c : AscCox m)

theorem VData.normalizes_K
    [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z)
    (h27 : 27 ∣ Nat.card G) {y : G} (h : OuterData c y) {v : G} (hv : VData c v) :
    ∀ k ∈ h.K, v * k * v⁻¹ ∈ h.K := by
  intro k hk
  obtain ⟨p, hp, hkx, hkx1⟩ := h.K_act hk
  obtain ⟨ha, hb, hab⟩ := KP_mem hp
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv.sq
  have hF : ∀ d ∈ D6l, v * c.ρ d * v⁻¹ = c.ρ (fAct x6 bv d) := fun d hd =>
    c.conj_fAct hv.act_x hv.act_x1 hd
  have e1 : (v * k * v⁻¹) * c.ρ x6 * (v * k * v⁻¹)⁻¹ = c.ρ (fAct x6 bv p.1) := by
    calc (v * k * v⁻¹) * c.ρ x6 * (v * k * v⁻¹)⁻¹
        = v * (k * (v⁻¹ * c.ρ x6 * v) * k⁻¹) * v⁻¹ := by group
      _ = v * (k * (v * c.ρ x6 * v⁻¹) * k⁻¹) * v⁻¹ := by rw [hvi]
      _ = v * (k * c.ρ x6 * k⁻¹) * v⁻¹ := by rw [hv.act_x]
      _ = v * c.ρ p.1 * v⁻¹ := by rw [hkx]
      _ = c.ρ (fAct x6 bv p.1) := hF _ ha
  have e2 : (v * k * v⁻¹) * c.ρ x16 * (v * k * v⁻¹)⁻¹ =
      c.ρ (fAct x6 bv (p.1 * (p.2 * p.2))) := by
    have hbv : k * c.ρ bv * k⁻¹ = c.ρ (p.1 * (p.2 * p.2)) := by
      have : c.ρ bv = c.ρ x6 * (c.ρ x16 * c.ρ x16) := by
        simp only [bv, map_mul]
      calc k * c.ρ bv * k⁻¹ = (k * c.ρ x6 * k⁻¹) * ((k * c.ρ x16 * k⁻¹) * (k * c.ρ x16 * k⁻¹)) := by
            rw [this]; group
        _ = c.ρ (p.1 * (p.2 * p.2)) := by rw [hkx, hkx1, map_mul, map_mul]
    calc (v * k * v⁻¹) * c.ρ x16 * (v * k * v⁻¹)⁻¹
        = v * (k * (v⁻¹ * c.ρ x16 * v) * k⁻¹) * v⁻¹ := by group
      _ = v * (k * (v * c.ρ x16 * v⁻¹) * k⁻¹) * v⁻¹ := by rw [hvi]
      _ = v * (k * c.ρ bv * k⁻¹) * v⁻¹ := by rw [hv.act_x1]
      _ = v * c.ρ (p.1 * (p.2 * p.2)) * v⁻¹ := by rw [hbv]
      _ = c.ρ (fAct x6 bv (p.1 * (p.2 * p.2))) := hF _ hab
  obtain ⟨k', hk'K, hk'x, hk'x1⟩ := h.K_real (KP_conj hp)
  have hc1 : (k'⁻¹ * (v * k * v⁻¹)) * m.ψ mX = m.ψ mX * (k'⁻¹ * (v * k * v⁻¹)) := by
    have e : (v * k * v⁻¹) * c.ρ x6 * (v * k * v⁻¹)⁻¹ = k' * c.ρ x6 * k'⁻¹ := by
      rw [e1, hk'x]
    rw [← c.rho_x6]
    calc (k'⁻¹ * (v * k * v⁻¹)) * c.ρ x6
        = k'⁻¹ * (((v * k * v⁻¹) * c.ρ x6 * (v * k * v⁻¹)⁻¹) * (v * k * v⁻¹)) := by group
      _ = k'⁻¹ * ((k' * c.ρ x6 * k'⁻¹) * (v * k * v⁻¹)) := by rw [e]
      _ = c.ρ x6 * (k'⁻¹ * (v * k * v⁻¹)) := by group
  have hc2 : (k'⁻¹ * (v * k * v⁻¹)) * c.x1 = c.x1 * (k'⁻¹ * (v * k * v⁻¹)) := by
    have e : (v * k * v⁻¹) * c.ρ x16 * (v * k * v⁻¹)⁻¹ = k' * c.ρ x16 * k'⁻¹ := by
      rw [e2, hk'x1]
    rw [← c.rho_x16]
    calc (k'⁻¹ * (v * k * v⁻¹)) * c.ρ x16
        = k'⁻¹ * (((v * k * v⁻¹) * c.ρ x16 * (v * k * v⁻¹)⁻¹) * (v * k * v⁻¹)) := by group
      _ = k'⁻¹ * ((k' * c.ρ x16 * k'⁻¹) * (v * k * v⁻¹)) := by rw [e]
      _ = c.ρ x16 * (k'⁻¹ * (v * k * v⁻¹)) := by group
  have hmemD : k'⁻¹ * (v * k * v⁻¹) ∈ c.D :=
    c.centralizer_D_le hyp h27 h ((mem_C c).2 ((c.centralizes_D_iff).2 ⟨hc1, hc2⟩))
  have hmemK : k'⁻¹ * (v * k * v⁻¹) ∈ h.K := h.D_le_K hmemD
  have := h.K.mul_mem hk'K hmemK
  simpa using this

theorem VData.not_mem_L
    {y : G} (h : OuterData c y) {v : G} (hv : VData c v) : v ∉ h.L := by
  intro hvL
  have hvK : v ∈ h.K := ⟨hvL, hv.mem_N⟩
  obtain ⟨p, hp, hpx, hpx1⟩ := h.K_act hvK
  have h1 : p.1 = x6 := c.ρ_inj (by rw [← hpx, hv.act_x])
  have h2 : p.2 = bv := c.ρ_inj (by rw [← hpx1, hv.act_x1])
  apply KP_not_v
  have : p = (x6, bv) := Prod.ext h1 h2
  rw [← this]
  exact hp

end AscCox

end CFSG.Quasithin
