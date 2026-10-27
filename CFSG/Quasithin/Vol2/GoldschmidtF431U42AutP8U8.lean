module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8U7
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8U6

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431

theorem conj_pres {G : Type} [Group G] {F e s ρ : G}
    (hρe : ρ * e * ρ⁻¹ = e ∨ ρ * e * ρ⁻¹ = e * F) (hρs : ρ * s * ρ⁻¹ = s * F)
    (hFe : e * F = F * e) (hFs : s * F = F * s) :
    ρ * (e * s * e⁻¹) * ρ⁻¹ = (e * s * e⁻¹) * F := by
  have hFe' : F * e⁻¹ = e⁻¹ * F := by
    calc F * e⁻¹ = e⁻¹ * (e * F) * e⁻¹ := by group
      _ = e⁻¹ * (F * e) * e⁻¹ := by rw [hFe]
      _ = e⁻¹ * F := by group
  have h0 : ρ * (e * s * e⁻¹) * ρ⁻¹ = (ρ * e * ρ⁻¹) * (ρ * s * ρ⁻¹) * (ρ * e * ρ⁻¹)⁻¹ := by group
  rw [h0]
  rcases hρe with h1 | h1
  · rw [h1, hρs]
    calc e * (s * F) * e⁻¹ = e * s * (F * e⁻¹) := by group
      _ = e * s * (e⁻¹ * F) := by rw [hFe']
      _ = (e * s * e⁻¹) * F := by group
  · rw [h1, hρs]
    calc e * F * (s * F) * (e * F)⁻¹ = e * (F * s) * e⁻¹ := by group
      _ = e * (s * F) * e⁻¹ := by rw [hFs]
      _ = e * s * (F * e⁻¹) := by group
      _ = e * s * (e⁻¹ * F) := by rw [hFe']
      _ = (e * s * e⁻¹) * F := by group

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section Five

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G} {ρ : G}

theorem rho_five (h : F55Ctx c R) (hr : RhoCtx c R ρ) (hρE : ρ ∉ Eg c)
    (hE : Nat.card ↥(Eg c) = 1440) (hX : Nat.card ↥(cenOf (c.iso.toG fhB)) = 2880)
    (qd : QData c) (hρQ : ∀ q ∈ oddCl (cenOf (c.iso.toG fhB)), ρ * q = q * ρ)
    (ι : Ah ≃* ↥(M₁ ⊔ M₂)) (h1 : ∀ x : P1h, (ι (x : Ah) : G) = (c.iso.phi1 x : G)) :
    ∀ a ∈ [p10sA 0, p10sA 2, p10sA 4, p10sA 5, p10tA],
      ρ * (ι a : G) * ρ⁻¹ = (ι a : G) * c.iso.toG fhB := by
  set F := c.iso.toG fhB with hF
  have hF2 : F * F = 1 := F_sq c.iso
  have hρX : ρ ∈ cenOf F := h.hR.1 hr.mem.1
  have hρF : ρ * F = F * ρ := Subgroup.mem_centralizer_singleton_iff.1 hρX
  have hιB : ∀ b : ↥Bh, (ι (b : Ah) : G) = c.iso.toG b := fun b =>
    (h1 (Subgroup.inclusion Bh_le_P1h b)).trans (AutIso.toG1_inclusion c.iso b)
  have hιF : (ι fhatA : G) = F := hιB fhB
  have hιx : (ι xA : G) = z := (hιB xB).trans (c.iso.toG_xB c.z2 c.z1 c.zc)
  have hcomm : ∀ a : Ah, a * fhatA = fhatA * a →
      ((ι a : ↥(M₁ ⊔ M₂)) : G) * F = F * ((ι a : ↥(M₁ ⊔ M₂)) : G) := by
    intro a ha
    have := congrArg (fun w : ↥(M₁ ⊔ M₂) => (w : G)) (congrArg ι ha)
    simpa only [map_mul, Subgroup.coe_mul, hιF] using this
  have hEg : ∀ a : Ah, a * fhatA = fhatA * a → ((ι a : ↥(M₁ ⊔ M₂)) : G) ∈ Eg c := fun a ha =>
    ⟨(ι a).2, Subgroup.mem_centralizer_singleton_iff.2 (hcomm a ha)⟩
  have hrho := rho_comm_Eg c h hr hρE hE hX qd hρQ
  obtain ⟨μ, hμ, hs3⟩ := s3_decomp
  have hμB : μ ∈ Bh := Uh_le_Bh hμ
  have hu : ((ι μ : ↥(M₁ ⊔ M₂)) : G) ∈ UG c :=
    (hιB ⟨μ, hμB⟩) ▸ c.iso.mem_imgG.2 ⟨⟨μ, hμB⟩, hμ, rfl⟩
  have huF : ((ι μ : ↥(M₁ ⊔ M₂)) : G) * F = F * ((ι μ : ↥(M₁ ⊔ M₂)) : G) :=
    Subgroup.mem_centralizer_singleton_iff.1 (TfG_le_cen c (UG_le_TfG c hu))
  have hzF : z * F = F * z := zF_comm c
  have hs3G : ((ι (p10sA 2) : ↥(M₁ ⊔ M₂)) : G) = F * z * ((ι μ : ↥(M₁ ⊔ M₂)) : G) := by
    rw [hs3, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hιF, hιx]
  have hρs3 : ρ * ((ι (p10sA 2) : ↥(M₁ ⊔ M₂)) : G) * ρ⁻¹ =
      ((ι (p10sA 2) : ↥(M₁ ⊔ M₂)) : G) * F := by
    set u : G := ((ι μ : ↥(M₁ ⊔ M₂)) : G) with hudef
    have hρu : ρ * u = u * ρ := hr.comm_UG h hu
    have hρz := hr.conj_z h
    rw [hs3G]
    calc ρ * (F * z * u) * ρ⁻¹ = (ρ * F * ρ⁻¹) * (ρ * z * ρ⁻¹) * (ρ * u * ρ⁻¹) := by group
      _ = F * (F * z) * u := by
        have h1' : ρ * F * ρ⁻¹ = F := by rw [hρF]; group
        have h2' : ρ * u * ρ⁻¹ = u := by rw [hρu]; group
        rw [h1', hρz, h2']
      _ = (F * F) * z * u := by group
      _ = z * u := by rw [hF2, one_mul]
      _ = F * z * u * F := by
        calc z * u = (F * F) * z * u := by rw [hF2, one_mul]
          _ = F * z * (F * u) := by calc F * F * z * u = F * (F * z) * u := by group
                                      _ = F * (z * F) * u := by rw [← hzF]
                                      _ = F * z * (F * u) := by group
          _ = F * z * (u * F) := by rw [huF]
          _ = F * z * u * F := by group
  have hs3F : ((ι (p10sA 2) : ↥(M₁ ⊔ M₂)) : G) * F = F * ((ι (p10sA 2) : ↥(M₁ ⊔ M₂)) : G) := by
    rw [hs3G]
    calc F * z * ((ι μ : ↥(M₁ ⊔ M₂)) : G) * F = F * z * (F * ((ι μ : ↥(M₁ ⊔ M₂)) : G)) := by
          rw [mul_assoc (F * z), huF]
      _ = F * (z * F) * ((ι μ : ↥(M₁ ⊔ M₂)) : G) := by group
      _ = F * (F * z) * ((ι μ : ↥(M₁ ⊔ M₂)) : G) := by rw [hzF]
      _ = F * (F * z * ((ι μ : ↥(M₁ ⊔ M₂)) : G)) := by group
  have key : ∀ (w : List ℕ) (a : Ah), aW w * p10sA 2 * (aW w)⁻¹ = a →
      aW w * fhatA = fhatA * aW w → ρ * (ι a : G) * ρ⁻¹ = (ι a : G) * F := by
    intro w a hconj hc
    rw [← hconj, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact conj_pres (hrho _ (hEg _ hc)) hρs3 (hcomm _ hc) hs3F
  intro a ha
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact key _ _ conj_s1 comm_s1
  · exact hρs3
  · exact key _ _ conj_s5 comm_s5
  · exact key _ _ conj_s6 comm_s6
  · exact key _ _ conj_t comm_t

end Five

end CFSG.Quasithin.H13.F431.U42Aut
