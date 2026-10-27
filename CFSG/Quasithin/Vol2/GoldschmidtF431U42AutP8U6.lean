module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8U5

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section Act

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G} {ρ : G}

theorem rho_not_mem_M0 (hr : RhoCtx c R ρ) (ι : Ah ≃* ↥(M₁ ⊔ M₂))
    (h1 : ∀ x : P1h, (ι (x : Ah) : G) = (c.iso.phi1 x : G)) : ρ ∉ M₁ ⊔ M₂ := by
  intro hρ
  obtain ⟨a, ha⟩ := ι.surjective ⟨ρ, hρ⟩
  have hιf : (ι fhatA : G) = c.iso.toG fhB := (h1 fP1).trans (toG1_fP1 c)
  have hsq : ι (a * a) = ι fhatA := by
    apply Subtype.ext
    rw [map_mul, Subgroup.coe_mul, hιf]
    have : ((ι a : ↥(M₁ ⊔ M₂)) : G) = ρ := congrArg Subtype.val ha
    rw [this, hr.sq]
  have haa : a * a = fhatA := ι.injective hsq
  have hY : a * a ∈ Yh := by
    rw [← signA_eq_one_iff, map_mul]
    exact Int.units_mul_self _
  exact fhatA_not_mem_Yh (haa ▸ hY)

theorem rho_not_mem_Eg (hr : RhoCtx c R ρ) (ι : Ah ≃* ↥(M₁ ⊔ M₂))
    (h1 : ∀ x : P1h, (ι (x : Ah) : G) = (c.iso.phi1 x : G)) : ρ ∉ Eg c :=
  fun hE => rho_not_mem_M0 c hr ι h1 hE.1

theorem rho_comm_Eg (h : F55Ctx c R) (hr : RhoCtx c R ρ) (hρE : ρ ∉ Eg c)
    (hE : Nat.card ↥(Eg c) = 1440) (hX : Nat.card ↥(cenOf (c.iso.toG fhB)) = 2880)
    (qd : QData c) (hρQ : ∀ q ∈ oddCl (cenOf (c.iso.toG fhB)), ρ * q = q * ρ) :
    ∀ e ∈ Eg c, ρ * e * ρ⁻¹ = e ∨ ρ * e * ρ⁻¹ = e * c.iso.toG fhB := by
  intro e he
  set F := c.iso.toG fhB with hF
  have hρX : ρ ∈ cenOf F := h.hR.1 hr.mem.1
  have heX : e ∈ cenOf F := Eg_le_cen c he
  have hρinvE : ρ⁻¹ ∉ Eg c := fun hm => hρE (by simpa using (Eg c).inv_mem hm)
  have hρeE : ρ * e ∉ Eg c := fun hm => hρE (((mul_mem_Eg_iff c hE hX hρX heX).1 hm).2 he)
  have hmem : ρ * e * ρ⁻¹ ∈ Eg c :=
    (mul_mem_Eg_iff c hE hX ((cenOf F).mul_mem hρX heX) ((cenOf F).inv_mem hρX)).2
      ⟨fun h' => absurd h' hρeE, fun h' => absurd h' hρinvE⟩
  have hkE : ρ * e * ρ⁻¹ * e⁻¹ ∈ Eg c := (Eg c).mul_mem hmem ((Eg c).inv_mem he)
  have hcen : ∀ q ∈ oddCl (cenOf F), (ρ * e * ρ⁻¹ * e⁻¹) * q = q * (ρ * e * ρ⁻¹ * e⁻¹) := by
    intro q hq
    have hq' : e⁻¹ * q * e ∈ oddCl (cenOf F) := by
      have := oddCl_conj_cen c ((cenOf F).inv_mem heX) hq
      simpa using this
    have h1 : ρ * q = q * ρ := hρQ q hq
    have h2 : ρ * (e⁻¹ * q * e) = (e⁻¹ * q * e) * ρ := hρQ _ hq'
    have h3 : ρ⁻¹ * (e⁻¹ * q * e) = (e⁻¹ * q * e) * ρ⁻¹ := by
      calc ρ⁻¹ * (e⁻¹ * q * e) = ρ⁻¹ * ((e⁻¹ * q * e) * ρ) * ρ⁻¹ := by group
        _ = ρ⁻¹ * (ρ * (e⁻¹ * q * e)) * ρ⁻¹ := by rw [h2]
        _ = (e⁻¹ * q * e) * ρ⁻¹ := by group
    calc (ρ * e * ρ⁻¹ * e⁻¹) * q = ρ * e * (ρ⁻¹ * (e⁻¹ * q * e)) * e⁻¹ := by group
      _ = ρ * e * ((e⁻¹ * q * e) * ρ⁻¹) * e⁻¹ := by rw [h3]
      _ = ρ * q * (e * ρ⁻¹ * e⁻¹) := by group
      _ = (q * ρ) * (e * ρ⁻¹ * e⁻¹) := by rw [h1]
      _ = q * (ρ * e * ρ⁻¹ * e⁻¹) := by group
  have hFc : e * F = F * e := Subgroup.mem_centralizer_singleton_iff.1 heX
  rcases cen_Q_cases c h hr hρE qd hkE hcen with h1 | h1
  · left
    calc ρ * e * ρ⁻¹ = (ρ * e * ρ⁻¹ * e⁻¹) * e := by group
      _ = e := by rw [h1, one_mul]
  · right
    calc ρ * e * ρ⁻¹ = (ρ * e * ρ⁻¹ * e⁻¹) * e := by group
      _ = F * e := by rw [h1]
      _ = e * F := hFc.symm

end Act

end CFSG.Quasithin.H13.F431.U42Aut
