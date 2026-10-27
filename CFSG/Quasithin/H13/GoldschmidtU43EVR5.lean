module

public import CFSG.Quasithin.H13.GoldschmidtU43EVR4

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z) (r : S.Rho)

theorem crd_injective : Function.Injective (S.crd r) := fun a b h => by
  have := congrArg (evC (basis r)) h
  rwa [S.evC_crd, S.evC_crd] at this

variable {S} {V₃ : Subgroup G}

@[expose] noncomputable def rho3N (e : S.Nbar ≃* alternatingGroup (Fin 6)) (hV : S.IsV3 V₃)
    (hAU : (S.A : G) ∈ Uz z) : ↥S.Ng := ⟨S.rho3 r.ρ, S.rho3_mem_Ng e hV hAU r⟩

theorem chiN_rho3N (e : S.Nbar ≃* alternatingGroup (Fin 6)) (hV : S.IsV3 V₃)
    (hAU : (S.A : G) ∈ Uz z) : S.chiN r (S.rho3N r e hV hAU) = Rho3mat :=
  S.chiN_rho3 r e hV hAU

theorem rho3_conj_rho (e : S.Nbar ≃* alternatingGroup (Fin 6)) (hV : S.IsV3 V₃)
    (hAU : (S.A : G) ∈ Uz z) :
    S.rho3 r.ρ * r.ρ * (S.rho3 r.ρ)⁻¹ = (S.σ₁ : G) * r.ρ := by
  have h : S.conjM (S.rho3N r e hV hAU) (S.rho3N r e hV hAU).2 (S.ρM r) = S.σ₁M * S.ρM r := by
    apply S.crd_injective r
    rw [S.crd_conjM, S.chiN_rho3N r e hV hAU, S.crd_mul, S.crd_ρM, S.crd_σ₁M]
    decide
  exact congrArg Subtype.val h

theorem rho3_conj_rho2 (e : S.Nbar ≃* alternatingGroup (Fin 6)) (hV : S.IsV3 V₃)
    (hAU : (S.A : G) ∈ Uz z) :
    S.rho3 r.ρ * S.rho2 r.ρ * (S.rho3 r.ρ)⁻¹ = S.rho2 r.ρ := by
  have h : S.conjM (S.rho3N r e hV hAU) (S.rho3N r e hV hAU).2 (S.ρ₂M r) = S.ρ₂M r := by
    apply S.crd_injective r
    rw [S.crd_conjM, S.chiN_rho3N r e hV hAU, S.crd_ρ₂M]
    decide
  exact congrArg Subtype.val h

theorem rel_r17 (e : S.Nbar ≃* alternatingGroup (Fin 6)) (hV : S.IsV3 V₃)
    (hAU : (S.A : G) ∈ Uz z) :
    (S.rho3 r.ρ)⁻¹ * r.ρ * S.rho3 r.ρ = r.ρ * (S.σ₁ : G)⁻¹ := by
  have h := S.rho3_conj_rho r e hV hAU
  have hc : S.rho3 r.ρ * (S.σ₁ : G) = (S.σ₁ : G) * S.rho3 r.ρ := S.rho3_comm_σ₁ r
  have hρσ : r.ρ * (S.σ₁ : G) = (S.σ₁ : G) * r.ρ :=
    S.abelian_Mg _ r.mem_Mg _ (S.Tg_le_Mg S.σ₁G_mem_Tg)
  have hci : (S.rho3 r.ρ)⁻¹ * (S.σ₁ : G) = (S.σ₁ : G) * (S.rho3 r.ρ)⁻¹ := by
    calc (S.rho3 r.ρ)⁻¹ * (S.σ₁ : G)
        = (S.rho3 r.ρ)⁻¹ * ((S.σ₁ : G) * S.rho3 r.ρ) * (S.rho3 r.ρ)⁻¹ := by group
      _ = (S.rho3 r.ρ)⁻¹ * (S.rho3 r.ρ * (S.σ₁ : G)) * (S.rho3 r.ρ)⁻¹ := by rw [hc]
      _ = (S.σ₁ : G) * (S.rho3 r.ρ)⁻¹ := by group
  have h1 : r.ρ = (S.rho3 r.ρ)⁻¹ * ((S.σ₁ : G) * r.ρ) * S.rho3 r.ρ := by
    rw [← h]
    group
  calc (S.rho3 r.ρ)⁻¹ * r.ρ * S.rho3 r.ρ
      = (S.σ₁ : G)⁻¹ * ((S.σ₁ : G) * ((S.rho3 r.ρ)⁻¹ * r.ρ * S.rho3 r.ρ)) := by group
    _ = (S.σ₁ : G)⁻¹ * (((S.σ₁ : G) * (S.rho3 r.ρ)⁻¹) * r.ρ * S.rho3 r.ρ) := by group
    _ = (S.σ₁ : G)⁻¹ * (((S.rho3 r.ρ)⁻¹ * (S.σ₁ : G)) * r.ρ * S.rho3 r.ρ) := by rw [hci]
    _ = (S.σ₁ : G)⁻¹ * ((S.rho3 r.ρ)⁻¹ * ((S.σ₁ : G) * r.ρ) * S.rho3 r.ρ) := by group
    _ = (S.σ₁ : G)⁻¹ * r.ρ := by rw [← h1]
    _ = r.ρ * (S.σ₁ : G)⁻¹ := by
        have : (S.σ₁ : G)⁻¹ * r.ρ = r.ρ * (S.σ₁ : G)⁻¹ := by
          calc (S.σ₁ : G)⁻¹ * r.ρ = (S.σ₁ : G)⁻¹ * (r.ρ * (S.σ₁ : G)) * (S.σ₁ : G)⁻¹ := by group
            _ = (S.σ₁ : G)⁻¹ * ((S.σ₁ : G) * r.ρ) * (S.σ₁ : G)⁻¹ := by rw [hρσ]
            _ = r.ρ * (S.σ₁ : G)⁻¹ := by group
        exact this

theorem rho4_conj_rho (e : S.Nbar ≃* alternatingGroup (Fin 6)) (hV : S.IsV3 V₃)
    (hAU : (S.A : G) ∈ Uz z) : S.rho4 r.ρ * r.ρ * (S.rho4 r.ρ)⁻¹ = r.ρ := by
  have h1 := S.rho3_conj_rho2 r e hV hAU
  have h2 := S.conj_v_rho3 r
  have h3 : S.rho2 r.ρ = (S.v : G)⁻¹ * r.ρ * (S.v : G) := rfl
  calc S.rho4 r.ρ * r.ρ * (S.rho4 r.ρ)⁻¹
      = (S.v : G) * (S.rho3 r.ρ * ((S.v : G)⁻¹ * r.ρ * (S.v : G)) * (S.rho3 r.ρ)⁻¹) *
          (S.v : G)⁻¹ := by rw [← h2]; group
    _ = (S.v : G) * (S.rho3 r.ρ * S.rho2 r.ρ * (S.rho3 r.ρ)⁻¹) * (S.v : G)⁻¹ := by rw [h3]
    _ = (S.v : G) * S.rho2 r.ρ * (S.v : G)⁻¹ := by rw [h1]
    _ = r.ρ := S.conj_v_rho2 r

theorem rel_r18 (e : S.Nbar ≃* alternatingGroup (Fin 6)) (hV : S.IsV3 V₃)
    (hAU : (S.A : G) ∈ Uz z) :
    r.ρ⁻¹ * (S.rho4 r.ρ)⁻¹ * r.ρ * S.rho4 r.ρ = 1 := by
  have h := S.rho4_conj_rho r e hV hAU
  have h' : r.ρ * S.rho4 r.ρ = S.rho4 r.ρ * r.ρ := by
    calc r.ρ * S.rho4 r.ρ = (S.rho4 r.ρ * r.ρ * (S.rho4 r.ρ)⁻¹) * S.rho4 r.ρ := by rw [h]
      _ = S.rho4 r.ρ * r.ρ := by group
  calc r.ρ⁻¹ * (S.rho4 r.ρ)⁻¹ * r.ρ * S.rho4 r.ρ
      = (S.rho4 r.ρ * r.ρ)⁻¹ * (r.ρ * S.rho4 r.ρ) := by group
    _ = 1 := by rw [h']; group

theorem rel_r16 (e : S.Nbar ≃* alternatingGroup (Fin 6)) (hV : S.IsV3 V₃)
    (hAU : (S.A : G) ∈ Uz z) :
    (S.σ₂ : G)⁻¹ * S.rho3 r.ρ * (S.σ₂ : G) = r.ρ⁻¹ * S.rho3 r.ρ * (S.σ₁ : G) := by
  obtain ⟨nn, hnn_def⟩ : ∃ nn : ↥S.Ng, nn = S.rho3N r e hV hAU * S.rho3N r e hV hAU :=
    ⟨_, rfl⟩
  have hρ3 : S.rho3 r.ρ ^ 3 = 1 := S.rho3_pow_three (S.rho_pow_three r.mem r.inv)
  have hnn : (nn : G) = (S.rho3 r.ρ)⁻¹ := by
    rw [hnn_def]
    show S.rho3 r.ρ * S.rho3 r.ρ = (S.rho3 r.ρ)⁻¹
    rw [eq_inv_iff_mul_eq_one]
    rw [← pow_three'] 
    exact hρ3
  have hcσ : ((S.conjM nn nn.2 S.σ₂M : ↥S.Mg) : G) =
      (S.rho3 r.ρ)⁻¹ * (S.σ₂ : G) * S.rho3 r.ρ := by
    show (nn : G) * (S.σ₂ : G) * (nn : G)⁻¹ = _
    rw [hnn]
    group
  have hcρ : ((S.conjM nn nn.2 (S.ρM r) : ↥S.Mg) : G) =
      (S.rho3 r.ρ)⁻¹ * r.ρ * S.rho3 r.ρ := by
    show (nn : G) * r.ρ * (nn : G)⁻¹ = _
    rw [hnn]
    group
  have hM : (S.conjM nn nn.2 S.σ₂M)⁻¹ * S.σ₂M = (S.conjM nn nn.2 (S.ρM r))⁻¹ * S.σ₁M := by
    apply S.crd_injective r
    rw [S.crd_mul, S.crd_mul, S.crd_inv, S.crd_inv, S.crd_conjM, S.crd_conjM, hnn_def,
      S.chiN_mul, S.chiN_rho3N r e hV hAU, S.crd_σ₂M, S.crd_ρM, S.crd_σ₁M]
    decide
  have hG' : ((S.rho3 r.ρ)⁻¹ * (S.σ₂ : G) * S.rho3 r.ρ)⁻¹ * (S.σ₂ : G) =
      ((S.rho3 r.ρ)⁻¹ * r.ρ * S.rho3 r.ρ)⁻¹ * (S.σ₁ : G) := by
    have e1 : ((S.conjM nn nn.2 S.σ₂M)⁻¹ * S.σ₂M : ↥S.Mg).val =
        ((S.rho3 r.ρ)⁻¹ * (S.σ₂ : G) * S.rho3 r.ρ)⁻¹ * (S.σ₂ : G) := by
      show ((S.conjM nn nn.2 S.σ₂M : ↥S.Mg) : G)⁻¹ * (S.σ₂ : G) = _
      rw [hcσ]
    have e2 : ((S.conjM nn nn.2 (S.ρM r))⁻¹ * S.σ₁M : ↥S.Mg).val =
        ((S.rho3 r.ρ)⁻¹ * r.ρ * S.rho3 r.ρ)⁻¹ * (S.σ₁ : G) := by
      show ((S.conjM nn nn.2 (S.ρM r) : ↥S.Mg) : G)⁻¹ * (S.σ₁ : G) = _
      rw [hcρ]
    rw [← e1, ← e2]
    exact congrArg Subtype.val hM
  calc (S.σ₂ : G)⁻¹ * S.rho3 r.ρ * (S.σ₂ : G)
      = S.rho3 r.ρ * (((S.rho3 r.ρ)⁻¹ * (S.σ₂ : G) * S.rho3 r.ρ)⁻¹ * (S.σ₂ : G)) := by group
    _ = S.rho3 r.ρ * (((S.rho3 r.ρ)⁻¹ * r.ρ * S.rho3 r.ρ)⁻¹ * (S.σ₁ : G)) := by rw [hG']
    _ = r.ρ⁻¹ * S.rho3 r.ρ * (S.σ₁ : G) := by group

end JWSetup

end CFSG.Quasithin.H13.U43
