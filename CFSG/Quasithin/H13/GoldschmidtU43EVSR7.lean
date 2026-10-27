module

public import CFSG.Quasithin.H13.GoldschmidtU43EVSChi
public import CFSG.Quasithin.H13.GoldschmidtU43EVSMat
public import CFSG.Quasithin.H13.GoldschmidtU43EVSRel
public import CFSG.Quasithin.H13.GoldschmidtU43EVSSyl

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)

theorem exists_conj_i7 : ∃ k : G, k * z * k⁻¹ = S.a₂G⁻¹ * ((S.u : G) * S.v * z) * S.a₂G := by
  have hy : (S.u : G) * S.v * z ∈ Eg z S.t S.w S.a' := mul_mem S.huvE Swap.z_mem_Eg
  obtain ⟨k, -, hk⟩ := S.e.swap.exists_conj_to_z S.e.ha' hy S.u_v_z_ne_one
  refine ⟨S.a₂G⁻¹ * k, ?_⟩
  calc S.a₂G⁻¹ * k * z * (S.a₂G⁻¹ * k)⁻¹ = S.a₂G⁻¹ * (k * z * k⁻¹) * S.a₂G := by group
    _ = _ := by rw [hk]

theorem comm_uvz_rho (r : S.Rho) :
    ((S.u : G) * S.v * z) * (r.ρ⁻¹ * S.rho2 r.ρ) =
      (r.ρ⁻¹ * S.rho2 r.ρ) * ((S.u : G) * S.v * z) := by
  have h1 : z * (r.ρ⁻¹ * S.rho2 r.ρ) * z⁻¹ = r.ρ * (S.rho2 r.ρ)⁻¹ := by
    calc z * (r.ρ⁻¹ * S.rho2 r.ρ) * z⁻¹ = (z * r.ρ * z⁻¹)⁻¹ * (z * S.rho2 r.ρ * z⁻¹) := by group
      _ = r.ρ * (S.rho2 r.ρ)⁻¹ := by rw [r.inv, S.z_rho2 r.inv, inv_inv]
  have h2 : (S.v : G) * (r.ρ * (S.rho2 r.ρ)⁻¹) * (S.v : G)⁻¹ = (S.rho2 r.ρ)⁻¹ * r.ρ⁻¹ := by
    calc (S.v : G) * (r.ρ * (S.rho2 r.ρ)⁻¹) * (S.v : G)⁻¹
        = ((S.v : G) * r.ρ * (S.v : G)⁻¹) * ((S.v : G) * S.rho2 r.ρ * (S.v : G)⁻¹)⁻¹ := by group
      _ = (S.rho2 r.ρ)⁻¹ * r.ρ⁻¹ := by rw [S.conj_v_rho r, S.conj_v_rho2 r]
  have h3 : (S.u : G) * ((S.rho2 r.ρ)⁻¹ * r.ρ⁻¹) * (S.u : G)⁻¹ = S.rho2 r.ρ * r.ρ⁻¹ := by
    calc (S.u : G) * ((S.rho2 r.ρ)⁻¹ * r.ρ⁻¹) * (S.u : G)⁻¹
        = ((S.u : G) * S.rho2 r.ρ * (S.u : G)⁻¹)⁻¹ * ((S.u : G) * r.ρ * (S.u : G)⁻¹)⁻¹ := by
          group
      _ = S.rho2 r.ρ * r.ρ⁻¹ := by rw [S.conj_u_rho2 r, S.conj_u_rho r, inv_inv]
  have hc : r.ρ * S.rho2 r.ρ = S.rho2 r.ρ * r.ρ := S.commute_rho r.mem r.inv
  have h4 : S.rho2 r.ρ * r.ρ⁻¹ = r.ρ⁻¹ * S.rho2 r.ρ := by
    calc S.rho2 r.ρ * r.ρ⁻¹ = r.ρ⁻¹ * (r.ρ * S.rho2 r.ρ) * r.ρ⁻¹ := by group
      _ = r.ρ⁻¹ * (S.rho2 r.ρ * r.ρ) * r.ρ⁻¹ := by rw [hc]
      _ = r.ρ⁻¹ * S.rho2 r.ρ := by group
  have h5 : ((S.u : G) * S.v * z) * (r.ρ⁻¹ * S.rho2 r.ρ) * ((S.u : G) * S.v * z)⁻¹ =
      r.ρ⁻¹ * S.rho2 r.ρ := by
    calc ((S.u : G) * S.v * z) * (r.ρ⁻¹ * S.rho2 r.ρ) * ((S.u : G) * S.v * z)⁻¹
        = (S.u : G) * ((S.v : G) * (z * (r.ρ⁻¹ * S.rho2 r.ρ) * z⁻¹) * (S.v : G)⁻¹) *
            (S.u : G)⁻¹ := by group
      _ = r.ρ⁻¹ * S.rho2 r.ρ := by rw [h1, h2, h3, h4]
  exact mul_inv_eq_iff_eq_mul.mp h5

theorem comm_i7 (r : S.Rho) :
    ((S.u : G) * S.v * (S.rho3 r.ρ)⁻¹ * S.rho4 r.ρ) * (S.a₂G⁻¹ * ((S.u : G) * S.v * z) * S.a₂G) =
      (S.a₂G⁻¹ * ((S.u : G) * S.v * z) * S.a₂G) * ((S.u : G) * S.v * (S.rho3 r.ρ)⁻¹ * S.rho4 r.ρ) :=
  by
  have hw : ((S.u : G) * S.v) * (S.a₂G⁻¹ * ((S.u : G) * S.v * z) * S.a₂G) =
      (S.a₂G⁻¹ * ((S.u : G) * S.v * z) * S.a₂G) * ((S.u : G) * S.v) :=
    (congrArg Subtype.val S.uv_comm_i).symm
  have hq : ((S.rho3 r.ρ)⁻¹ * S.rho4 r.ρ) * (S.a₂G⁻¹ * ((S.u : G) * S.v * z) * S.a₂G) =
      (S.a₂G⁻¹ * ((S.u : G) * S.v * z) * S.a₂G) * ((S.rho3 r.ρ)⁻¹ * S.rho4 r.ρ) := by
    have hx := S.comm_uvz_rho r
    unfold rho3 rho4
    calc (S.a₂G⁻¹ * r.ρ * S.a₂G)⁻¹ * (S.a₂G⁻¹ * S.rho2 r.ρ * S.a₂G) *
          (S.a₂G⁻¹ * ((S.u : G) * S.v * z) * S.a₂G)
        = S.a₂G⁻¹ * ((r.ρ⁻¹ * S.rho2 r.ρ) * ((S.u : G) * S.v * z)) * S.a₂G := by group
      _ = S.a₂G⁻¹ * (((S.u : G) * S.v * z) * (r.ρ⁻¹ * S.rho2 r.ρ)) * S.a₂G := by rw [hx]
      _ = (S.a₂G⁻¹ * ((S.u : G) * S.v * z) * S.a₂G) *
          ((S.a₂G⁻¹ * r.ρ * S.a₂G)⁻¹ * (S.a₂G⁻¹ * S.rho2 r.ρ * S.a₂G)) := by group
  calc ((S.u : G) * S.v * (S.rho3 r.ρ)⁻¹ * S.rho4 r.ρ) *
        (S.a₂G⁻¹ * ((S.u : G) * S.v * z) * S.a₂G)
      = ((S.u : G) * S.v) * (((S.rho3 r.ρ)⁻¹ * S.rho4 r.ρ) *
          (S.a₂G⁻¹ * ((S.u : G) * S.v * z) * S.a₂G)) := by group
    _ = ((S.u : G) * S.v) * ((S.a₂G⁻¹ * ((S.u : G) * S.v * z) * S.a₂G) *
          ((S.rho3 r.ρ)⁻¹ * S.rho4 r.ρ)) := by rw [hq]
    _ = (((S.u : G) * S.v) * (S.a₂G⁻¹ * ((S.u : G) * S.v * z) * S.a₂G)) *
          ((S.rho3 r.ρ)⁻¹ * S.rho4 r.ρ) := by group
    _ = ((S.a₂G⁻¹ * ((S.u : G) * S.v * z) * S.a₂G) * ((S.u : G) * S.v)) *
          ((S.rho3 r.ρ)⁻¹ * S.rho4 r.ρ) := by rw [hw]
    _ = (S.a₂G⁻¹ * ((S.u : G) * S.v * z) * S.a₂G) *
          ((S.u : G) * S.v * (S.rho3 r.ρ)⁻¹ * S.rho4 r.ρ) := by group

theorem rel_r20 (e : S.Nbar ≃* alternatingGroup (Fin 6)) {V₃ : Subgroup G} (hV : S.IsV3 V₃)
    (hAU : (S.A : G) ∈ Uz z) (r : S.Rho) :
    ((S.u : G) * S.v * (S.rho3 r.ρ)⁻¹ * S.rho4 r.ρ) ^ 3 = 1 := by
  have hinv : (S.rho3 r.ρ)⁻¹ = S.rho3 r.ρ * S.rho3 r.ρ := by
    have h3 := S.rho3_pow_three (S.rho_pow_three r.mem r.inv)
    rw [pow_three] at h3
    exact inv_eq_of_mul_eq_one_right h3
  have h9 : ((S.u : G) * S.v * (S.rho3 r.ρ * S.rho3 r.ρ) * S.rho4 r.ρ) ^ 9 = 1 := by
    refine S.pow_nine_of_chiN_cube r
      (⟨(S.u : G), S.u_mem_Ng⟩ * ⟨(S.v : G), S.v_mem_Ng⟩ *
        (⟨S.rho3 r.ρ, S.rho3_mem_Ng e hV hAU r⟩ * ⟨S.rho3 r.ρ, S.rho3_mem_Ng e hV hAU r⟩) *
        ⟨S.rho4 r.ρ, S.rho4_mem_Ng e hV hAU r⟩) ?_
    rw [S.chiN_mul, S.chiN_mul, S.chiN_mul, S.chiN_mul, S.chiN_u, S.chiN_v,
      S.chiN_rho3 r e hV hAU, S.chiN_rho4 r e hV hAU]
    exact cube_Umat_Vmat_Rho3mat_Rho4mat
  rw [← hinv] at h9
  obtain ⟨k, hk⟩ := S.exists_conj_i7
  have hc := S.comm_i7 r
  rw [← hk] at hc
  exact S.pow_three_of_comm_conj hc h9

end JWSetup

end CFSG.Quasithin.H13.U43
