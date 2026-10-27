module

public import CFSG.Quasithin.H13.GoldschmidtU43EVSMat
public import CFSG.Quasithin.H13.GoldschmidtU43EVSSyl
public import CFSG.Quasithin.H13.GoldschmidtU43EVSChi
public import CFSG.Quasithin.H13.GoldschmidtU43EVSRel

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)

theorem exists_conj_i6 : ∃ k : G, k * z * k⁻¹ = S.a₂G⁻¹ * (S.u : G) * S.a₂G := by
  obtain ⟨k, hk⟩ := S.exists_conj_u
  refine ⟨S.a₂G⁻¹ * k, ?_⟩
  calc S.a₂G⁻¹ * k * z * (S.a₂G⁻¹ * k)⁻¹ = S.a₂G⁻¹ * (k * z * k⁻¹) * S.a₂G := by group
    _ = _ := by rw [hk]

theorem comm_i6 (r : S.Rho) :
    ((S.u : G) * z * S.rho3 r.ρ) * (S.a₂G⁻¹ * (S.u : G) * S.a₂G) =
      (S.a₂G⁻¹ * (S.u : G) * S.a₂G) * ((S.u : G) * z * S.rho3 r.ρ) := by
  set i : G := S.a₂G⁻¹ * (S.u : G) * S.a₂G with hi
  have hu : (S.u : G) * i = i * (S.u : G) := congrArg Subtype.val S.u_comm_i
  have hz : z * i = i * z := (z_comm_H (S.a₂⁻¹ * S.u * S.a₂)).symm
  have hρu : r.ρ * (S.u : G) = (S.u : G) * r.ρ :=
    (mul_inv_eq_iff_eq_mul.mp (S.conj_u_rho r)).symm
  have hρ : S.rho3 r.ρ * i = i * S.rho3 r.ρ := by
    unfold rho3
    calc S.a₂G⁻¹ * r.ρ * S.a₂G * i = S.a₂G⁻¹ * (r.ρ * (S.u : G)) * S.a₂G := by rw [hi]; group
      _ = S.a₂G⁻¹ * ((S.u : G) * r.ρ) * S.a₂G := by rw [hρu]
      _ = i * (S.a₂G⁻¹ * r.ρ * S.a₂G) := by rw [hi]; group
  calc ((S.u : G) * z * S.rho3 r.ρ) * i = (S.u : G) * z * (S.rho3 r.ρ * i) := by group
    _ = (S.u : G) * z * (i * S.rho3 r.ρ) := by rw [hρ]
    _ = (S.u : G) * (z * i) * S.rho3 r.ρ := by group
    _ = (S.u : G) * (i * z) * S.rho3 r.ρ := by rw [hz]
    _ = ((S.u : G) * i) * z * S.rho3 r.ρ := by group
    _ = (i * (S.u : G)) * z * S.rho3 r.ρ := by rw [hu]
    _ = i * ((S.u : G) * z * S.rho3 r.ρ) := by group

theorem rel_r19 (e : S.Nbar ≃* alternatingGroup (Fin 6)) {V₃ : Subgroup G} (hV : S.IsV3 V₃)
    (hAU : (S.A : G) ∈ Uz z) (r : S.Rho) : ((S.u : G) * z * S.rho3 r.ρ) ^ 3 = 1 := by
  have h9 : ((S.u : G) * z * S.rho3 r.ρ) ^ 9 = 1 := by
    refine S.pow_nine_of_chiN_cube r
      (⟨(S.u : G), S.u_mem_Ng⟩ * ⟨z, S.z_mem_Ng⟩ * ⟨S.rho3 r.ρ, S.rho3_mem_Ng e hV hAU r⟩) ?_
    rw [S.chiN_mul, S.chiN_mul, S.chiN_u, S.chiN_z, S.chiN_rho3 r e hV hAU]
    exact cube_Umat_Zmat_Rho3mat
  obtain ⟨k, hk⟩ := S.exists_conj_i6
  have hc := S.comm_i6 r
  rw [← hk] at hc
  exact S.pow_three_of_comm_conj hc h9

end JWSetup

end CFSG.Quasithin.H13.U43
