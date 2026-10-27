module

public import CFSG.Quasithin.H13.GoldschmidtU43EVSAlg
public import CFSG.Quasithin.H13.GoldschmidtU43EQRel

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable {z : G} (S : JWSetup z)
include S

theorem A_mul_a₂ : S.A * S.a₂ = S.a₂ * S.A := by
  have h : S.A⁻¹ * S.a₂⁻¹ * S.A * S.a₂ = 1 := S.jw.r8
  calc S.A * S.a₂ = S.a₂ * S.A * (S.A⁻¹ * S.a₂⁻¹ * S.A * S.a₂) := by group
    _ = S.a₂ * S.A := by rw [h, mul_one]

theorem u_a₂_u : S.u * S.a₂ * S.u = S.A := by
  calc S.u * S.a₂ * S.u = S.u * (S.u⁻¹ * S.A * S.u) * S.u := rfl
    _ = S.A * (S.u * S.u) := by group
    _ = S.A := by rw [S.uu, mul_one]

theorem u_v_u : S.u * S.v * S.u = S.v⁻¹ := by
  have h : S.u⁻¹ * S.v * S.u = S.v⁻¹ := S.jw.r13
  rwa [S.ui] at h

theorem v_a₂_v : S.v * S.a₂ * S.v⁻¹ = S.a₂⁻¹ := by
  have h : S.v⁻¹ * S.a₂ * S.v = S.a₂⁻¹ := S.jw.r6
  rw [← S.conj_v_inv S.a₂]
  exact h

theorem u_comm_i : S.u * (S.a₂⁻¹ * S.u * S.a₂) = (S.a₂⁻¹ * S.u * S.a₂) * S.u :=
  u_comm_conj (fun x => zK_comm x) (zK_mul_zK S.hyp) S.hAA S.a₂_sq S.A_mul_a₂ S.uu S.u_a₂_u

theorem uv_comm_i : (S.a₂⁻¹ * (S.u * S.v * zK z) * S.a₂) * (S.u * S.v) =
    (S.u * S.v) * (S.a₂⁻¹ * (S.u * S.v * zK z) * S.a₂) :=
  uv_comm_conj (fun x => zK_comm x) (zK_mul_zK S.hyp) S.hAA S.a₂_sq S.A_mul_a₂ S.uu S.u_a₂_u
    S.u_v_u S.v_a₂_v

theorem u_v_z_ne_one : (S.u : G) * S.v * z ≠ 1 := by
  intro h
  have hK : S.u * S.v * zK z = 1 := Subtype.ext h
  have hZ : zK z * zK z = 1 := zK_mul_zK S.hyp
  have hZi : (zK z)⁻¹ = zK z := inv_eq_of_mul_eq_one_right hZ
  have hui : S.u⁻¹ = S.u := S.ui
  have huv : S.v = S.u * zK z := by
    have h1 : S.u * S.v = zK z := by
      have := eq_inv_of_mul_eq_one_left hK
      rwa [hZi] at this
    calc S.v = S.u⁻¹ * (S.u * S.v) := by group
      _ = S.u * zK z := by rw [h1, hui]
  have hvv : S.v * S.v = 1 := by
    calc S.v * S.v = S.u * zK z * (S.u * zK z) := by rw [← huv]
      _ = S.u * (zK z * S.u) * zK z := by group
      _ = S.u * (S.u * zK z) * zK z := by rw [zK_comm S.u]
      _ = (S.u * S.u) * (zK z * zK z) := by group
      _ = 1 := by rw [S.uu, hZ, mul_one]
  have : zK z = 1 := by rw [← S.vv]; exact hvv
  exact S.hyp.z_ne_one (congrArg Subtype.val this)

end JWSetup

end CFSG.Quasithin.H13.U43
