module

public import CFSG.Quasithin.H13.GoldschmidtU43EData

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem comm_of_form {K : Type} [Group K] {x y : K} (h : x⁻¹ * y⁻¹ * x * y = 1) :
    x * y = y * x := by
  have h1 : y⁻¹ * x * y = x := by
    have := congrArg (x * ·) h
    simpa [mul_assoc] using this
  calc x * y = y * (y⁻¹ * x * y) := by group
    _ = y * x := by rw [h1]

theorem zK_ne_one {z : G} (h : Hyp z) : zK z ≠ 1 := by
  intro e
  apply h.z_ne_one
  have := congrArg (fun x : ↥(Hz z) => (x : G)) e
  exact this

namespace JWSetup

variable {z : G} (S : JWSetup z)

include S in
theorem hyp : Hyp z := S.e.swap.hyp

@[expose] def σ₂ : ↥(Hz z) := S.u⁻¹ * S.σ₁ * S.u

theorem uu : S.u * S.u = 1 := by
  have := S.jw.r12
  rwa [pow_two] at this

theorem ui : S.u⁻¹ = S.u := inv_eq_of_mul_eq_one_right S.uu

theorem vv : S.v * S.v = zK z := by
  have := S.jw.r11
  rw [pow_two, pow_two, S.hAA] at this
  exact this


theorem A_not_comm : ¬ (S.A * S.σ₁ = S.σ₁ * S.A) := by
  intro hc
  have h4 := S.jw.r4
  have e : S.σ₁⁻¹ * S.A * S.σ₁ = S.A := by
    calc S.σ₁⁻¹ * S.A * S.σ₁ = S.σ₁⁻¹ * (S.A * S.σ₁) := by group
      _ = S.A := by rw [hc]; group
  rw [e, e] at h4
  have h1 : S.A = 1 := by simpa using h4
  apply zK_ne_one S.hyp
  rw [← S.hAA, h1, one_mul]

theorem σ₁_ne_one : S.σ₁ ≠ 1 := by
  intro h1
  apply S.A_not_comm
  rw [h1]
  simp

theorem σ₂_mem : S.σ₂ ∈ S.R := by
  have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem S.hu) S.σ₁).mp S.hσR
  simpa [σ₂] using this

theorem A_comm_σ₂ : S.A * S.σ₂ = S.σ₂ * S.A := comm_of_form S.jw.r9

theorem σ₂_ne_σ₁ : S.σ₂ ≠ S.σ₁ := by
  intro h
  apply S.A_not_comm
  have := S.A_comm_σ₂
  rwa [h] at this

theorem σ₂_ne_σ₁_inv : S.σ₂ ≠ S.σ₁⁻¹ := by
  intro h
  apply S.A_not_comm
  have hc := S.A_comm_σ₂
  rw [h] at hc
  calc S.A * S.σ₁ = S.σ₁ * (S.σ₁⁻¹ * S.A) * S.σ₁ := by group
    _ = S.σ₁ * (S.A * S.σ₁⁻¹) * S.σ₁ := by rw [← hc]
    _ = S.σ₁ * S.A := by group

theorem σ₁σ₂_ne_one : S.σ₁ * S.σ₂ ≠ 1 := by
  intro h
  apply S.σ₂_ne_σ₁_inv
  rw [mul_eq_one_iff_eq_inv] at h
  rw [h]
  simp

theorem σ₁σ₂_comm : S.σ₁ * S.σ₂ = S.σ₂ * S.σ₁ := comm_of_form S.jw.r10

theorem conj_u_σ₂ : S.u⁻¹ * S.σ₂ * S.u = S.σ₁ := by
  unfold σ₂
  rw [S.ui]
  calc S.u * (S.u * S.σ₁ * S.u) * S.u = (S.u * S.u) * S.σ₁ * (S.u * S.u) := by group
    _ = S.σ₁ := by rw [S.uu]; group

theorem conj_u_σ₁' : S.u * S.σ₁ * S.u⁻¹ = S.σ₂ := by
  unfold σ₂
  rw [S.ui]

theorem conj_v_σ₂ : S.v⁻¹ * S.σ₂ * S.v = S.σ₂⁻¹ := S.jw.r7

theorem conj_v_inv (x : ↥(Hz z)) : S.v⁻¹ * x * S.v = S.v * x * S.v⁻¹ := conj_inv_eq S.hyp S.vv x

theorem conj_v_σ₁ : S.v⁻¹ * S.σ₁ * S.v = S.σ₁⁻¹ := by
  have e1 : S.u⁻¹ * S.v⁻¹ * S.u = S.v := by
    have := congrArg (fun x => x⁻¹) S.jw.r13
    simpa [mul_assoc] using this
  have h2 : S.v * S.σ₁ * S.v⁻¹ = S.σ₁⁻¹ := by
    calc S.v * S.σ₁ * S.v⁻¹ = (S.u⁻¹ * S.v⁻¹ * S.u) * S.σ₁ * (S.u⁻¹ * S.v * S.u) := by
          rw [e1, S.jw.r13]
      _ = S.u⁻¹ * (S.v⁻¹ * (S.u * S.σ₁ * S.u⁻¹) * S.v) * S.u := by group
      _ = S.u⁻¹ * S.σ₂⁻¹ * S.u := by rw [S.conj_u_σ₁', S.conj_v_σ₂]
      _ = (S.u⁻¹ * S.σ₂ * S.u)⁻¹ := by group
      _ = S.σ₁⁻¹ := by rw [S.conj_u_σ₂]
  rw [S.conj_v_inv, h2]

theorem hv : S.v ∈ Subgroup.normalizer (S.R : Set ↥(Hz z)) := by
  have h := mul_mem ((Subgroup.normalizer (S.R : Set ↥(Hz z))).inv_mem S.hu) S.huv
  have e : S.u⁻¹ * (S.u * S.v) = S.v := by group
  rwa [e] at h

theorem uvuv : (S.u * S.v) * (S.u * S.v) = 1 := by
  have h := S.jw.r13
  rw [S.ui] at h
  calc S.u * S.v * (S.u * S.v) = (S.u * S.v * S.u) * S.v := by group
    _ = 1 := by rw [h]; group

end JWSetup

end CFSG.Quasithin.H13.U43
