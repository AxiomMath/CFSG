module

public import CFSG.Quasithin.H13.GoldschmidtU43EBasic

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable {z : G} (S : JWSetup z)

theorem σ₁_cube : S.σ₁ * S.σ₁ * S.σ₁ = 1 := by
  have := S.jw.r1
  rwa [pow_three'] at this

theorem σ₂_cube : S.σ₂ * S.σ₂ * S.σ₂ = 1 := by
  have h := S.σ₁_cube
  calc S.σ₂ * S.σ₂ * S.σ₂ = S.u⁻¹ * (S.σ₁ * S.σ₁ * S.σ₁) * S.u := by unfold σ₂; group
    _ = 1 := by rw [h]; group

theorem σ₁_inv_inv : S.σ₁⁻¹ * S.σ₁⁻¹ = S.σ₁ := by
  calc S.σ₁⁻¹ * S.σ₁⁻¹ = S.σ₁⁻¹ * S.σ₁⁻¹ * (S.σ₁ * S.σ₁ * S.σ₁) * 1 := by rw [S.σ₁_cube]; group
    _ = S.σ₁ := by group

theorem σ_A_σ : S.σ₁ * S.A * S.σ₁ = S.A * S.σ₁⁻¹ * S.A := by
  have h4 := S.jw.r4
  have h5 : S.σ₁⁻¹ * S.σ₁⁻¹ * S.A * S.σ₁ = S.A * S.σ₁⁻¹ * S.A := by
    calc S.σ₁⁻¹ * S.σ₁⁻¹ * S.A * S.σ₁
        = (S.σ₁⁻¹ * (S.σ₁⁻¹ * S.A * S.σ₁) * S.σ₁) * S.σ₁⁻¹ := by group
      _ = (S.A * (S.σ₁⁻¹ * S.A * S.σ₁)) * S.σ₁⁻¹ := by rw [h4]
      _ = S.A * S.σ₁⁻¹ * S.A := by group
  calc S.σ₁ * S.A * S.σ₁ = S.σ₁⁻¹ * S.σ₁⁻¹ * S.A * S.σ₁ := by rw [S.σ₁_inv_inv]
    _ = S.A * S.σ₁⁻¹ * S.A := h5

theorem Aσ_cube : S.A * S.σ₁ * (S.A * S.σ₁) * (S.A * S.σ₁) = 1 := by
  calc S.A * S.σ₁ * (S.A * S.σ₁) * (S.A * S.σ₁) = S.A * (S.σ₁ * S.A * S.σ₁) * S.A * S.σ₁ := by
        group
    _ = S.A * (S.A * S.σ₁⁻¹ * S.A) * S.A * S.σ₁ := by rw [S.σ_A_σ]
    _ = (S.A * S.A) * S.σ₁⁻¹ * (S.A * S.A) * S.σ₁ := by group
    _ = zK z * S.σ₁⁻¹ * zK z * S.σ₁ := by rw [S.hAA]
    _ = zK z * (S.σ₁⁻¹ * zK z) * S.σ₁ := by group
    _ = zK z * (zK z * S.σ₁⁻¹) * S.σ₁ := by rw [← zK_comm S.σ₁⁻¹]
    _ = (zK z * zK z) * (S.σ₁⁻¹ * S.σ₁) := by group
    _ = 1 := by rw [zK_mul_zK S.hyp]; group

theorem b₁_sq : (S.σ₁⁻¹ * S.A * S.σ₁) * (S.σ₁⁻¹ * S.A * S.σ₁) = zK z := by
  have h := S.jw.r2
  rw [pow_two, pow_two, S.hAA] at h
  exact h

theorem Ab₁_sq : (S.A * (S.σ₁⁻¹ * S.A * S.σ₁)) * (S.A * (S.σ₁⁻¹ * S.A * S.σ₁)) = zK z := by
  have h4 := S.jw.r4
  rw [← h4]
  calc S.σ₁⁻¹ * (S.σ₁⁻¹ * S.A * S.σ₁) * S.σ₁ * (S.σ₁⁻¹ * (S.σ₁⁻¹ * S.A * S.σ₁) * S.σ₁)
      = S.σ₁⁻¹ * ((S.σ₁⁻¹ * S.A * S.σ₁) * (S.σ₁⁻¹ * S.A * S.σ₁)) * S.σ₁ := by group
    _ = S.σ₁⁻¹ * zK z * S.σ₁ := by rw [S.b₁_sq]
    _ = zK z := by rw [← zK_comm S.σ₁⁻¹]; group

@[expose] def a₂ : ↥(Hz z) := S.u⁻¹ * S.A * S.u

@[expose] def b₂ : ↥(Hz z) := S.σ₂⁻¹ * S.a₂ * S.σ₂

theorem a₂_sq : S.a₂ * S.a₂ = zK z := by
  have h := S.jw.r5
  rw [pow_two, pow_two, S.hAA] at h
  exact h

theorem b₂_sq : S.b₂ * S.b₂ = zK z := by
  calc S.b₂ * S.b₂ = S.σ₂⁻¹ * (S.a₂ * S.a₂) * S.σ₂ := by unfold b₂; group
    _ = zK z := by rw [S.a₂_sq, ← zK_comm S.σ₂⁻¹]; group

theorem b₂_eq : S.b₂ = S.u⁻¹ * (S.σ₁⁻¹ * S.A * S.σ₁) * S.u := by
  unfold b₂ a₂ σ₂
  group

theorem a₂b₂_sq : (S.a₂ * S.b₂) * (S.a₂ * S.b₂) = zK z := by
  have e : (S.a₂ * S.b₂) * (S.a₂ * S.b₂) =
      S.u⁻¹ * ((S.A * (S.σ₁⁻¹ * S.A * S.σ₁)) * (S.A * (S.σ₁⁻¹ * S.A * S.σ₁))) * S.u := by
    rw [S.b₂_eq]
    unfold a₂
    group
  rw [e, S.Ab₁_sq, ← zK_comm S.u⁻¹]
  group

theorem a₂_comm_σ₁ : S.a₂ * S.σ₁ = S.σ₁ * S.a₂ := by
  have h := S.A_comm_σ₂
  have e : S.u⁻¹ * (S.A * S.σ₂) * S.u = S.u⁻¹ * (S.σ₂ * S.A) * S.u := by rw [h]
  have e1 : S.u⁻¹ * (S.A * S.σ₂) * S.u = S.a₂ * S.σ₁ := by
    calc S.u⁻¹ * (S.A * S.σ₂) * S.u = (S.u⁻¹ * S.A * S.u) * (S.u⁻¹ * S.σ₂ * S.u) := by group
      _ = S.a₂ * S.σ₁ := by rw [S.conj_u_σ₂]; rfl
  have e2 : S.u⁻¹ * (S.σ₂ * S.A) * S.u = S.σ₁ * S.a₂ := by
    calc S.u⁻¹ * (S.σ₂ * S.A) * S.u = (S.u⁻¹ * S.σ₂ * S.u) * (S.u⁻¹ * S.A * S.u) := by group
      _ = S.σ₁ * S.a₂ := by rw [S.conj_u_σ₂]; rfl
  rw [← e1, ← e2]
  exact e

theorem a₂σ₂_cube : S.a₂ * S.σ₂ * (S.a₂ * S.σ₂) * (S.a₂ * S.σ₂) = 1 := by
  have h := S.Aσ_cube
  calc S.a₂ * S.σ₂ * (S.a₂ * S.σ₂) * (S.a₂ * S.σ₂)
      = S.u⁻¹ * (S.A * S.σ₁ * (S.A * S.σ₁) * (S.A * S.σ₁)) * S.u := by
        unfold a₂ σ₂
        group
    _ = 1 := by rw [h]; group

theorem a₂_ne_one : S.a₂ ≠ 1 := by
  intro h1
  have := S.a₂_sq
  rw [h1, one_mul] at this
  exact zK_ne_one S.hyp this.symm

theorem a₂_not_comm_σ₂ : ¬ (S.a₂ * S.σ₂ = S.σ₂ * S.a₂) := by
  intro hc
  have hcomm : Commute S.a₂ S.σ₂ := hc
  have h3 : (S.a₂ * S.σ₂) ^ 3 = 1 := by
    rw [pow_three']
    exact S.a₂σ₂_cube
  have hs3 : S.σ₂ ^ 3 = 1 := by
    rw [pow_three']
    exact S.σ₂_cube
  rw [hcomm.mul_pow, hs3, mul_one] at h3
  have h4 : S.a₂ * S.a₂ * (S.a₂ * S.a₂) = 1 := by
    rw [S.a₂_sq, zK_mul_zK S.hyp]
  apply S.a₂_ne_one
  have h3' : S.a₂ * S.a₂ * S.a₂ = 1 := by
    rw [← pow_three']
    exact h3
  calc S.a₂ = (S.a₂ * S.a₂ * (S.a₂ * S.a₂)) * (S.a₂ * S.a₂ * S.a₂)⁻¹ := by group
    _ = 1 := by rw [h4, h3']; group

end JWSetup

end CFSG.Quasithin.H13.U43
