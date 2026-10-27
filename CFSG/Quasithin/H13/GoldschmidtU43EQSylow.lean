module

public import CFSG.Quasithin.H13.GoldschmidtU43EQFix
public import CFSG.Quasithin.H13.GoldschmidtU43EQGen
public import CFSG.Quasithin.H13.GoldschmidtU43EQRel

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem conj_mem_Uz {z : G} {x : ↥(Hz z)} {y : G} (hy : y ∈ Uz z) :
    (x : G) * y * (x : G)⁻¹ ∈ Uz z :=
  (Subgroup.mem_normalizer_iff.mp (Hz_le_normalizer z x.2) y).mp hy

namespace JWSetup

variable {z : G} (S : JWSetup z)

theorem b₂_not_mem_zpowers : S.b₂ ∉ Subgroup.zpowers S.a₂ := by
  intro hmem
  have h1 : zK z ≠ 1 := zK_ne_one S.hyp
  have hz2 : zK z * zK z = 1 := zK_mul_zK S.hyp
  have h4 : S.a₂ ^ 4 = 1 := by
    calc S.a₂ ^ 4 = (S.a₂ * S.a₂) * (S.a₂ * S.a₂) := u43_pow_four S.a₂
      _ = 1 := by rw [S.a₂_sq, hz2]
  rcases u43_mem_zpowers_of_pow_four h4 hmem with h | h | h | h
  · apply h1
    rw [← S.b₂_sq, h, one_mul]
  · apply h1
    have := S.a₂b₂_sq
    rw [h, S.a₂_sq, hz2] at this
    exact this.symm
  · apply h1
    have := S.b₂_sq
    rw [h, S.a₂_sq, hz2] at this
    exact this.symm
  · apply h1
    have := S.a₂b₂_sq
    rw [h, mul_inv_cancel, one_mul] at this
    exact this.symm

theorem b₂_conj_a₂ : S.b₂ * S.a₂ * S.b₂⁻¹ = S.a₂⁻¹ := by
  have hz2 : zK z * zK z = 1 := zK_mul_zK S.hyp
  have h1 : S.b₂ * S.a₂ * S.b₂ = S.a₂ := by
    have e : S.a₂ * (S.b₂ * S.a₂ * S.b₂) = S.a₂ * S.a₂ := by
      calc S.a₂ * (S.b₂ * S.a₂ * S.b₂) = (S.a₂ * S.b₂) * (S.a₂ * S.b₂) := by group
        _ = zK z := S.a₂b₂_sq
        _ = S.a₂ * S.a₂ := S.a₂_sq.symm
    exact mul_left_cancel e
  have hz : S.b₂⁻¹ = S.b₂ * zK z := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, S.b₂_sq, hz2]
  have e1 : S.b₂ * S.a₂ * S.b₂⁻¹ = (S.b₂ * S.a₂ * S.b₂) * zK z := by
    rw [hz]
    group
  calc S.b₂ * S.a₂ * S.b₂⁻¹ = (S.b₂ * S.a₂ * S.b₂) * zK z := e1
    _ = S.a₂ * zK z := by rw [h1]
    _ = S.a₂⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        calc S.a₂ * zK z * S.a₂ = zK z * (S.a₂ * S.a₂) := by rw [← zK_comm S.a₂]; group
          _ = 1 := by rw [S.a₂_sq, hz2]

theorem a₂_mem_U (hAU : (S.A : G) ∈ Uz z) : ((S.a₂ : ↥(Hz z)) : G) ∈ Uz z := by
  have := conj_mem_Uz (z := z) (x := S.u⁻¹) hAU
  simpa [a₂] using this

theorem b₂_mem_U (hAU : (S.A : G) ∈ Uz z) : ((S.b₂ : ↥(Hz z)) : G) ∈ Uz z := by
  have := conj_mem_Uz (z := z) (x := S.σ₂⁻¹) (S.a₂_mem_U hAU)
  simpa [b₂] using this

theorem a₂_mem_Cg1 : ((S.a₂ : ↥(Hz z)) : G) ∈ S.Cg1 := by
  rw [Cg1, Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val S.a₂_comm_σ₁

theorem b₂_comm_σ₁ : S.b₂ * S.σ₁ = S.σ₁ * S.b₂ := by
  have c1 : S.σ₂ * S.σ₁ = S.σ₁ * S.σ₂ := S.σ₁σ₂_comm.symm
  have c2 : S.σ₂⁻¹ * S.σ₁ = S.σ₁ * S.σ₂⁻¹ := by
    calc S.σ₂⁻¹ * S.σ₁ = S.σ₂⁻¹ * (S.σ₁ * S.σ₂) * S.σ₂⁻¹ := by group
      _ = S.σ₂⁻¹ * (S.σ₂ * S.σ₁) * S.σ₂⁻¹ := by rw [c1]
      _ = S.σ₁ * S.σ₂⁻¹ := by group
  calc S.b₂ * S.σ₁ = S.σ₂⁻¹ * S.a₂ * (S.σ₂ * S.σ₁) := by unfold b₂; group
    _ = S.σ₂⁻¹ * S.a₂ * (S.σ₁ * S.σ₂) := by rw [c1]
    _ = S.σ₂⁻¹ * (S.a₂ * S.σ₁) * S.σ₂ := by group
    _ = S.σ₂⁻¹ * (S.σ₁ * S.a₂) * S.σ₂ := by rw [S.a₂_comm_σ₁]
    _ = (S.σ₂⁻¹ * S.σ₁) * S.a₂ * S.σ₂ := by group
    _ = (S.σ₁ * S.σ₂⁻¹) * S.a₂ * S.σ₂ := by rw [c2]
    _ = S.σ₁ * S.b₂ := by unfold b₂; group

theorem b₂_mem_Cg1 : ((S.b₂ : ↥(Hz z)) : G) ∈ S.Cg1 := by
  rw [Cg1, Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val S.b₂_comm_σ₁

theorem orderOf_a₂ : orderOf S.a₂ = 4 := by
  have hz2 : zK z * zK z = 1 := zK_mul_zK S.hyp
  have h4 : S.a₂ ^ 2 ^ (1 + 1) = 1 := by
    rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num]
    calc S.a₂ ^ 4 = (S.a₂ * S.a₂) * (S.a₂ * S.a₂) := u43_pow_four S.a₂
      _ = 1 := by rw [S.a₂_sq, hz2]
  have h2 : ¬ S.a₂ ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two, S.a₂_sq]
    exact zK_ne_one S.hyp
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := S.a₂) h2 h4
  simpa using this

end JWSetup

end CFSG.Quasithin.H13.U43
