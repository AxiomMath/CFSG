module

public import CFSG.Quasithin.Vol2.GoldschmidtE217NCAbs
public import CFSG.Quasithin.Vol2.Ch3E213MOLA6

public section

namespace CFSG.Quasithin

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
open scoped MatrixGroups

namespace E217R3

@[expose] def unipLin (F : Type) [Field F] : SL(3, F) :=
  ⟨!![1, 0, -2; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem not_oddCube_lin {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hp5 : 5 ≤ p) (hF : Nat.card F = p) {E : Type} [Group E] (θ : SL(3, F) →* E)
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center SL(3, F)) {z : E}
    (hz : orderOf z = 2) : ¬ OddCube z := by
  have hp : p.Prime := Fact.out
  have h2 : (2 : F) ≠ 0 := Models.two_ne_zero_of_charP_ne_two (p := p) (by omega)
  have hodd : Odd (Nat.card F) := hF ▸ hp.odd_of_ne_two (by omega)
  set D : SL(3, F) := Models.rootInv F (n := 3) (by norm_num) with hD
  set Y : SL(3, F) := unipLin F with hY
  have hDm : (D : Matrix (Fin 3) (Fin 3) F) = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] :=
    coe_rootInv_three
  have hYm : (Y : Matrix (Fin 3) (Fin 3) F) = !![1, 0, -2; 0, 1, 0; 0, 0, 1] := rfl
  have hDD : D * D = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, hDm, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hu₁ : (D * Y) * (D * Y) = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_one, hDm, hYm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hDY : D * (D * Y) = Y := by rw [← mul_assoc, hDD, one_mul]
  have hnc : D * (D * Y) ≠ (D * Y) * D := by
    rw [hDY]
    intro h
    have h' := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F) 0 2) h
    simp only [Matrix.SpecialLinearGroup.coe_mul, hDm, hYm] at h'
    simp [Matrix.mul_apply, Fin.sum_univ_three] at h'
    apply h2
    have h4 : (2 : F) * 2 = 0 := by linear_combination -h'
    exact mul_self_eq_zero.1 h4
  have hy : (D * (D * Y)) ^ p = 1 := by
    rw [hDY]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hYm, Matrix.SpecialLinearGroup.coe_one]
    have hN2 : (!![0, 0, -2; 0, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) F) *
        !![0, 0, -2; 0, 0, 0; 0, 0, 0] = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    have hN : (!![0, 0, -2; 0, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) F) ^ 3 = 0 := by
      rw [pow_succ, pow_two, hN2, zero_mul]
    have hsplit : (!![1, 0, -2; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) =
        1 + !![0, 0, -2; 0, 0, 0; 0, 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hsplit]
    exact pow_eq_one_of_pow_three_eq_zero (by omega) hN
  have hconj : ∀ t s : E, orderOf t = 2 → orderOf s = 2 → ∃ g : E, t = g * s * g⁻¹ := by
    intro t s ht hs
    obtain ⟨g₁, hg₁⟩ := CFSG.Quasithin.Ch3E213M.OLA.lin_conj_inv hodd θ hθ hker t ht
    obtain ⟨g₂, hg₂⟩ := CFSG.Quasithin.Ch3E213M.OLA.lin_conj_inv hodd θ hθ hker s hs
    refine ⟨g₁ * g₂⁻¹, ?_⟩
    rw [hg₁, hg₂]
    group
  exact not_oddCube_of_pair θ hker hp hp5 hDD hu₁ hnc hconj hy hz

end E217R3

end CFSG.Quasithin
