module

public import CFSG.RankThree.GF2n.Smith81.S81A5Cent

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix exteriorPower

variable {K : Type*} [Field K]

theorem rho_sub_one_ιMulti {t : GL (Fin 6) K} {a f : Fin 6 → K}
    (ht : (t : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a f) (x₀ x₁ x₂ : Fin 6 → K) :
    rho K t (ιMulti K 3 ![x₀, x₁, x₂]) - ιMulti K 3 ![x₀, x₁, x₂] =
      (f ⬝ᵥ x₀) • ιMulti K 3 ![a, x₁, x₂] + (f ⬝ᵥ x₁) • ιMulti K 3 ![x₀, a, x₂] +
        (f ⬝ᵥ x₂) • ιMulti K 3 ![x₀, x₁, a] := by
  have hrt : ∀ x : Fin 6 → K, (t : Matrix (Fin 6) (Fin 6) K).mulVec x = x + (f ⬝ᵥ x) • a := by
    intro x
    rw [ht, Matrix.add_mulVec, Matrix.one_mulVec, fe3_vecMulVec_mulVec]
  have hfun : (fun i => (t : Matrix (Fin 6) (Fin 6) K).mulVec (![x₀, x₁, x₂] i)) =
      ![x₀ + (f ⬝ᵥ x₀) • a, x₁ + (f ⬝ᵥ x₁) • a, x₂ + (f ⬝ᵥ x₂) • a] := by
    funext i
    fin_cases i
    · exact hrt x₀
    · exact hrt x₁
    · exact hrt x₂
  rw [rho_ιMulti, hfun]
  simp only [ι3_add_fst, ι3_add_snd, ι3_add_thd, ι3_smul_fst, ι3_smul_snd, ι3_smul_thd,
    ι3_eq_fst_snd, ι3_eq_fst_thd, ι3_eq_snd_thd, smul_zero, add_zero, zero_add]
  module

end CFSG.RankThree.GF2n.Smith81.A5Cube
