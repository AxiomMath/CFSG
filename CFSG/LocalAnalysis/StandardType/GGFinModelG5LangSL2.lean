module

public import CFSG.LocalAnalysis.StandardType.GGFinModelRat
public import CFSG.LieType.Chevalley.LangRootRankOne

public section

namespace CFSG.StandardType.GGFinModel.G5

open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.Assembly CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank

private theorem g5_neg_eq_self (x : GGL) : -x = x := by
  have h2 : (2 : GGL) = 0 := CharP.cast_eq_zero GGL 2
  have hxx : x + x = 0 := by
    calc x + x = (2 : GGL) * x := by ring
      _ = 0 := by rw [h2, zero_mul]
  exact (add_eq_zero_iff_eq_neg.mp hxx).symm

private theorem g5_add_one_add_one (x : GGL) : x + 1 + 1 = x := by
  have h2 : (2 : GGL) = 0 := CharP.cast_eq_zero GGL 2
  have h11 : (1 : GGL) + 1 = 0 := by
    calc (1 : GGL) + 1 = (2 : GGL) * 1 := by ring
      _ = 0 := by rw [h2, zero_mul]
  rw [add_assoc, h11, add_zero]

theorem ggLang_sl2 {f : ℕ} (hf : 1 ≤ f) :
    ∃ z : SL2 GGL, Matrix.SpecialLinearGroup.map (ggFrobT f) z = z * nSL (1 : GGLˣ) := by
  have h2 : (2 : GGL) = 0 := CharP.cast_eq_zero GGL 2
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  have hpow : 1 < 2 ^ f := by
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hdeg : (Polynomial.X ^ (2 ^ f) + Polynomial.X + 1 : Polynomial GGL).degree ≠ 0 := by
    have hlt : (Polynomial.X + 1 : Polynomial GGL).degree <
        (Polynomial.X ^ (2 ^ f) : Polynomial GGL).degree := by
      rw [show (Polynomial.X + 1 : Polynomial GGL) = Polynomial.X + Polynomial.C 1 by simp,
        Polynomial.degree_X_add_C, Polynomial.degree_X_pow]
      exact WithBot.coe_lt_coe.mpr hpow
    have hd := Polynomial.degree_add_eq_left_of_degree_lt hlt
    rw [show (Polynomial.X ^ (2 ^ f) + Polynomial.X + 1 : Polynomial GGL) =
      Polynomial.X ^ (2 ^ f) + (Polynomial.X + 1) by ring, hd, Polynomial.degree_X_pow]
    exact ne_of_gt (WithBot.coe_lt_coe.mpr (Nat.two_pow_pos f))
  obtain ⟨l, hl⟩ := IsAlgClosed.exists_root
    (Polynomial.X ^ (2 ^ f) + Polynomial.X + 1 : Polynomial GGL) hdeg
  have hlq : l ^ 2 ^ f = l + 1 := by
    have hsum : l ^ 2 ^ f + (l + 1) = 0 := by
      have h := hl
      simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one] at h
      simpa only [add_assoc] using h
    have hneg := add_eq_zero_iff_eq_neg.mp hsum
    simpa only [g5_neg_eq_self (l + 1)] using hneg
  let z : SL2 GGL := ⟨!![1, 1; l, l + 1], by simp [Matrix.det_fin_two]⟩
  refine ⟨z, ?_⟩
  apply Subtype.ext
  show (↑(Matrix.SpecialLinearGroup.map (ggFrobT f) z) : Matrix (Fin 2) (Fin 2) GGL) =
    (↑(z * nSL (1 : GGLˣ)) : Matrix (Fin 2) (Fin 2) GGL)
  rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [z, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two, nSL,
      ggFrobT_apply, hlq, add_pow_char_pow, g5_neg_eq_self, g5_add_one_add_one, one_pow]

end CFSG.StandardType.GGFinModel.G5
