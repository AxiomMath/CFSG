module

public import CFSG.RankThree.GF2n.Smith81.S81A5Cent
public import CFSG.CGT.Timmesfeld75.ListWCLinMain
public import CFSG.CGT.Timmesfeld75.SLTransvectionOrder

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix CFSG.CGT.Timmesfeld75

variable {K : Type} [Field K]

private theorem det_one_add_vecMulVec' (p r : Fin 6 → K) :
    (1 + vecMulVec p r).det = 1 + r ⬝ᵥ p := by
  rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow]

theorem exists_sl_of_isTransvec {g : GL (Fin 6) K} (hg : IsTransvec K g) :
    ∃ u : Matrix.SpecialLinearGroup (Fin 6) K, IsTransvection u ∧
      Matrix.SpecialLinearGroup.toGL u = g := by
  obtain ⟨a, f, ha, hf, hfa, hg1⟩ := IsTransvec.exists hg
  have hdet : (g : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    rw [hg1, det_one_add_vecMulVec', hfa, add_zero]
  exact ⟨⟨g, hdet⟩, isTransvection_of_coe ha hf hfa hg1, Units.ext rfl⟩

theorem orderOf_mul_cases_gl [Finite K] [CharP K 2] {gx gy : GL (Fin 6) K} (hx : IsTransvec K gx)
    (hy : IsTransvec K gy) : orderOf (gx * gy) ∣ 4 ∨ Odd (orderOf (gx * gy)) := by
  obtain ⟨u₁, hu₁, rfl⟩ := exists_sl_of_isTransvec hx
  obtain ⟨u₂, hu₂, rfl⟩ := exists_sl_of_isTransvec hy
  rw [← map_mul, orderOf_injective Matrix.SpecialLinearGroup.toGL
    Matrix.SpecialLinearGroup.toGL_injective]
  exact hu₁.orderOf_mul_cases hu₂

end CFSG.RankThree.GF2n.Smith81.A5Cube
