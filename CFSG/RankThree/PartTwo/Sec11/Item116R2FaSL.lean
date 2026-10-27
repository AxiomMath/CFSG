module

public import CFSG.RankThree.PartTwo.Sec11.Item116R2Heis
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankClsThree

public section

open Subgroup CFSG.Assembly.LowTwoRank CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls

namespace CFSG.RankThree.PartTwo.Sec11

theorem exists_heisenberg_statedSL {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 1) :
    ∃ H : Subgroup (StatedSL 3 K), IsPGroup 3 H ∧
      ∃ x ∈ H, ∃ y ∈ H, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x := by
  obtain ⟨ω, hω3, hω1⟩ := exists_cube_root_of_three_dvd (K := K) (by
    have : 0 < Nat.card K := Nat.card_pos
    omega)
  have hsc3 : (Matrix.scalar (Fin 3) ω : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← map_pow, hω3, map_one]
  have hdS : glOfPowThree (cubeDiag ω) (cubeDiag_pow_three hω3) ∈ StatedSL 3 K :=
    Subgroup.subset_closure (by simpa [coe_glOfPowThree] using det_cubeDiag hω3)
  have hPS : glOfPowThree (cycMat : Matrix (Fin 3) (Fin 3) K) cycMat_pow_three ∈ StatedSL 3 K :=
    Subgroup.subset_closure (by simpa [coe_glOfPowThree] using det_cycMat (K := K))
  have hzS : glOfPowThree (Matrix.scalar (Fin 3) ω) hsc3 ∈ StatedSL 3 K :=
    Subgroup.subset_closure (by
      simpa [coe_glOfPowThree, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_three,
        pow_succ] using hω3)
  obtain ⟨d, hd⟩ : ∃ d : StatedSL 3 K,
      (d : GL (Fin 3) K) = glOfPowThree (cubeDiag ω) (cubeDiag_pow_three hω3) :=
    ⟨⟨_, hdS⟩, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : StatedSL 3 K,
      (P : GL (Fin 3) K) = glOfPowThree (cycMat : Matrix (Fin 3) (Fin 3) K) cycMat_pow_three :=
    ⟨⟨_, hPS⟩, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : StatedSL 3 K,
      (z : GL (Fin 3) K) = glOfPowThree (Matrix.scalar (Fin 3) ω) hsc3 :=
    ⟨⟨_, hzS⟩, rfl⟩
  have hd3 : d ^ 3 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, hd, Subgroup.coe_one]
    exact glOfPowThree_pow_three _ _)
  have hP3 : P ^ 3 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, hP, Subgroup.coe_one]
    exact glOfPowThree_pow_three _ _)
  have hz3 : z ^ 3 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, hz, Subgroup.coe_one]
    exact glOfPowThree_pow_three _ _)
  have hzd : z * d = d * z := Subtype.ext (Units.ext (by
    simp only [Subgroup.coe_mul, Units.val_mul, hz, hd, coe_glOfPowThree]
    exact Matrix.scalar_comm ω (fun _ => mul_comm _ _) _))
  have hzP : z * P = P * z := Subtype.ext (Units.ext (by
    simp only [Subgroup.coe_mul, Units.val_mul, hz, hP, coe_glOfPowThree]
    exact Matrix.scalar_comm ω (fun _ => mul_comm _ _) _))
  have hdP : d * P = P * d * z := Subtype.ext (Units.ext (by
    simp only [Subgroup.coe_mul, Units.val_mul, hz, hd, hP, coe_glOfPowThree,
      Matrix.scalar_apply]
    exact cycMat_mul_cubeDiag hω3))
  refine ⟨Subgroup.closure ({d, P, z} : Set (StatedSL 3 K)),
    isPGroup_closure_heisenberg hd3 hP3 hz3 hzd hzP hdP,
    d, Subgroup.subset_closure (by simp), P, Subgroup.subset_closure (by simp), hd3, hP3, ?_⟩
  intro h
  have h2 : P * d * z = P * d * 1 := by
    rw [mul_one, ← hdP]
    exact h
  have hz1 : z = 1 := mul_left_cancel h2
  have hz1' : glOfPowThree (Matrix.scalar (Fin 3) ω) hsc3 = 1 := by
    rw [← hz]
    simp [hz1]
  have hm : (Matrix.scalar (Fin 3) ω : Matrix (Fin 3) (Fin 3) K) = 1 :=
    congrArg Units.val hz1'
  have h00 := congrFun (congrFun hm 0) 0
  simp at h00
  exact hω1 h00

end CFSG.RankThree.PartTwo.Sec11
