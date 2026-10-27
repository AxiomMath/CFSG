module

public import CFSG.Quasithin.Vol2.KGNatPointT
public import CFSG.Quasithin.Vol2.KGNatSL3Torus

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL
  specialLinearGroupEquivStatedSL_coe)

theorem g_e0_ne_zero {K : Type} [Field K] (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    (g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] ≠ 0 := by
  intro h0
  have := congrArg (fun x => ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) *ᵥ x) h0
  simp only [ginv_g_mulVec, Matrix.mulVec_zero] at this
  exact one_ne_zero (congrFun this 0)

theorem factPointTSL3_holds : Ch11.SecB.FactPointTSL3 := by
  intro K _ _ n hn hK W _ _ hW H π hπ P hP U hU S hS2 hSH hSU _
  have : CharP K 2 := charP_two_of_card (by omega) hK
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf hP
  rw [← hK] at hU
  have hUeq := eq_U1_of_isFlagW hW hf hg hU
  refine actsCyclicallyOn_point hf (fun T hT => commutant_statedSL (by norm_num) T hT)
    (g_e0_ne_zero g) (fun w => ?_) hS2 hSH hSU
  rw [hUeq, ← stdLine_eq_flagSpace]
  exact mem_gmap_stdLine_iff

end CFSG.Quasithin.Vol2.KGNat
