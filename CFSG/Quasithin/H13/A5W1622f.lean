module

public import CFSG.Quasithin.Background.G2SL3
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Core
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch6Semilinear

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.SL3Model (natAct3 natAct3_apply)

variable {F : Type} [Field F]

@[expose] def u01 : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def u12 : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem u01_mem : u01 ∈ unitriangular 3 F := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [u01]
  · fin_cases i <;> simp [u01]

theorem u12_mem : u12 ∈ unitriangular 3 F := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [u12]
  · fin_cases i <;> simp [u12]

theorem fixed_unitriangular {v : Fin 3 → F} (h : ∀ A ∈ unitriangular 3 F, A • v = v) :
    v 1 = 0 ∧ v 2 = 0 := by
  have h1 := congrFun (h u01 u01_mem) 0
  have h2 := congrFun (h u12 u12_mem) 1
  change (((u01 : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 0 = v 0 at h1
  change (((u12 : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 1 = v 1 at h2
  simp [u01, u12, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1 h2
  exact ⟨h1, h2⟩

end CFSG.Quasithin.H13.A5
