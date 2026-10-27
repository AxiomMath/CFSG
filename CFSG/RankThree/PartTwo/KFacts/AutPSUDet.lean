module

public import CFSG.RankThree.PartTwo.KFacts.AutPSU

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.LocalAnalysis.ComponentInitial Matrix

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem norm_det_of_mem_unitaryIsom3 {A : GL (Fin 3) K} (hA : A ∈ unitaryIsom3 h) :
    h.norm (A : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  have h1 := congrArg Matrix.det (mem_unitaryIsom3.mp hA)
  rw [det_mul, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_one] at h1
  rw [UnitaryFieldData.norm, mul_comm]
  exact h1

end CFSG.RankThree.PartTwo.KFacts
