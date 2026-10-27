module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138P5

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup)
open Matrix
open CFSG.LocalAnalysis.ComponentInitial

section Mat

variable {K : Type} [Field K]

@[expose] def negSwap01 : GL (Fin 3) K :=
  ⟨!![0, -1, 0; -1, 0, 0; 0, 0, -1], !![0, -1, 0; -1, 0, 0; 0, 0, -1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]⟩

theorem coe_negSwap01 :
    ((negSwap01 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![0, -1, 0; -1, 0, 0; 0, 0, -1] :=
  rfl

variable {p f : ℕ}

theorem negSwap01_mem_slPi {π : Bool} (hπ : π = false → UnitaryFieldData p f K) :
    negSwap01 ∈ slPi π 3 (p ^ f) K := by
  have hdet : ((negSwap01 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [coe_negSwap01, det_fin_three]
    simp
  cases π
  · have h := hπ rfl
    rw [mem_slPi_false h]
    refine ⟨hdet, ?_⟩
    rw [coe_negSwap01]
    ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, transpose_apply]
  · rw [mem_slPi_true]
    exact hdet

end Mat

variable {G : Type} [Group G] [Finite G]

end CFSG.RankThree.PartTwo.Sec13.Ronan138P5
