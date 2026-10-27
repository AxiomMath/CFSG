module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.Assembly.LowTwoRank (StatedSp)
open Matrix
open scoped Matrix

abbrev H8 : Type :=
  ↥(StatedSp 4 (ZMod 2))

@[expose] def sm8 (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) :
    Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  M.submatrix finSumFinEquiv finSumFinEquiv

@[expose] def mk8 (M Mi : Matrix (Fin 8) (Fin 8) (ZMod 2))
    (h : sm8 M * sm8 Mi = 1 ∧ sm8 Mi * sm8 M = 1 ∧
      (sm8 M)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm8 M = Matrix.fromBlocks 0 1 (-1) 0) : H8 :=
  ⟨⟨sm8 M, sm8 Mi, h.1, h.2.1⟩, Subgroup.subset_closure h.2.2⟩

@[expose] def sp8Z0M : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 0, 0, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def sp8Z0Mi : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def sp8Z1M : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def sp8Z1Mi : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def sp8Z2M : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def sp8Z2Mi : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def sp8EM : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 0, 0, 0, 1]

@[expose] def sp8EMi : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 1;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 0, 0, 0, 0]

@[expose] def sp8TM : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 0, 1, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def sp8TMi : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def sp8FM : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 0, 0, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def sp8SM : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 0, 0, 1, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1, 0, 0, 0]

theorem sp8Z0_check : sm8 sp8Z0M * sm8 sp8Z0Mi = 1 ∧ sm8 sp8Z0Mi * sm8 sp8Z0M = 1 ∧
    (sm8 sp8Z0M)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm8 sp8Z0M = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

theorem sp8Z1_check : sm8 sp8Z1M * sm8 sp8Z1Mi = 1 ∧ sm8 sp8Z1Mi * sm8 sp8Z1M = 1 ∧
    (sm8 sp8Z1M)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm8 sp8Z1M = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

theorem sp8Z2_check : sm8 sp8Z2M * sm8 sp8Z2Mi = 1 ∧ sm8 sp8Z2Mi * sm8 sp8Z2M = 1 ∧
    (sm8 sp8Z2M)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm8 sp8Z2M = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

theorem sp8E_check : sm8 sp8EM * sm8 sp8EMi = 1 ∧ sm8 sp8EMi * sm8 sp8EM = 1 ∧
    (sm8 sp8EM)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm8 sp8EM = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

theorem sp8T_check : sm8 sp8TM * sm8 sp8TMi = 1 ∧ sm8 sp8TMi * sm8 sp8TM = 1 ∧
    (sm8 sp8TM)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm8 sp8TM = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

theorem sp8F_check : sm8 sp8FM * sm8 sp8FM = 1 ∧ sm8 sp8FM * sm8 sp8FM = 1 ∧
    (sm8 sp8FM)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm8 sp8FM = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

theorem sp8S_check : sm8 sp8SM * sm8 sp8SM = 1 ∧ sm8 sp8SM * sm8 sp8SM = 1 ∧
    (sm8 sp8SM)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm8 sp8SM = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

@[expose] def sp8Z : Fin 3 → H8 :=
  ![mk8 sp8Z0M sp8Z0Mi sp8Z0_check, mk8 sp8Z1M sp8Z1Mi sp8Z1_check,
    mk8 sp8Z2M sp8Z2Mi sp8Z2_check]

@[expose] def sp8T : H8 := mk8 sp8TM sp8TMi sp8T_check

@[expose] def sp8E : H8 := mk8 sp8EM sp8EMi sp8E_check

@[expose] def sp8F : H8 := mk8 sp8FM sp8FM sp8F_check

@[expose] def sp8S : H8 := mk8 sp8SM sp8SM sp8S_check

end CFSG.RankThree.PartTwo.Sec4.RonanK432
