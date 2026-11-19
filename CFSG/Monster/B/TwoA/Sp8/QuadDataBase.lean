
module

public import CFSG.Monster.B.TwoA.Sp8.DataBase
public import CFSG.Monster.B.TwoA.Base.RankThreeBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv

def cQ : Dfull := dhat 0 2

def P3 : Subgroup Dfull := K3 ⊓ Subgroup.centralizer {cQ}

theorem cQ_mem_Ehat : cQ ∈ Ehat := dhat_mem_Ehat 0 2

theorem cQ_mem_Shat : cQ ∈ Shat := Ehat_le_Shat cQ_mem_Ehat

theorem P3_le_K3 : P3 ≤ K3 := inf_le_left

theorem gram0_apply (i j : Fin 8) : gram0 i j = b0 (Pi.single i 1) (Pi.single j 1) := by
  rw [b0_single, gram0, Matrix.of_apply]

theorem qPoly_eq (v : Fin 8 → ZMod 2) :
    qPoly v = (∑ i : Fin 8, ∑ j : Fin 8,
      if i < j then b0 (Pi.single i 1) (Pi.single j 1) * v i * v j else 0) + v 6 + v 7 := by
  simp only [qPoly, gram0_apply]

end CFSG.Monster.B.TwoA.Sp8
