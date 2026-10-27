
module

public import CFSG.Monster.B.TwoA.Sp8.QuadDataBase

public import CFSG.Monster.B.TwoA.Sp8.Data
public import CFSG.Monster.B.TwoA.Base.RankThreePar

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv

@[expose] def P4 :
    Subgroup Dfull := Xgrp ⊓ Subgroup.centralizer {cQ}

theorem P4_le_Xgrp :
    P4 ≤ Xgrp := inf_le_left

@[expose] def T9 :
    Subgroup Dfull := Subgroup.closure (insert cQ (A8 : Set Dfull))

theorem T9_le_Shat :
    T9 ≤ Shat := by
  rw [T9, Subgroup.closure_le]
  rintro x (rfl | hx)
  · exact cQ_mem_Shat
  · exact A8_le_Shat hx

theorem short_quadratic_involution_data :
    cQ = iotaD (kappa ⟨rhoEquiv (DQ (deltaPair 0 2)), rhoEquiv_mem_Cgen (DQ_mem_centralizer _)⟩) ∧
    T9 = Subgroup.closure (insert cQ (A8 : Set Dfull)) ∧ T9 ≤ Shat ∧
    P4 = Xgrp ⊓ Subgroup.centralizer {cQ} ∧
    K3 = Subgroup.normalizer (E3 : Set Dfull) ∧ P3 = K3 ⊓ Subgroup.centralizer {cQ} ∧
    R3 = (CFSG.pCore 2 K3).map K3.subtype ∧
    ∀ v : Fin 8 → ZMod 2, qPoly v = (∑ i : Fin 8, ∑ j : Fin 8,
      if i < j then b0 (Pi.single i 1) (Pi.single j 1) * v i * v j else 0) + v 6 + v 7 :=
  ⟨rfl, rfl, T9_le_Shat, rfl, rfl, rfl, R3_eq_pCore_K3, qPoly_eq⟩

end CFSG.Monster.B.TwoA.Sp8
