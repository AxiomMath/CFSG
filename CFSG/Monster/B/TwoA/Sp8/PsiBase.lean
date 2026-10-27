
module

public import CFSG.Monster.B.TwoA.Base.PsiV
public import CFSG.Monster.B.TwoA.Co2Inv.Data

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371
  CFSG.Monster.B.TwoA.Census CFSG.Monster.VisCert CFSG.Monster.B.Co2

theorem offPair24 : OffPair 2 4 := ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem offPair25 : OffPair 2 5 := ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem offPair26 : OffPair 2 6 := ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem psiW_yhat8 :
    psiW yhatE = decW 31 := psiW_yhat.trans wFr_eq_decW

theorem psiW_d23 :
    psiW (dhatE 2 3) = decW 12288 :=
  (psiW_dhat (by decide) offPair23).trans pairW23_eq_decW

end CFSG.Monster.B.TwoA.Sp8
