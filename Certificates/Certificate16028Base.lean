
module

public import CFSG.Monster.B.TwoA.Sp8.PsiInputs
public import CFSG.Monster.B.TwoA.Base.WCls
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Monster.B.TwoA.Co2Inv.RowsInputs
public import Certificates.Data.BT2K1Vocab

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Griess
  CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371 CFSG.Monster.B.TwoA.Census
  CFSG.Monster.VisCert CFSG.Monster.B.Co2

public section


open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Griess
  CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371 CFSG.Monster.B.TwoA.Census
  CFSG.Monster.VisCert CFSG.Monster.B.Co2

namespace CertificateChecks.Batch16028

private theorem pairW24_eq_decW_0 :
    rowCheck (pairN (2 : Fin 24) (4 : Fin 24)) 81920 = true := by
  decide +kernel

private theorem pairW25_eq_decW_1 :
    rowCheck (pairN (2 : Fin 24) (5 : Fin 24)) 147456 = true := by
  decide +kernel

private theorem pairW26_eq_decW_2 :
    rowCheck (pairN (2 : Fin 24) (6 : Fin 24)) 278528 = true := by
  decide +kernel

private theorem lamX_form_eq_3 :
    (fun k : Fin 24 => if P ((dC : C) : Fin 24 → ZMod 2) = 0 then
      2 * bitLift (((dC : C) : Fin 24 → ZMod 2) k) else
      2 * (1 - bitLift (((dC : C) : Fin 24 → ZMod 2) k))) = fun k : Fin 24 => twoD k := by
  decide +kernel

end CertificateChecks.Batch16028

namespace Certificates

end Certificates
