module

public import Certificates.Certificate733004
public import Certificates.Data.G24IdentLin
import CFSG.Certificates.Kernel.G24LinQSound
import Certificates.Data.Kernel.G24LinK
import Certificates.Kernel.G24IdLin.Rec
import CFSG.Certificates.Kernel.Common.Harness
meta import Certificates.Kernel.Misc.Perm.CharsCatList
import Init.Data.Range.Basic
import Init.Data.Nat.Fold
import Init.Data.Array.Basic
import Init.Data.List.Basic
public import Certificates.Certificate733006

public section

namespace CFSG.Quasithin.St84

theorem pc_checkA :
    Finite (CFSG.CosetTable.PG 3 G24Pc.relsA) ∧ Nat.card (CFSG.CosetTable.PG 3 G24Pc.relsA) ≤ 180 :=
  Certificates.certificate733004.1

theorem pc_checkQ1 :
    Finite (CFSG.CosetTable.PG 10 G24Pc.relsQ1) ∧
      Nat.card (CFSG.CosetTable.PG 10 G24Pc.relsQ1) ≤ 1024 :=
  Certificates.certificate733004.2.1

theorem wit_check : G24Wit.witCheck () = true :=
  Certificates.certificate733006

end CFSG.Quasithin.St84
