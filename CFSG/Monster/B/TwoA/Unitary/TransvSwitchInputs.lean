module

public import CFSG.Monster.B.TwoA.Unitary.Transv
public meta import CFSG.Monster.B.TwoA.Unitary.Planes
public meta import CFSG.Monster.B.TwoA.Unitary.Form
public meta import CFSG.Monster.B.TwoA.Unitary.NData
public meta import CFSG.Monster.B.TwoA.Co2Inv.Rows
public meta import CFSG.Monster.B.Co2.Data
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import Certificates.Certificate3026
public import Certificates.Certificate3028
import CFSG.Fischer.F4

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Fischer CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Co2Inv Matrix Module
open CFSG.Monster.B.Classical.UnitarySix (bar bar_one)
open CFSG.Monster.B.TwoA.Amalgam (e6)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU)

@[expose] def alphaKv (i : Fin 24) :
    Kstab v0 := ⟨CFSG.Monster.B.Co2.alpha i, alpha_mem_Kv i⟩

@[expose] def swG :
    Kstab v0 := alphaKv 4 * alphaKv 12 * alphaKv 23 * alphaKv 7

@[expose] def swGRows : Array ℕ :=
  Co2Inv.rowsMul
    (Co2Inv.rowsMul (Co2Inv.rowsMul (genQuotMatrix 4) (genQuotMatrix 12)) (genQuotMatrix 23))
    (genQuotMatrix 7)

@[expose] def swGInvRows : Array ℕ :=
  #[1256770, 2324267, 3672493, 3347298, 1329337, 3277438, 731605, 2164540, 2182946, 1271062,
    2151836, 3098942, 3098882, 16384, 2794977, 3768638, 832193, 3094300, 65536, 2242818, 3162370,
    2599617]

@[expose] def swQRows : Array ℕ :=
  Co2Inv.rowsMul (Co2Inv.rowsMul swGInvRows (genQuotMatrix 12)) swGRows

@[expose] def swRows6 : Array ℕ := #[5, 4, 29, 1092, 3393, 1024]

@[expose] def swMat : Matrix (Fin 6) (Fin 6) F4 := Matrix.of fun i => vec6 swRows6[(i : ℕ)]!

@[expose] def swIdx (j : Fin 891) : Fin 891 :=
  ⟨n6VecArr.toList.idxOf (Native.actD 22 swQRows n6VecArr[(j : ℕ)]!) % 891,
    Nat.mod_lt _ (by norm_num)⟩

end CFSG.Monster.B.TwoA.Unitary
