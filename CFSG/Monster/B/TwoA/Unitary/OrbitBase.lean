
module

public import CFSG.Monster.B.TwoA.Unitary.ActionBase
public import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Unitary.NData
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Unitary.OrbitInputs
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Unitary.Bridge
public import CFSG.Monster.B.TwoA.Unitary.ActionInputs

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.VisQuot CFSG.Monster.VisCert
  CFSG.Monster.SpinLattice CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census

@[expose] def n6vec (j : Fin 891) : Wv v0 := decW n6VecArr[(j : ℕ)]!

theorem n6Vec_size : n6VecArr.size = 891 := by decide +kernel

theorem n6Vec_zero : n6VecArr[0]! = 31 := by decide +kernel

theorem n6Rows_fix_sigma : ∀ k < 17, Native.actD 22 n6RowArr[k]! 6144 = 6144 := by
  decide +kernel

theorem n6vec_zero :
    n6vec 0 = wFr := by
  rw [n6vec, wFr_eq_decW]
  exact congrArg decW n6Vec_zero

theorem sigmaCls_eq_dec : sigmaCls = dec 20480 :=
  cls_pairN_eq (by decide) (pairN_eq 0 2 (by decide)) (by decide +kernel)

theorem sigmaW_eq_decW :
    sigmaW = decW 6144 := by
  obtain ⟨hm, he⟩ := decW_eq_mk 6144
  rw [he, sigmaW]
  congr 1
  apply Subtype.ext
  change sigmaCls = dec (Native.actD 22 Native.quotientBasis 6144)
  rw [show Native.actD 22 Native.quotientBasis 6144 = 20480 by decide, sigmaCls_eq_dec]

attribute [local instance] wLeftAction

end CFSG.Monster.B.TwoA.Unitary
