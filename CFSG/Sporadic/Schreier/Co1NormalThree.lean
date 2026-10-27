module

public import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
import Init.Data.Nat.Fold
import Init.Data.Array.Basic
import Init.Data.Range.Basic
public import CFSG.Sporadic.Schreier.Co1EigenPlanes
public import Certificates.Certificate2133
public import Certificates.Certificate2150
public import Certificates.Certificate3024

public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.Sporadic.SmallF2 (rowsMatrix)
open ThreeLocal Matrix

namespace NormalThree

theorem ne_one_of_rep {X : Native.Rows} {g : GL24} (h : MRep X g) (hX : Native.wf X = true)
    (hone : Native.wf Native.one = true) (hne : X ≠ Native.one) : g ≠ 1 := by
  rintro rfl
  exact hne (rowsMatrix_injective_of_wf hX hone (h.trans MRep.one.symm))

theorem eq_one_of_rep {X : Native.Rows} {g : GL24} (h : MRep X g) (he : X = Native.one) :
    g = 1 := by
  rw [he] at h
  exact h.eq MRep.one

end NormalThree

end CFSG.Sporadic.Co1Schreier
