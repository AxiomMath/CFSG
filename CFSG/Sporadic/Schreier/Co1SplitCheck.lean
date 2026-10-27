module

public import CFSG.Sporadic.Schreier.Co1ElemThreeCheck
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeCheck
public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public import CFSG.Sporadic.Schreier.Co1SplitCheckInputs
public import Certificates.Certificate2147

public section

namespace CFSG.Sporadic.Co1Schreier

namespace Native

open CFSG.Sporadic.SmallF2.Native

theorem zq_eq {e k : Nat} (he : e < 3) (hk : k < 12) : zq e k = zPow e (qNat k) := by
  unfold zq zqT
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [show 3 * k + e < 36 by omega, ↓reduceDIte, Option.getD_some]
  rw [show (3 * k + e) % 3 = e by omega, show (3 * k + e) / 3 = k by omega]

end Native

theorem split_check : Native.splitCheck = true :=
  Certificates.certificate2147.1

theorem split_data_check : Native.splitDataCheck = true :=
  Certificates.certificate2147.2.1

theorem split_conj_check : Native.splitConjCheck = true :=
  Certificates.certificate2147.2.2.1

theorem zq_check : Native.zqCheck = true :=
  Certificates.certificate2147.2.2.2

end CFSG.Sporadic.Co1Schreier
