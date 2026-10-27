
module

public import CFSG.Open.QuasithinDefs
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Quasithin.Recognition.CertChain
public import CFSG.Quasithin.Recognition.CertDataTits
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Open.QuasithinDefs
public meta import CFSG.Quasithin.Recognition.CertDataTits
public meta import Certificates.Data.CFSGNative.YGroups.ExactCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Quasithin.Recognition.CertTitsInputs

@[expose] public section

namespace CFSG.Quasithin

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem titsArray_getElem (s : String) {i : ℕ} (hi : i < 1755) :
    (titsArray s)[i]! = CFSG.Open.quasithinFixedWidth 4 (CFSG.Open.quasithinDigits s) i % 1755 := by
  unfold titsArray
  exact getElem!_ofFn_nat _ hi

theorem coe_permOfArr_titsArray (s : String)
    (h : isInvA 1755 (titsArray s) (invCand 1755 (titsArray s)) = true) :
    ⇑(permOfArr 1755 (titsArray s)) = CFSG.Open.quasithinDecodePerm 1755 (by norm_num) s := by
  funext x
  apply Fin.ext
  have hx := (rep_permOfArr h).1 x
  rw [← hx, titsArray_getElem s x.2]
  rfl

private theorem titsGens_size : titsGens.size = 2 := by simp [titsGens]

private theorem titsGens_zero : titsGens[0]! = titsArray CFSG.Open.quasithinTitsData1 := by
  simp [titsGens]

private theorem titsGens_one : titsGens[1]! = titsArray CFSG.Open.quasithinTitsData2 := by
  simp [titsGens]

private theorem titsBase_nodup : titsBase.Nodup := by decide

end CFSG.Quasithin
