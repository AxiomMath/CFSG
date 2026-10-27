
module

import Certificates.Kernel.Misc.Tits.Bridge8072
import CFSG.Certificates.Kernel.Misc.TitsBridgeSound
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Recognition.CertTitsInputs
public import CFSG.Sporadic.Schreier.TitsArrays

@[expose] public section

set_option maxRecDepth 400000

open CFSG CFSG.Quasithin CFSG.KC.TitsBridge CFSG.KC.Enum CFSG.KS

namespace CertificateChecks.Batch8072

private theorem titsArray_eq {P : Nat} {cs : List Char} {s : String} (hs : s = String.ofList cs)
    (h : bridgeK P cs = true) : titsArray s = CFSG.KS.Raw.unpack 1755 11 P := by
  rw [titsArray, CFSG.KS.Raw.unpack, hs, digitsK_eq]
  congr 1
  funext i
  exact cmp4_sound P 0 _ h i.val (by omega) |>.trans (by rw [Nat.zero_add])

private theorem titsBridge_array₁_0 :
    titsArray CFSG.Open.quasithinTitsData1 = CFSG.Sporadic.Schreier.Tits.titsDerivedArrs[0]! := by
  exact (titsArray_eq KernelMisc.TitsB1.eq KernelMisc.TitsB.bridge₁).trans
    (KernelMisc.TitsText.titsDerivedArrs_get (j := 0) (by omega)).symm

private theorem titsBridge_array₂_1 :
    titsArray CFSG.Open.quasithinTitsData2 = CFSG.Sporadic.Schreier.Tits.titsDerivedArrs[1]! := by
  exact (titsArray_eq KernelMisc.TitsB2.eq KernelMisc.TitsB.bridge₂).trans
    (KernelMisc.TitsText.titsDerivedArrs_get (j := 1) (by omega)).symm

end CertificateChecks.Batch8072

end
