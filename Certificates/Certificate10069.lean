
module


public import CFSG.Sporadic.Co1.Module.FormsInputs
import Certificates.Kernel.Co1M.C10069
public import CFSG.Sporadic.HS.SmallF2Spec

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module CFSG.Sporadic.SmallF2 in
theorem certificate10069 :
    mulRows 24 (mulRows 24 (transposeRows 24 dat.rowsA) f0Rows) dat.rowsA = f0Rows ∧
      mulRows 24 (mulRows 24 (transposeRows 24 dat.rowsB) f0Rows) dat.rowsB = f0Rows ∧
      mulRows 24 f0Rows f0InvRows = idRows 24 ∧ mulRows 24 f0InvRows f0Rows = idRows 24 ∧
      (∀ i < 24, ((mulRows 24 (mulRows 24 (transposeRows 24 dat.rowsA) qRows)
        dat.rowsA)[i]?.getD 0).testBit i = ((qRows[i]?.getD 0).testBit i)) ∧
      (∀ i < 24, ((mulRows 24 (mulRows 24 (transposeRows 24 dat.rowsB) qRows)
        dat.rowsB)[i]?.getD 0).testBit i = ((qRows[i]?.getD 0).testBit i)) ∧
      vecMulN 24 (transposeRows 24 (wordRows stabWord₁)) 2 = 2 ∧
      vecMulN 24 (transposeRows 24 (wordRows stabWord₂)) 2 = 2 ∧
      addRows (mulRows 24 certC1 (addRows (wordRows stabWord₁) (idRows 24)))
        (mulRows 24 certC2 (addRows (wordRows stabWord₂) (idRows 24))) = projRows ∧
      addRows (mulRows 24 (addRows (wordRows stabWord₁) (idRows 24)) certD1)
        (mulRows 24 (addRows (wordRows stabWord₂) (idRows 24)) certD2) = lamRows ∧
      toVecD 24 (vecMulN 24 dat.rowsA 10379264) ≠ toVecD 24 10379264 ∧
      (qRows[1]?.getD 0).testBit 1 = false ∧ (qRows[12]?.getD 0).testBit 12 = true ∧
      (qRows[0]?.getD 0).testBit 0 = false ∧
      f0Rows = #[8388608, 10379264, 4321280, 1679360, 4710400, 81920, 11182080, 13221888, 16683008,
        9777152, 8183808, 11567104, 975620, 3397214, 11318454, 15105500, 6169276, 16363858,
        14276370, 3626442, 3092234, 14347584, 2590100, 2542531] := KernelCo1M.c10069

end Certificates
