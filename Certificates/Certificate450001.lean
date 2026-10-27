module

public import CFSG.Sporadic.SmallOddCore.HSThreeCentInputs
public meta import CFSG.Sporadic.SmallOddCore.HSData
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
import Certificates.Kernel.HS3850.Facts450001
import CFSG.Certificates.Kernel.Misc.RuInvHash
import CFSG.Certificates.Kernel.Spor.ClassOneH

public section

namespace Certificates

open CFSG CFSG.Sporadic CFSG.Sporadic.SmallOddCore CFSG.PSL3Four.Native in
open CFSG.Sporadic.SmallOddCore.Native in
theorem certificate450001 : ((∀ k < 5, permOK 3850 (hsCentTbl (k + 21)) = true ∧
        (CFSG.Sporadic.SmallOddCore.Native.natArr (hsCentTbl (k + 21))).size = 3850) ∧
      (permOK 3850 (hsCentTbl 32) = true ∧ (CFSG.Sporadic.SmallOddCore.Native.natArr (hsCentTbl 32)).size = 3850) ∧
      (∀ i ∈ hsThreeX0Word, i < 5) ∧ (∀ j < 3, ∀ i ∈ hsThreeWords.getD j [], i < 5)
    )
    ∧ (wordTabS 3850 hsThreeBase hsThreeX0Word = CFSG.Sporadic.SmallOddCore.Native.natArr (hsCentTbl 32) ∧
      comp 3850 (comp 3850 (CFSG.Sporadic.SmallOddCore.Native.natArr (hsCentTbl 32)) (CFSG.Sporadic.SmallOddCore.Native.natArr (hsCentTbl 32)))
        (CFSG.Sporadic.SmallOddCore.Native.natArr (hsCentTbl 32)) = idTab 3850 ∧
      CFSG.Sporadic.SmallOddCore.Native.natArr (hsCentTbl 32) ≠ idTab 3850
    )
    ∧ (CFSG.PSL3Four.Native.enumOK 3850 hsThreeGens hsThreeEnum = true ∧ hsThreeEnum.tabs.size = 720 ∧
      CFSG.Sporadic.SmallOddCore.commAll 3850 hsThreeGens (CFSG.Sporadic.SmallOddCore.Native.natArr (hsCentTbl 32)) = true
    ) := CFSG.KD.HS3850.T450001.hsThree_true

end Certificates
