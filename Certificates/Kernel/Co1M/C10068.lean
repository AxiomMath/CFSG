module

public import CFSG.Monster.GMS.CoTwoRep
public import CFSG.Sporadic.Co1.Module.CoTwoNorton
public import CFSG.Sporadic.Co1.Module.OddNative
public import CFSG.Sporadic.Co1.Module.Pairs
public import Certificates.Data.CFSGNative.Co1.CoTwoNorton
public import CFSG.Sporadic.Co1.Module.CoTwoNortonDataInputs
public import Certificates.Kernel.Co1M.Orb98280
import all Certificates.Data.CFSGNative.Co1.CoTwoNorton
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Monster.GMS.Leech.Linear
public import CFSG.Sporadic.Co1.Module.OddFacts
public import Certificates.Certificate10073Base

public section

namespace CertificateChecks.KernelCo1M

open CFSG.Sporadic.Co1.CoTwoNative CFSG.Sporadic.Co1.Module.CoTwo CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.Module

theorem c10068_norton : nortonCheck 22 genRows nortonCert = true := by quickRfl

theorem c10068_rep : repCheck (transposeRows 24 qRows) (transposeRows 24 f0Rows) r1Rows r2Rows
    wRows mt1 mt2 2 359217 = true := by quickRfl

theorem c10068_y₀ :
    Pairs.inPts (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 359217 = true := by
  have e : Pairs.inPts = CFSG.Sporadic.Co1.OddNative.inPts := rfl
  rw [e]
  exact (cm_orb_inPts 359217).trans (by quickRfl)

open CFSG.Sporadic.Co1.CoTwoNative CFSG.Sporadic.Co1.Module.CoTwo CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.Module in
open Certificates in
theorem c10068 :
    (nortonCheck 22 genRows nortonCert = true)
    ∧ (repCheck (transposeRows 24 qRows) (transposeRows 24 f0Rows) r1Rows r2Rows
      wRows mt1 mt2 2 359217 = true)
    ∧ (Pairs.inPts (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280
      359217 = true) := ⟨c10068_norton, c10068_rep, c10068_y₀⟩

end CertificateChecks.KernelCo1M

end
