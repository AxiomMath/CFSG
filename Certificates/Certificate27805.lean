module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8EA16Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8D8Words
public import CFSG.Sporadic.SmallOddCore.J2DataInputs
public import CFSG.Sporadic.SmallOddCore.J3DataInputs
import Certificates.Kernel.TS8.C27805

public section

namespace Certificates

open CertificateChecks

theorem certificate27805 : CFSG.EvenSporadicStandard.Fin76b.TS8EA16.checkEA16 315
      (CFSG.Sporadic.Schreier.PairNative.j2StrongArrs[0]!)
      (CFSG.Sporadic.Schreier.PairNative.j2StrongArrs[1]!)
      (CFSG.Sporadic.SmallOddCore.Native.natArr (CFSG.Sporadic.SmallOddCore.j2CentTbl 0))
      CFSG.EvenSporadicStandard.Fin76b.TS8D8.j2SylowWords = true ∧
    CFSG.EvenSporadicStandard.Fin76b.TS8EA16.checkEA16 6156
      (CFSG.Sporadic.Schreier.j3StrongArrs[0]!)
      (CFSG.Sporadic.Schreier.j3StrongArrs[1]!)
      (CFSG.Sporadic.SmallOddCore.Native.natArr (CFSG.Sporadic.SmallOddCore.j3CentTbl 0))
      CFSG.EvenSporadicStandard.Fin76b.TS8D8.j3SylowWords = true := KernelTS8.c27805

end Certificates
