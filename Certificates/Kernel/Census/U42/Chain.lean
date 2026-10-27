module

public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverU42Check
public meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverU42Check
public meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.RawGen

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelCensus.U42C 45 6 16
  CFSG.ComponentClassification.RankTwoHypIICover.U42.u42S
  CFSG.ComponentClassification.RankTwoHypIICover.U42.u42Base 2
  CFSG.ComponentClassification.RankTwoHypIICover.U42.u42Words

end
