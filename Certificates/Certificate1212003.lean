module

public import Certificates.Data.NT44Model
public import CFSG.LieType.Multipliers.L34Data
public import CFSG.Certificates.SchreierChainData
import Certificates.Kernel.NT44.Glue
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

public section

namespace Certificates

open CertificateChecks

theorem certificate1212003 : CFSG.GH74.GLS.NT44.PermutationNative.bridgeCheck
    (CFSG.LieType.Multipliers.L34.coverWs.map
      (List.map CFSG.Certificates.schreierLetterCode))
    (CFSG.LieType.Multipliers.L34.zThree.map
      CFSG.Certificates.schreierLetterCode) = true :=
  KernelNT44.Glue.nt44_bridge

end Certificates
