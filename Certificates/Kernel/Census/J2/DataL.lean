module

public import Certificates.Kernel.Census.J2.DataII
public import Certificates.Kernel.Census.J2.DataExc
public import Certificates.Data.Kernel.Census.PackedL

public section

namespace CertificateChecks.KernelCensus.J2K

open CFSG.KC.Census

@[expose] noncomputable def nodeIIL (fl : List Bool) (i : Nat) : Bool :=
  pnodeL 315 9 [0, 4, 3] inP inP false true false j2IICS j2IINodes j2IIWCS fl i

@[expose] noncomputable def nodeExcL (fl : List Bool) (i : Nat) : Bool :=
  pnodeExcL 315 9 [0, 4, 3] inP inP inRP false false false j2ExcCS j2ExcNodes cNLExc j2ExcWCS
    j2ExcE0P j2ExcExcs fl i

@[expose] noncomputable def blkIIL (a len : Nat) : Bool :=
  withFl 315 9 j2IICS fun fl => (List.range' a len).all (nodeIIL fl)

@[expose] noncomputable def blkExcL (a len : Nat) : Bool :=
  withFl 315 9 j2ExcCS fun fl => (List.range' a len).all (nodeExcL fl)

end CertificateChecks.KernelCensus.J2K

end
