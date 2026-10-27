module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
public import Certificates.Certificate2185
public import CFSG.Sporadic.Schreier.LyCheckSep
public import CFSG.Sporadic.Ly.KeySpec
public import CFSG.Sporadic.He.FpSpec
import Certificates.Kernel.SporSch.Ly.SepGlue
public import Certificates.Certificate2189
public import Certificates.Certificate3085
public import Certificates.Certificate8130
public import Certificates.Certificate8131
public import Certificates.Certificate14970
import Certificates.Kernel.LyFivePc.Facts

public section

namespace Certificates

theorem certificate1023018 :     CFSG.StandardType.SporadicShape.SporKRestCover 5 CFSG.Blueprint.NativeSporadic.Ly :=
  CertificateChecks.KernelLyFivePc.cover_native

end Certificates
