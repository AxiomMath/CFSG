module

public import Certificates.Data.CFSGNative.SectionRank.TitsChain
import Certificates.Kernel.LocalComp.Tits.ChainK
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Chevalley.FixedBruhat
public import CFSG.LieType.Chevalley.RootOps.Data.E8
public import Certificates.Certificate113

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.SectionRank CFSG.SectionRank.Native.Tits CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps in
theorem certificate8033 : titsChainCheck = true := KernelLC.Tits.chain

end Certificates
