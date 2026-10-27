module

public import Certificates.Data.CFSGNative.SectionRank.TitsLocal
import Certificates.Kernel.LocalComp.Tits.Local
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Chevalley.FixedBruhat
public import CFSG.LieType.Simplicity.TitsBits

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.SectionRank CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Simplicity in
open CFSG.SectionRank.Native.Tits in
open scoped commutatorElement in
theorem certificate8032 : (cubicOK titsSylow3 = true)
    ∧ (squareOK titsSylow5 = true) :=
  ⟨KernelLC.Tits.sylow3, KernelLC.Tits.sylow5⟩

end Certificates
