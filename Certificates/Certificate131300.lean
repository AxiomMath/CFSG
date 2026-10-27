module

public import CFSG.HardMathSupport.Foote.E27.SporFi24Data
import Certificates.Kernel.E27Spor.Fi24OrbFacts

public section

namespace Certificates

open CFSG.HardMathSupport.Foote.E27 CFSG.HardMathSupport.Foote.E27.OrbitF3
  CFSG.Monster.B.Pinned in
theorem certificate131300 : (MulAction.orbit (Subgroup.closure {g | g ∈ [Fi24.XU, Fi24.YU]})
    (⟨rowsVec 3 10 Fi24.base⟩ : RowVD 10)).ncard = 12672 :=
  CertificateChecks.KernelE27Spor.Fi24Orb.fi24_orbit

end Certificates
