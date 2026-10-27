
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HNElevenInputs
import Certificates.Kernel.SporSch.HN.C13607
import CFSG.Sporadic.HNSchreier.ChainCheckInputs
import CFSG.Sporadic.HNSchreier.LevelInputs
meta import CFSG.Sporadic.HNSchreier.OrbitCheck
meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
import CFSG.Sporadic.HNSchreier.LocalCheckInputs
meta import CFSG.Sporadic.HNSchreier.PrimCheck
meta import CFSG.Sporadic.HNSchreier.LocalData
meta import CFSG.Sporadic.HNSchreier.MaskCheck
import CFSG.Sporadic.HNSchreier.OrbitCheckInputs
import CFSG.Sporadic.HNSchreier.PrimCheckInputs
meta import Certificates.Data.CFSGNative.Perm.Chain
import CFSG.Sporadic.HNSchreier.VectorData

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.HNSchreier.Native CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native in
theorem certificate13607 : elevenChecksO (hnsData.orbit ()) = true ∧ elevenNatCheck () = true :=
  ⟨KernelSporSch.HN13607.eleven_ok, KernelSporSch.HN13607.nat_ok⟩

end Certificates
