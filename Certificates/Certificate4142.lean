module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ2Inputs
import Certificates.Kernel.LocalQT.Base.C4142

public section

namespace Certificates

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.K1 CFSG.QuasithinUnique.K1.SporadicPerm in
open CFSG.Sporadic.J2 CFSG.Sporadic.Th.Native CFSG.Blueprint.NativeSporadic in
theorem certificate4142 : (slpValidAux j2Prog 2 = true)
    ∧ (BaseCertS 315 (List.range 315) j2SLP j2Qp 143 181 185 183 187
            j2Enum.1 j2Enum.2.1 j2Enum.2.2 7) :=
  ⟨CFSG.KD.LQT.C4142.valid, CFSG.KD.LQT.C4142.cert⟩

end Certificates
