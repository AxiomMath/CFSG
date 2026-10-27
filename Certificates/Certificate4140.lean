module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHSInputs
import Certificates.Kernel.LocalQT.Base.C4140

public section

namespace Certificates

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.K1 CFSG.QuasithinUnique.K1.SporadicPerm in
open CFSG.Sporadic.SmallF2 in
open CFSG.Sporadic.Th.Native (ap) in
open CFSG.Blueprint.NativeSporadic (Carrier) in
open CFSG.Sporadic.HS.Native (hsData) in
theorem certificate4140 : (slpValidAux hsProg 2 = true)
    ∧ (BaseCertS hsData.n hsB hsSLP hsQp 164 202 206 204 208
            hsEnum.1 hsEnum.2.1 hsEnum.2.2 9) :=
  ⟨CFSG.KD.LQT.C4140.valid, CFSG.KD.LQT.C4140.cert⟩

end Certificates
