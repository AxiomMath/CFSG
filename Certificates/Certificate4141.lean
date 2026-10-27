module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHeInputs
import Certificates.Kernel.LocalQT.Base.C4141

public section

namespace Certificates

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.K1 CFSG.QuasithinUnique.K1.SporadicPerm in
open CFSG.Sporadic.He in
open CFSG.Blueprint.NativeSporadic (Carrier) in
theorem certificate4141 : (slpValidAux heProg 2 = true)
    ∧ (BaseCertS 8330 heB heSLP heQp 170 249 253 251 255
            heEnum.1 heEnum.2.1 heEnum.2.2 10) :=
  ⟨CFSG.KD.LQT.C4141.valid, CFSG.KD.LQT.C4141.cert⟩

end Certificates
