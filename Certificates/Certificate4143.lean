module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRuInputs
import Certificates.Kernel.LocalQT.Base.C4143

public section

namespace Certificates

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.K1 CFSG.QuasithinUnique.K1.SporadicPerm in
open CFSG.Sporadic.SmallF2 in
open CFSG.Sporadic.Th.Native (ap) in
open CFSG.Blueprint.NativeSporadic (Carrier) in
open CFSG.Sporadic.Ru.Native (ruData) in
theorem certificate4143 : (slpValidAux ruProg 2 = true)
    ∧ (BaseCertS ruData.n ruB ruSLP ruQp 154 187 191 189 193
            ruEnum.1 ruEnum.2.1 ruEnum.2.2 14) :=
  ⟨CFSG.KD.LQT.C4143.valid, CFSG.KD.LQT.C4143.cert⟩

end Certificates
