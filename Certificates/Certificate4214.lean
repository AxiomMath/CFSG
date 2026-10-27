module

public import Certificates.Data.E68Spor.Chk
public import Certificates.Data.E68Spor.Words
public import CFSG.Quasithin.Background.E2TwoProofSporJ2Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporSound
import Certificates.Kernel.E68Spor4214.Wit

public section

namespace Certificates

open CFSG.Quasithin.E6.Spor CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.Sporadic.SmallF2 in
open CFSG.Sporadic.HS.Native (hsData) in
theorem certificate4214 :
    (classChk 315 j2ta.toArray j2tb.toArray j2SLP[143]! 315 = true ∧
      rChk 315 (codeSetAct 315) CFSG.Quasithin.E2P.SporB.J2Lat.j2Delta
        CFSG.Quasithin.E2P.SporB.J2Lat.j2STabs j2ta.toArray j2tb.toArray j2SLP[143]!
        j2UWords j2YWord j2NWord 5 15 = true) ∧
    ∀ (z₀ : J hsData),
      (tab hsData.n z₀).toArray = hsSLP[164]! →
        (¬ ∀ g : J hsData, g * z₀ = z₀ * g) ∧
          RWit CFSG.QuasithinUnique.Ch1.SporLat.HS.hsCtx z₀ 5 15 :=
  ⟨CFSG.KD.E68S4214.j2_ok, fun z₀ hzT => CFSG.KD.E68S4214.hs_wit z₀ hzT⟩

end Certificates
