module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatFactsK
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCode
public import CFSG.Quasithin.Background.E2TwoProofSporJ2Inputs
public import Certificates.Data.Kernel.SporLatDcCode
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CFSG.Quasithin.E2P.SporB.J2Lat.J2K
  "CFSG/Quasithin/Background/data/j2LatK.json.gz" 6872 16160519555290276566
  (mw : List (List (List Nat)))
  (Om : List (List (List Nat) × List (List Nat) × List Nat × List Nat))
  (Ot : List (List (List (List Nat)) × List (List Nat) × List Nat × List Nat))

public section

namespace CFSG.Quasithin.E2P.SporB

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.J2

@[expose] noncomputable def j2Sg : List ↥J :=
  j2Qp.map fun p => (slpElts (a : J) (b : J) j2Prog).getD p.1 1

namespace J2Lat

open CFSG.KC.SLDc

@[expose] noncomputable def j2LatD : LatData (List ℕ) where
  O := default
  F := default
  sTabs := j2STabs
  mw := J2K.mw.toArray
  mt := J2K.mw.toArray.map fun ws => ws.map (wordTabL #[j2ta.toArray, j2tb.toArray] 315)
  Om := #[omL (J2K.Om.getD 0 default), omL (J2K.Om.getD 1 default), omL (J2K.Om.getD 2 default),
    omL (J2K.Om.getD 3 default), omL (J2K.Om.getD 4 default)]
  atoms := #[]
  joins := []

@[expose] noncomputable def j2OtD : Array (OmegaData (List (List ℕ))) :=
  #[omL (J2K.Ot.getD 0 default), omL (J2K.Ot.getD 1 default), omL (J2K.Ot.getD 2 default),
    omL (J2K.Ot.getD 3 default), omL (J2K.Ot.getD 4 default)]

end J2Lat

end CFSG.Quasithin.E2P.SporB

end
