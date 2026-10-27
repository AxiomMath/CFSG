module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSDcInputs

public noncomputable section

namespace CFSG.Quasithin.A312Hs

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.HS
open CFSG.Sporadic.HS.Native (hsData)

@[expose] def hsLettersK (j : ℕ) : List (Array ℕ) := hsLatK.sTabs ++ hsLatK.mt[j]!

@[expose] def hsQuot2EnumK : Array (List ℕ) × Array ℕ × Array ℕ :=
  bfsEnumB hsData.n hsB (hsQuot2.map (quotGt hsData.n (hsLettersK 2)))
    (hsQuot2.map (quotGi hsData.n (hsLettersK 2))) 1000000

end CFSG.Quasithin.A312Hs
