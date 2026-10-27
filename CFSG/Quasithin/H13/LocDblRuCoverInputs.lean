module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRuKInputs

public section

namespace CFSG.Quasithin.H13.LocDbl.RuCov

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2 CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.RuCert
open CFSG.Sporadic.Ru.Native (ruData)

@[expose] noncomputable def ruS : Subgroup (J ruData) := Subgroup.closure {x | x ∈ ruSgK}

@[expose] noncomputable def ruVA : Subgroup (J ruData) :=
  Subgroup.closure {x | x ∈ ruSgK ++ (ruMw[1]!).map (wordElt (a ruData) (b ruData))}

@[expose] noncomputable def ruVB : Subgroup (J ruData) :=
  Subgroup.closure {x | x ∈ ruSgK ++ (ruMw[2]!).map (wordElt (a ruData) (b ruData))}

@[expose] noncomputable def ruLet : Array (J ruData) :=
  (a ruData :: b ruData :: (ruSgK ++ ruSgK.map (·⁻¹))).toArray

@[expose] noncomputable def ruWord (w : List ℕ) : J ruData := evalElt ruLet w

@[expose] noncomputable def ruTopW : List (List ℕ) :=
  (CFSG.KD.RuDc.D.Rc.flatten.filter fun r : CFSG.KC.SLDc.Rep => CFSG.KC.SLDc.Rep.cls r == 5).map
    CFSG.KC.SLDc.Rep.w

end CFSG.Quasithin.H13.LocDbl.RuCov

end
