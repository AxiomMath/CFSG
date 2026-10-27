module

public import CFSG.Quasithin.Background.E2TwoProofSporJ2KInputs

public section

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
  CFSG.Quasithin.E2P.SporB.J2Lat

namespace J2T3K

@[expose] def notNormal : Prop :=
  ∃ ℓ ∈ (j2LatD.Om[4]!).lbl.toList, ∃ s ∈ j2LatD.sTabs, codeSetAct 315 s ℓ ≠ ℓ

@[expose] def incl : Prop := GensIn (codeSetAct 315) j2Delta j2LatD 1 3

@[expose] def stmt : Prop := notNormal ∧ incl

end J2T3K
