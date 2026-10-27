module

public import CFSG.Quasithin.Background.E2TwoProofSporJ2KInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows

public section

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
  CFSG.Quasithin.E2P.SporB.J2Lat

namespace J2Y9K

@[expose] def mems : List Mem :=
  [⟨128, 128, 128⟩, ⟨384, 128, 384⟩, ⟨1152, 64, 1152⟩, ⟨1920, 32, 1920⟩, ⟨384, 64, 384⟩]

@[expose] def rows : Prop :=
  O2OK (codeSetAct 315) j2LatD j2OtD ∧ (List.range 5).map (defaultRow 7 j2LatD j2OtD) = mems

@[expose] def incl42 : Prop := GensIn (codeSetAct 315) j2Delta j2LatD 4 2

@[expose] def incl13 : Prop := GensIn (codeSetAct 315) j2Delta j2LatD 1 3

@[expose] def stmt : Prop := rows ∧ incl42 ∧ incl13

end J2Y9K
