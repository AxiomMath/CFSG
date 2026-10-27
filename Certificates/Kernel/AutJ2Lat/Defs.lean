module

public import Certificates.Kernel.AutJ2Lat.Data
public import Certificates.Kernel.J2Dc.IdxGCheck
public import Certificates.Data.Kernel.AutJ2Lat.Lat
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData

public noncomputable section

namespace CFSG.KD.AutJ2Lat

open CFSG.KC.LQT.PW CFSG.KC.SLDc CFSG.KC.IdxG CFSG.ComponentClassification.J2Cover
open CFSG.KD.J2Dc (wW)

@[expose] noncomputable def AC : Nat := J2Dc.J.tc.getD 0 0

@[expose] noncomputable def BC : Nat := J2Dc.J.tc.getD 1 0

@[expose] noncomputable def wXY (w : List Nat) : Nat :=
  w.foldr (fun l acc => mulW 315 9 ([K.XC, BC].getD l 0) acc) (oneW 315 9)

@[expose] noncomputable def wT (w : List Nat) : Nat :=
  w.foldr (fun l acc => mulW 315 9 (K.SC.getD l 0) acc) (oneW 315 9)

@[expose] noncomputable def WA : List Nat := [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1]

@[expose] noncomputable def ORD : List Nat := [0, 2, 3, 4, 1]

@[expose] noncomputable def trW (w : List Nat) : List Nat :=
  w.foldr (fun l acc => (bif Nat.beq l 0 then WA else [1]) ++ acc) []

@[expose] noncomputable def mwR : List (List (List Nat)) :=
  ORD.map fun j => (J2Dc.J.mw.getD j []).map fun w => trW K.cw ++ trW w ++ trW K.ciw

@[expose] noncomputable def Δc : List Nat := [27575, 29787, 32003, 32010, 83176, 83273, 89812, 89909]

@[expose] noncomputable def lets (j : Nat) : List Nat := K.SC ++ K.MC.getD j []

@[expose] noncomputable def Om (j : Nat) : CFSG.QuasithinUnique.Ch1.SporLat.OmegaData (List Nat) :=
  omL (AutJ2Lat.RL.Om.getD j default)

@[expose] noncomputable def OtD (j : Nat) : CFSG.QuasithinUnique.Ch1.SporLat.OmegaData (List (List Nat)) :=
  omL (AutJ2Lat.RL.Ot.getD j default)

@[expose] noncomputable def imgs (c : Nat) : List Nat := (List.range 315).map (imgW 9 c)

@[expose] noncomputable def xOK : Bool :=
  outerArr.toList == imgs K.UC && K.XC == mulW 315 9 K.UC AC

@[expose] noncomputable def abOK : Bool :=
  (autStrong.getD 0 #[]).toList == imgs AC && (autStrong.getD 1 #[]).toList == imgs BC

@[expose] noncomputable def sOK : Bool :=
  (List.range 3).all fun i => (sylowStrong.getD i #[]).toList == imgs (K.SC.getD i 0)

@[expose] noncomputable def waOK : Bool := wXY WA == AC

@[expose] noncomputable def cOK : Bool :=
  wW K.cw == K.CC && wW K.ciw == K.CI && mulW 315 9 K.CC K.CI == oneW 315 9

@[expose] noncomputable def conjOK : Bool :=
  (List.range 3).all fun i =>
    mulW 315 9 K.CC (mulW 315 9 (J2Dc.J.tc.getD (Nat.add 2 i) 0) K.CI) == wT (K.tw.getD i [])

@[expose] noncomputable def mcOK : Bool :=
  K.MC == ORD.map fun j => (J2Dc.J.mw.getD j []).map fun w => mulW 315 9 K.CC (mulW 315 9 (wW w) K.CI)

@[expose] noncomputable def mwOK : Bool := AutJ2Lat.RL.mw == mwR

@[expose] noncomputable def omOK (j : Nat) : Bool :=
  omOKG (fun l x => codeSetF 315 (imgW 9 ((lets j).getD l 0)) x) Δc (lets j).length (Om j)

@[expose] noncomputable def otOK (j : Nat) : Bool :=
  omOKG (fun l X => X.map (codeSetF 315 (imgW 9 (K.SC.getD l 0)))) (Om j).lbl.toList 3 (OtD j)

@[expose] noncomputable def gensB (j jj : Nat) : Bool :=
  (K.MC.getD j []).all fun c => (Om jj).lbl.toList.contains (codeSetF 315 (imgW 9 c) Δc)

@[expose] noncomputable def fixB : Bool := K.SC.all fun c => fixCodes 315 Δc (imgW 9 c)

@[expose] noncomputable def moveB : Bool :=
  (List.range' 1 4).all fun j => (K.MC.getD j []).any fun c => !fixCodes 315 Δc (imgW 9 c)

@[expose] noncomputable def topB : Bool := !fixCodes 315 Δc (imgW 9 K.XC) || !fixCodes 315 Δc (imgW 9 BC)

end CFSG.KD.AutJ2Lat

end
