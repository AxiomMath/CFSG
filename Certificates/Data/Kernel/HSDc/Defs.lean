module

public import Certificates.Data.Kernel.HSDc.Data
public import Certificates.Data.Kernel.SporLatDc

public noncomputable section

namespace CFSG.KD.HSDc

open CFSG.KC.SLDc CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def nodes : List Nat := [0, 1, 172, 185, 200, 212, 217, 218]

@[expose] def L (l p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 11 (J.lc.getD l 0) p

@[expose] def Δ : List Nat := [213, 278, 582, 618, 782, 798, 950, 1057]

@[expose] def C : DcCtx := ⟨1100, Δ, L, 6, 3, 9, 86625⟩

@[expose] def D : DcData where
  w := J.w
  oidC := J.oidC
  tlC := J.tlC
  dpC := J.dpC
  obase := J.obase
  osz := J.osz
  K := J.K
  sep := J.sep
  mw := J.mw
  Rc := [J.R0, J.R1, J.R2, J.R3, J.R4, J.R5, J.R6, J.R7]
  msum := J.msum
  joins := J.joins
  csz := J.csz
  c0 := J.c0
  pcz := J.pcz
  npc := J.npc

@[expose] def omD {Lab : Type} (x : List Lab × List (List Nat) × List Nat × List Nat) :
    OmegaData Lab :=
  ⟨x.1.toArray, (x.2.1.map List.toArray).toArray, x.2.2.1.toArray, x.2.2.2.toArray⟩

@[expose] def Om (j : Nat) : OmegaData (List Nat) := omD (J.Om.getD j default)

@[expose] def Ot (j : Nat) : OmegaData (List (List Nat)) := omD (J.Ot.getD j default)

@[expose] def wordF' (ws : List (List Nat)) (i : Nat) : Nat → Nat :=
  CFSG.KC.E64F.wordF L (ws.getD i [])

@[expose] def Lm (j l : Nat) : Nat → Nat :=
  bif Nat.blt l 3 then L (Nat.add 2 l) else wordF' (J.mw.getD j []) (Nat.sub l 3)

@[expose] def memOK (j : Nat) : Bool :=
  omOKG (fun l x => labF (Lm j l) x) Δ (Nat.add 3 (J.mw.getD j []).length) (Om j) &&
    omOKG (fun l X => X.map (labF (L (Nat.add 2 l)))) (Om j).lbl.toList 3 (Ot j)

@[expose] def invOK : Bool :=
  (List.range 3).all fun i => (List.range 1100).all fun p => L (Nat.add 5 i) (L (Nat.add 2 i) p) == p

@[expose] def mwOK : Bool := J.mw.all fun ws => ws.all fun w => w.all (· < 2)

end CFSG.KD.HSDc

end
