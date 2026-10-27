module

public import Certificates.Data.Kernel.RuDc.Data
public import Certificates.Data.Kernel.SporLatDc

public noncomputable section

namespace CFSG.KD.RuDc

open CFSG.KC.SLDc CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def nodes : List Nat := [0, 1, 163, 172, 185, 198, 203, 207]

@[expose] def L (l p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 12 (J.lc.getD l 0) p

@[expose] def Δ : List Nat := [205, 666, 1130, 1490, 2050, 2096, 2608, 2972]

@[expose] def C : DcCtx := ⟨4060, Δ, L, 6, 3, 14, 8906625⟩

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
  Rc := J.Rc
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

@[expose] def gensInF (j jj : Nat) : Bool :=
  (J.mw.getD j []).all fun w => (Om jj).lbl.toList.contains (labF (CFSG.KC.E64F.wordF L w) Δ)

@[expose] def inclL : List (List Nat) := [[0, 1, 2, 3, 4], [1], [2], [1, 2, 3], [2, 4]]

@[expose] def inclOK : Bool :=
  (List.range 5).all fun j => (List.range 5).all fun jj =>
    gensInF j jj == (inclL.getD j []).contains jj

@[expose] def invOK : Bool :=
  (List.range 3).all fun i => (List.range 4060).all fun p => L (Nat.add 5 i) (L (Nat.add 2 i) p) == p

end CFSG.KD.RuDc

end
