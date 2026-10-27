module

public import Certificates.Data.Kernel.J3Dc.Data
public import Certificates.Data.Kernel.SporLatDc

public section

namespace CFSG.KD.J3Dc

open CFSG.KC.SLDc CFSG.QuasithinUnique.Ch1.SporLat

@[expose] noncomputable def L (l p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 13 (J.lc.getD l 0) p

@[expose] def Δ : List Nat := [371, 793, 2594, 4004]

@[expose] noncomputable def C : DcCtx := ⟨6156, Δ, L, 6, 3, 7, 392445⟩

@[expose] noncomputable def D : DcData where
  w := J.w
  oidC := J.oidC
  tlC := J.tlC
  dpC := J.dpC
  obase := J.obase
  osz := J.osz
  K := J.K
  sep := J.sep
  mw := J.mw
  Rc := [J.R0, J.R1, J.R2, J.R3, J.R4, J.R5, J.R6, J.R7, J.R8, J.R9, J.R10, J.R11, J.R12, J.R13,
    J.R14, J.R15, J.R16]
  msum := J.msum
  joins := J.joins
  csz := J.csz
  c0 := J.c0
  pcz := J.pcz
  npc := J.npc

@[expose] def omD {Lab : Type} (x : List Lab × List (List Nat) × List Nat × List Nat) :
    OmegaData Lab :=
  ⟨x.1.toArray, (x.2.1.map List.toArray).toArray, x.2.2.1.toArray, x.2.2.2.toArray⟩

@[expose] noncomputable def Om (j : Nat) : OmegaData (List Nat) := omD (J.Om.getD j default)

@[expose] noncomputable def Lm (j l : Nat) : Nat → Nat :=
  bif Nat.blt l 3 then L (Nat.add 2 l) else wordF' (J.mw.getD j []) (Nat.sub l 3)
where
  wordF' (ws : List (List Nat)) (i : Nat) : Nat → Nat := CFSG.KC.E64F.wordF L (ws.getD i [])

@[expose] noncomputable def memOK (j : Nat) : Bool :=
  omOKG (fun l x => labF (Lm j l) x) Δ (Nat.add 3 (J.mw.getD j []).length) (Om j)

@[expose] def B0 : List (List Nat) := [[0], [1], [3], [2]]

@[expose] noncomputable def Sb : OmegaData (List (List Nat)) := omD J.Sb

@[expose] noncomputable def sbOK : Bool := omOKG (fun l X => X.map (labF (L (Nat.add 2 l)))) B0 3 Sb

@[expose] noncomputable def sgwOK : Bool :=
  Nat.beq J.sgw.length 3 && J.sgw.all fun w => w.all fun l => Nat.blt l 2

@[expose] noncomputable def sgOK (i : Nat) : Bool :=
  (List.range 6156).all fun p => L (Nat.add 2 i) p == CFSG.KC.E64F.wordF L (J.sgw.getD i []) p

@[expose] noncomputable def abOK : Bool :=
  (List.range 2).all fun l => (List.range 6156).all fun p => Nat.blt (L l p) 6156

@[expose] noncomputable def invOK : Bool :=
  (List.range 3).all fun i => (List.range 6156).all fun p =>
    L (Nat.add 5 i) (L (Nat.add 2 i) p) == p

end CFSG.KD.J3Dc

end
