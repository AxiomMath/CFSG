module

public import Certificates.Data.Kernel.M24Dc.Data
public import Certificates.Data.Kernel.SporLatDcCode

public noncomputable section

namespace CFSG.KD.M24Dc

open CFSG.KC.SLDc CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def L0 (l : Nat) : Nat → Nat := tabF (J.tabs.getD l [])

@[expose] def L (l : Nat) : Nat → Nat := pairF 24 (L0 l)

@[expose] def C : DcCtx := ⟨576, J.delta, L, 8, 4, 10, 239085⟩

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

@[expose] def sepL : List Nat := (List.range 24).map fun i => i + 24 * i

@[expose] def Δc : List Nat :=
  [232, 252, 330, 481, 127576, 162052, 305155, 339137, 355411, 389889]

@[expose] def T (l : Nat) : Array Nat := (J.tabs.getD l []).toArray

@[expose] def sT : List (Array Nat) := [T 2, T 3, T 4, T 5]

@[expose] def mLet (j : Nat) : Array (Array Nat) :=
  (sT ++ (J.mw.getD j []).map (wordTabL #[T 0, T 1] 24)).toArray

@[expose] def Om (j : Nat) : OmegaData (List Nat) := omL (J.Om.getD j default)

@[expose] def Ot (j : Nat) : OmegaData (List (List Nat)) := omL (JO.Ot.getD j default)

@[expose] def memOK (j : Nat) : Bool := omCodeOK 24 (mLet j) Δc (Om j)

@[expose] def otOK (j : Nat) : Bool :=
  omOKG (fun l X => X.map (codeSetT 24 (sT.toArray.getD l #[]))) (Om j).lbl.toList 4 (Ot j)

@[expose] def tabsOK : Bool := J.tabs.length == 10 && J.tabs.all fun t => t.length == 24 && t.all (· < 24)

@[expose] def invOK : Bool :=
  (List.range 4).all fun i => (List.range 24).all fun p => L0 (Nat.add 6 i) (L0 (Nat.add 2 i) p) == p

@[expose] def mwOK : Bool := J.mw.all fun ws => ws.all fun w => w.all (· < 2)

@[expose] def fixOK : Bool := sT.all fun t => codeSetT 24 t Δc == Δc

@[expose] def moveOK : Bool := (List.range' 1 12).all fun j => (J.mw.getD j []).any fun w =>
  !(codeSetT 24 (wordTabL #[T 0, T 1] 24 w) Δc == Δc)

@[expose] def topOK : Bool := !(codeSetT 24 (T 0) Δc == Δc) || !(codeSetT 24 (T 1) Δc == Δc)

end CFSG.KD.M24Dc

end
