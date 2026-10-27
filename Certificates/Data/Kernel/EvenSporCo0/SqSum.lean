module

public import Certificates.Data.Kernel.EvenSporCo0.Eighth

public section

namespace CFSG.KC.EvenSporCo0

open CFSG.KC.Enum CFSG.KS CFSG.KLie.CT CFSG.Monster.Code CFSG.EvenSporadicStandard.TwoCo1

@[expose] noncomputable def linP (p w : ℕ) : ℕ := w ^^^ sigRecP p w 24

@[expose] noncomputable def imsS (p : ℕ) : List ℕ :=
  (List.range 12).map fun i => linP p (Bmask i)

@[expose] def hitF (d x : ℕ) : ℕ := if x % 16777216 = d then 1 else 0

@[expose] noncomputable def cntS (p d : ℕ) : ℕ :=
  let ims := imsS p
  let ws := witsGo [] 0 ims
  if witsOK (fun i => ims.getD i 0) (fun k => ws.getD k none) 12 then
    treeSumW (hitF d) (fun i => ims.getD i 0) (fun k => ws.getD k none) 12 0
  else treeSumN (hitF d) (fun i => ims.getD i 0) 12 0

@[expose] noncomputable def sqTermP (d p : ℕ) : ℕ :=
  if Nat.beq (pcomp 24 5 (mask 5) p p) (pidn 24 5) = true then cntS p d else 0

@[expose] def sumR (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumR f n + f n

@[expose] noncomputable def sqK (T : ℕ → ℕ) (N d : ℕ) : ℕ := sumR (fun i => sqTermP d (T i)) N

@[expose] noncomputable def sqOK (T : ℕ → ℕ) (N d n : ℕ) : Bool := Nat.beq (sqK T N d) n

@[expose] noncomputable def fixAllP (G : ℕ → ℕ) (a : ℕ) : Bool :=
  (List.range 10).all fun k => Nat.beq (linP (G k) a % 16777216) 0

@[expose] noncomputable def fixOKP (G : ℕ → ℕ) (a : ℕ) : Bool :=
  !fixAllP G a || (Nat.beq (a % 16777216) 0 || Nat.beq (a % 16777216) 255 ||
    Nat.beq (a % 16777216) 16776960 || Nat.beq (a % 16777216) 16777215)

@[expose] noncomputable def fixBadP (G : ℕ → ℕ) : ℕ :=
  treeSumN (fun a => if fixOKP G a = true then 0 else 1) Bmask 12 0

@[expose] noncomputable def fixK (G : ℕ → ℕ) : Bool := Nat.beq (fixBadP G) 0

end CFSG.KC.EvenSporCo0
