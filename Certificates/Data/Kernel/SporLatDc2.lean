module

public import Certificates.Data.Kernel.SporLatDcSort

public noncomputable section

namespace CFSG.KC.SLD2

open CFSG.KC.E64F

@[expose] def clampF (N : Nat) (f : Nat → Nat) (p : Nat) : Nat := bif Nat.blt p N then f p else 0

@[expose] def itW (L : Nat → Nat → Nat) (w : List Nat) : Nat → Nat → Nat
  | 0, p => p
  | e + 1, p => itW L w e (wordF L w p)

@[expose] def witW (r : List Nat) : List (List Nat) → List Nat
  | [] => []
  | s :: t => r ++ s ++ witW r t

structure Dc2Ctx where
  n : Nat
  L : Nat → Nat → Nat
  nl : Nat
  ns : Nat
  nf : Nat
  Λ : List Nat
  Δ : List Nat
  k : Nat
  N1 : Nat
  N2 : Nat

abbrev BOrb := Nat × Nat × Nat × Nat × Nat × List (List Nat) × List (List Nat)

namespace BOrb
@[expose] def qs (b : BOrb) : Nat := b.1
@[expose] def omc (b : BOrb) : Nat := b.2.1
@[expose] def tlc (b : BOrb) : Nat := b.2.2.1
@[expose] def dpc (b : BOrb) : Nat := b.2.2.2.1
@[expose] def osz (b : BOrb) : Nat := b.2.2.2.2.1
@[expose] def kg (b : BOrb) : List (List Nat) := b.2.2.2.2.2.1
@[expose] def kw (b : BOrb) : List (List Nat) := b.2.2.2.2.2.2
end BOrb

abbrev Clos := Nat × List (List (List Nat)) × List Nat × List Nat × List Nat × List Nat ×
  List (List Nat) × List Nat

namespace Clos
@[expose] def B (c : Clos) : Nat := c.1
@[expose] def C (c : Clos) : List (List (List Nat)) := c.2.1
@[expose] def rows (c : Clos) : List Nat := c.2.2.1
@[expose] def par (c : Clos) : List Nat := c.2.2.2.1
@[expose] def via (c : Clos) : List Nat := c.2.2.2.2.1
@[expose] def ord (c : Clos) : List Nat := c.2.2.2.2.2.1
@[expose] def R (c : Clos) : List (List Nat) := c.2.2.2.2.2.2.1
@[expose] def si (c : Clos) : List Nat := c.2.2.2.2.2.2.2
end Clos

abbrev Rec1 := List Nat × Nat × Nat × List Nat × Clos

namespace Rec1
@[expose] def u (r : Rec1) : List Nat := r.1
@[expose] def mode (r : Rec1) : Nat := r.2.1
@[expose] def m (r : Rec1) : Nat := r.2.2.1
@[expose] def key (r : Rec1) : List Nat := r.2.2.2.1
@[expose] def cl (r : Rec1) : Clos := r.2.2.2.2
end Rec1

abbrev Rec2 := List (List Nat × List Nat) × Nat

abbrev Root := Nat × Nat × List Nat × List (List Nat) × Nat × Nat

namespace Root
@[expose] def c (t : Root) : Nat := t.1
@[expose] def ρ (t : Root) : Nat := t.2.1
@[expose] def φ (t : Root) : List Nat := t.2.2.1
@[expose] def s (t : Root) : List (List Nat) := t.2.2.2.1
@[expose] def l (t : Root) : Nat := t.2.2.2.2.1
@[expose] def p (t : Root) : Nat := t.2.2.2.2.2
end Root

structure Dc2Data where
  sep : List Nat
  pw : Nat
  bo : List BOrb
  R1 : List Rec1
  fB : Nat
  fC : List (List (List Nat))
  fw : Nat
  fpc : List Nat
  fpar : List Nat
  fvia : List Nat
  ford : List Nat
  R2 : List Rec2
  gw : Nat
  gd : Nat
  roots : List (List Root)

end CFSG.KC.SLD2

end
