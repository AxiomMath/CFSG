module

public import Certificates.Data.Kernel.SporLatOrb

public section

namespace CFSG.KC.SLOrb

@[expose] def gP (w T p : Nat) : Nat := T / 2 ^ (w * p) % 2 ^ w

@[expose] def packL (w : Nat) : List Nat → Nat
  | [] => 0
  | a :: l => a + 2 ^ w * packL w l

@[expose] def conjP (w n t ti T : Nat) : Nat :=
  packL w ((List.range n).map fun q => gP w t (gP w T (gP w ti q)))

@[expose] def actS (w n : Nat) (Ls : List (Nat × Nat)) (l : Nat) (x : List Nat) : List Nat :=
  [conjP w n (Ls.getD l (0, 0)).1 (Ls.getD l (0, 0)).2 (x.headD 0)]

@[expose] def labP (n w T : Nat) : List Nat := (List.range n).map fun p => p * n + gP w T p

@[expose] def invB (n w t ti : Nat) : Bool :=
  (List.range n).all fun q =>
    Nat.blt (gP w t q) n && Nat.blt (gP w ti q) n && Nat.beq (gP w t (gP w ti q)) q

@[expose] def invL (n : Nat) (t : List Nat) : List Nat :=
  (List.range n).map fun q => ((List.range n).find? fun p => t.getD p 0 == q).getD 0

@[expose] def pk (w n : Nat) (t : List Nat) : Nat × Nat := (packL w t, packL w (invL n t))

@[expose] def pz (w n : Nat) (z : Array Nat) : Nat :=
  packL w ((List.range n).map fun p => z.getD p 0)

@[expose] def tabOK (w n : Nat) (ta tb : Array Nat) : Bool :=
  goodB n ta (gP w (pk w n ta.toList).1) && goodB n tb (gP w (pk w n tb.toList).1) &&
    invB n w (pk w n ta.toList).1 (pk w n ta.toList).2 &&
    invB n w (pk w n tb.toList).1 (pk w n tb.toList).2

end CFSG.KC.SLOrb

end
