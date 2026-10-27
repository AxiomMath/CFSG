module

public import Init

public section

namespace CFSG.KC.WP

@[expose] def hdW (st : List (List Nat)) : List Nat := st.headD []

@[expose] def stepW (WC : Nat → List Nat) (ins : Nat) (st : List (List Nat)) : List (List Nat) :=
  bif Nat.beq (Nat.land ins 3) 0 then [Nat.shiftRight ins 2] :: st
  else bif Nat.beq (Nat.land ins 3) 1 then WC (Nat.shiftRight ins 2) :: st
  else bif Nat.beq (Nat.land ins 3) 2 then (hdW st.tail ++ hdW st) :: st.tail.tail
  else (List.replicate (Nat.shiftRight ins 2 % 65536) (hdW st)).flatten :: st.tail

@[expose] def progW (WC : Nat → List Nat) : List Nat → List (List Nat) → List (List Nat)
  | [], st => st
  | ins :: P, st => progW WC P (stepW WC ins st)

@[expose] def progWord (WC : Nat → List Nat) (P : List Nat) : List Nat := hdW (progW WC P [])

@[expose] def letsOK (L : Nat) (P : List Nat) : Bool :=
  P.all fun ins => !Nat.beq (Nat.land ins 3) 0 || Nat.blt (Nat.shiftRight ins 2) (2 * L)

@[expose] def refsOK (k : Nat) (P : List Nat) : Bool :=
  P.all fun ins => !Nat.beq (Nat.land ins 3) 1 || Nat.blt (Nat.shiftRight ins 2) k

@[expose] def codesOK (L : Nat) (w : List Nat) : Bool := w.all fun c => Nat.blt c (2 * L)

@[expose] def codeOf (x : Nat × Bool) : Nat := 2 * x.1 + bif x.2 then 1 else 0

@[expose] def flipC (c : Nat) : Nat := c + 1 - 2 * (c % 2)

@[expose] def invC (w : List Nat) : List Nat := (w.map flipC).reverse

@[expose] def rotC (w : List Nat) (n : Nat) : List Nat := w.drop n ++ w.take n

@[expose] def coverOK (rels : List (List (Nat × Bool))) (WC : Nat → List Nat)
    (PR : Nat → List Nat) (nR : Nat) (r c : Nat) : Bool :=
  Nat.blt (c % 1024) nR &&
    (rels.getD r []).map codeOf ==
      rotC (bif Nat.beq (c / 1048576) 1 then invC (progWord WC (PR (c % 1024)))
        else progWord WC (PR (c % 1024))) (c / 1024 % 1024)

@[expose] def coverAll (rels : List (List (Nat × Bool))) (WC : Nat → List Nat)
    (PR : Nat → List Nat) (nR : Nat) (cv : Nat → Nat) : Nat → Bool
  | 0 => true
  | n + 1 => coverAll rels WC PR nR cv n && coverOK rels WC PR nR n (cv n)

@[expose] def statesOK (L : Nat) (WC : Nat → List Nat) (PS : Nat → List Nat) : Nat → Bool
  | 0 => true
  | k + 1 => statesOK L WC PS k && letsOK L (PS k) && refsOK k (PS k) &&
      progWord WC (PS k) == WC k && codesOK L (WC k)

@[expose] def relProgsOK (L nS : Nat) (PR : Nat → List Nat) : Nat → Bool
  | 0 => true
  | j + 1 => relProgsOK L nS PR j && letsOK L (PR j) && refsOK nS (PR j)

end CFSG.KC.WP

end
