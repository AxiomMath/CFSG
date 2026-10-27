module

public import Certificates.Data.E4QuatCheck
public import Certificates.Data.E4QuatArr

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4C

variable {n : ℕ}

@[expose] def commGens (i j b : Equiv.Perm (Fin n)) : Bool :=
  decide (b * i = i * b) && decide (b * j = j * b)

@[expose] def goodWit (r i j t x : Equiv.Perm (Fin n)) : Bool :=
  commGens i j (x⁻¹ * (r * t) * x) && commGens i j ((x * t)⁻¹ * (r * t) * (x * t))

@[expose] def relevantT (L : List (Equiv.Perm (Fin n))) (r i j t : Equiv.Perm (Fin n)) : Bool :=
  decide (t * r = r * t) && !norms L i j t

@[expose] def memberOK (L : List (Equiv.Perm (Fin n))) (r i j : Equiv.Perm (Fin n))
    (ws : List (Equiv.Perm (Fin n))) (t : Equiv.Perm (Fin n)) : Bool :=
  !relevantT L r i j t || (List.range ws.length).any fun l => goodWit r i j t (ws.getD l 1)

@[expose] def tCheck (L : List (Equiv.Perm (Fin n))) (r i j : Equiv.Perm (Fin n))
    (ws : List (Equiv.Perm (Fin n))) : Bool :=
  (List.range ws.length).all fun k => memberOK L r i j ws (ws.getD k 1 * r * (ws.getD k 1)⁻¹)

end CFSG.ClassicalInvolution.Q3.TL4.E4C

namespace CFSG.ClassicalInvolution.Q3.TL4.E4A

open CFSG.Monster.B.Co2.Native

variable (n : Nat)

@[expose] def commGensA (i j b : Array Nat) : Bool :=
  eqA n (compA n b i) (compA n i b) && eqA n (compA n b j) (compA n j b)

@[expose] def goodWitA (r i j t x : Array Nat) : Bool :=
  commGensA n i j (compA n (compA n (invCand n x) (compA n r t)) x) &&
    commGensA n i j
      (compA n (compA n (invCand n (compA n x t)) (compA n r t)) (compA n x t))

@[expose] def relevantTA (L : List (Array Nat)) (r i j t : Array Nat) : Bool :=
  eqA n (compA n t r) (compA n r t) && !normsA n L i j t

@[expose] def memberOKA (L : List (Array Nat)) (r i j : Array Nat) (ws : List (Array Nat))
    (t : Array Nat) : Bool :=
  !relevantTA n L r i j t ||
    (List.range ws.length).any fun l => goodWitA n r i j t (ws.getD l (idA n))

@[expose] def tCheckA (L : List (Array Nat)) (r i j : Array Nat) (ws : List (Array Nat)) : Bool :=
  (List.range ws.length).all fun k =>
    memberOKA n L r i j ws (conjA n (ws.getD k (idA n)) r)

end CFSG.ClassicalInvolution.Q3.TL4.E4A
