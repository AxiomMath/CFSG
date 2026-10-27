module

public import Certificates.Data.E189E4tCheck

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4C

variable {n : ℕ}

@[expose] def splitWit (L : List (Equiv.Perm (Fin n))) (i j w c : Equiv.Perm (Fin n)) : Bool :=
  decide (c * c = c⁻¹) && norms L i j c && commGens (w * i * w⁻¹) (w * j * w⁻¹) c &&
    !commGens i j c

@[expose] def splitOK (L : List (Equiv.Perm (Fin n))) (r i j : Equiv.Perm (Fin n))
    (cs : List (Equiv.Perm (Fin n))) (w : Equiv.Perm (Fin n)) : Bool :=
  !(decide (w * r * w⁻¹ = r) && !norms L i j w) || cs.any fun c => splitWit L i j w c

@[expose] def splitCheck (L : List (Equiv.Perm (Fin n))) (r i j : Equiv.Perm (Fin n))
    (ws cs : List (Equiv.Perm (Fin n))) : Bool :=
  (List.range ws.length).all fun k => splitOK L r i j cs (ws.getD k 1)

end CFSG.ClassicalInvolution.Q3.TL4.E4C

namespace CFSG.ClassicalInvolution.Q3.TL4.E4A

open CFSG.Monster.B.Co2.Native

variable (n : Nat)

@[expose] def splitWitA (L : List (Array Nat)) (i j w c : Array Nat) : Bool :=
  eqA n (compA n c c) (invCand n c) && normsA n L i j c &&
    commGensA n (conjA n w i) (conjA n w j) c && !commGensA n i j c

@[expose] def splitOKA (L : List (Array Nat)) (r i j : Array Nat) (cs : List (Array Nat))
    (w : Array Nat) : Bool :=
  !(eqA n (conjA n w r) r && !normsA n L i j w) || cs.any fun c => splitWitA n L i j w c

@[expose] def splitCheckA (L : List (Array Nat)) (r i j : Array Nat) (ws cs : List (Array Nat)) :
    Bool :=
  (List.range ws.length).all fun k => splitOKA n L r i j cs (ws.getD k (idA n))

end CFSG.ClassicalInvolution.Q3.TL4.E4A
