module

public import CFSG.RankThree.Asc83Table.MatCertDefs
public import Certificates.Data.CFSGNative.SectionRank.F2Fast

public section

namespace CFSG.RankThree.Asc83Table.Native

open CFSG.SectionRank.Native CFSG.Sporadic.SmallF2.Native

@[expose] def basisW (r : Nat × Nat × Nat) (k : Nat) : Word :=
  [(r.1, k % 3), (r.2.1, k / 3 % 3), (r.2.2, k / 9 % 3)]

@[expose] def hW (r : Nat × Nat × Nat) (m : Nat) : Word := [(r.1, m % 3), (r.2.1, m / 3)]

structure J3Cert where
  nregs : Nat
  prog : List Op
  rb : Nat × Nat × Nat
  rh : Nat × Nat × Nat
  base : List MFact
  ss : List (Nat × Nat)
  cs : List Nat
  xs : List Nat

@[expose] def stabFacts (x₀ : Nat) (s : Nat × Nat) (c : Nat) : List MFact :=
  [.ord s.1 s.2, .ord c 3, .conj s.1 [(x₀, 1)] [(c, 1)]]

@[expose] def J3Cert.facts (J : J3Cert) : List MFact :=
  J.base ++ (J.ss.zip J.cs).flatMap fun q => stabFacts J.rb.1 q.1 q.2

@[expose] def J3Cert.mcert (J : J3Cert) : MCert := ⟨J.nregs, J.prog, J.facts⟩

@[expose] def matNe (X Y : Array Nat) : Bool :=
  (List.range 80).any fun t =>
    (ops2fr 80).vne ((ops2fr 80).vmul ((ops2fr 80).unit t) X)
      ((ops2fr 80).vmul ((ops2fr 80).unit t) Y)

@[expose] def colAct (X : Array Nat) (v : Nat) : Nat := vecMulN 80 (transposeRows 80 X) v

@[expose] def movedOK (pts : Array Nat) (n : Nat) (xs : List Nat) (Ts : List (Array Nat)) :
    Bool :=
  (List.range n).all fun i =>
    xs.contains i || Ts.all fun T => (ops2fr 80).vne (vecMulN 80 T pts[i]!) pts[i]!

@[expose] def conjOK (C C2 : Array (Array Nat)) : Bool :=
  (List.range C.size).all fun k => (List.range C.size).all fun l =>
    k == l || (matNe C[k]! C[l]! && matNe C[k]! C2[l]!)

@[expose] def j3Extra (R : Array (Array Nat)) (pts : Array Nat) (n : Nat) (J : J3Cert) : Bool :=
  let O := ops2fr 80
  let bw := fun k => evalW O R (basisW J.rb k)
  let root := pts[0]!
  let C := (J.cs.map fun c => R[c]!).toArray
  movedOK pts n J.xs ((List.range 26).map fun k => transposeRows 80 (bw (k + 1))) &&
    colAct R[J.rb.1]! root == root &&
    (List.range 24).all (fun k => O.vne (colAct (bw (k + 3)) root) root) &&
    (List.range 26).all (fun k => matNe (bw (k + 1)) O.one) &&
    J.ss.all (fun s => colAct R[s.1]! root == root) &&
    conjOK C (C.map fun X => O.pow X 2) &&
    (List.range 27).all (fun k => (List.range 8).all fun m =>
      matNe (O.pow (evalW O R (basisW J.rb k ++ hW J.rh (m + 1))) 3) O.one) &&
    J.ss.length == J.cs.length

@[expose] def j3Check (sA sB : String) (pts : Array Nat) (n : Nat) (J : J3Cert) : Bool :=
  mcertCheck (ops2fr 80) sA sB J.mcert &&
    j3Extra ((ops2fr 80).regsOf sA sB J.nregs J.prog) pts n J

end CFSG.RankThree.Asc83Table.Native
