module

public import Certificates.Data.GH23Lat

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.GH23Data

set_option compiler.extract_closed false

@[expose] def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

@[expose] def nodupAux : List Nat → Std.HashSet Nat → Bool
  | [], _ => true
  | a :: l, s => !s.contains a && nodupAux l (s.insert a)

@[expose] def commIn (E : List Nat) (T : Std.HashSet Nat) : Bool :=
  let ps := E.map fun x => (x, invC x)
  ps.all (fun a => invOK a.1) &&
    ps.all fun a => ps.all fun b => T.contains (mulC (mulC (mulC a.1 b.1) a.2) b.2)

@[expose] def solvAux (E : List Nat) : List (List Nat) → Bool
  | [] => E.all (· == oneC)
  | g :: rest =>
    match closData g with
    | none => false
    | some (E', T') => commIn E T' && solvAux E' rest

@[expose] def solvOK (P : MemTab) (chain : List (List Nat)) : Bool := solvAux P.elems chain

@[expose] def twoOK (P : MemTab) (ngens : List Nat) : Bool :=
  match closData ngens with
  | none => false
  | some (EN, TN) =>
    ngens.all P.tab.contains && ngens.any (· != oneC) && EN.all (fun e => mulC e e == oneC) &&
      P.gens.all fun x => invOK x && ngens.all fun n =>
        TN.contains (mulC (mulC x n) (invC x)) && TN.contains (mulC (mulC (invC x) n) x)

@[expose] def carmRels (imgs : List Nat) : Bool :=
  (List.range imgs.length).all fun i =>
    mulC (mulC (imgs.getD i 0) (imgs.getD i 0)) (imgs.getD i 0) == oneC &&
      (List.range imgs.length).all fun j =>
        i == j || mulC (mulC (imgs.getD i 0) (imgs.getD j 0))
          (mulC (imgs.getD i 0) (imgs.getD j 0)) == oneC

@[expose] def coxRels (imgs : List Nat) : Bool :=
  (List.range imgs.length).all (fun i => mulC (imgs.getD i 0) (imgs.getD i 0) == oneC) &&
  (List.range imgs.length).all (fun i =>
    decide (imgs.length ≤ i + 1) ||
      mulC (mulC (imgs.getD i 0) (imgs.getD (i + 1) 0)) (imgs.getD i 0) ==
        mulC (mulC (imgs.getD (i + 1) 0) (imgs.getD i 0)) (imgs.getD (i + 1) 0)) &&
  (List.range imgs.length).all fun i => (List.range imgs.length).all fun j =>
    decide (j < i + 2) ||
      mulC (imgs.getD i 0) (imgs.getD j 0) == mulC (imgs.getD j 0) (imgs.getD i 0)

@[expose] def altOK (P : MemTab) (n : Nat) (imgs : List Nat) : Bool :=
  decide (3 ≤ n) && decide (imgs.length + 2 = n) && carmRels imgs && imgs.all P.tab.contains &&
    match closData imgs with
    | none => false
    | some (E, T) => decide (E.length = fact n / 2) && P.gens.all T.contains

@[expose] def symOK (P : MemTab) (n : Nat) (imgs : List Nat) : Bool :=
  decide (imgs.length + 1 = n) && coxRels imgs && imgs.all P.tab.contains &&
    match closData imgs with
    | none => false
    | some (E, T) => decide (E.length = fact n) && P.gens.all T.contains

@[expose] def z3a5OK (P : MemTab) (imgs : List Nat) (z : Nat) : Bool :=
  decide (imgs.length = 3) && carmRels imgs && mulC (mulC z z) z == oneC &&
    imgs.all (fun x => mulC z x == mulC x z) && (imgs ++ [z]).all P.tab.contains &&
    match closData (imgs ++ [z]) with
    | none => false
    | some (E, T) => decide (E.length = 180) && P.gens.all T.contains

@[expose] def q2OK (_ : Unit := ()) : Bool :=
  match closData q2gens with
  | none => false
  | some (E, _) => decide (E.length = 168)

@[expose] def idx2OK (P L : MemTab) : Bool :=
  L.gens.all P.tab.contains && decide (P.elems.length = 2 * L.elems.length)

@[expose] def phiTable (P : MemTab) (imgs : List Nat) : Std.HashMap Nat Nat := Id.run do
  let mut phi : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert oneC oneC
  for t in bfsChain P.gens do
    let k := P.gens.idxOf t.2.2
    phi := phi.insert t.1 (mulC (phi.getD t.2.1 0) (imgs.getD k 0))
  return phi

@[expose] def glOK (P : MemTab) (imgs : List Nat) : Bool :=
  match closData q2gens with
  | none => false
  | some (EQ, TQ) =>
    let phi := phiTable P imgs
    decide (imgs.length = P.gens.length) && imgs.all TQ.contains &&
      decide (EQ.length = P.elems.length) && phi[oneC]? == some oneC &&
      (P.elems.all fun x =>
        match phi[x]? with
        | none => false
        | some y => TQ.contains y && (List.range P.gens.length).all fun k =>
            phi[mulC x (P.gens.getD k 0)]? == some (mulC y (imgs.getD k 0))) &&
      nodupAux (P.elems.map fun x => phi.getD x 0) {}

end CFSG.OddStandard.SmallF3.HarrisU33.GH23Data
