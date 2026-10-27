module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42Check
public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.RankThree.PartOne.KS.PKitLines

public section

namespace CFSG.KC.D42K

open CFSG.Quasithin CFSG.AGLEmbedding.D4Two CFSG.AGLEmbedding.ChevOuter

@[expose] def gmTab : Nat := 2821848294356612419217921029917578219971947684264937521152

@[expose] def frTab : Nat := 7072520

@[expose] def gmK (a b : Nat) : Nat := (gmTab >>> (3 * (8 * a + b))) &&& 7

@[expose] def frK (a : Nat) : Nat := (frTab >>> (3 * a)) &&& 7

@[expose] def encM (A : Array GF8) : List (List Nat) :=
  (List.range 8).map fun i => (List.range 8).map fun j => (A.getD (8 * i + j) 0).toNat

@[expose] def entK (A : List (List Nat)) (i j : Nat) : Nat := (A.getD i []).getD j 0

@[expose] def dotK (A B : List (List Nat)) (i j : Nat) : Nat :=
  gmK (entK A i 0) (entK B 0 j) ^^^ gmK (entK A i 1) (entK B 1 j) ^^^
    gmK (entK A i 2) (entK B 2 j) ^^^ gmK (entK A i 3) (entK B 3 j) ^^^
    gmK (entK A i 4) (entK B 4 j) ^^^ gmK (entK A i 5) (entK B 5 j) ^^^
    gmK (entK A i 6) (entK B 6 j) ^^^ gmK (entK A i 7) (entK B 7 j)

@[expose] def mulMK (A B : List (List Nat)) : List (List Nat) :=
  (List.range 8).map fun i => (List.range 8).map fun j => dotK A B i j

@[expose] def frobK (A : List (List Nat)) : List (List Nat) := A.map fun r => r.map frK

@[expose] def frobPowK : Nat → List (List Nat) → List (List Nat)
  | 0, A => A
  | n + 1, A => frobK (frobPowK n A)

abbrev PrK : Type := List (List Nat) × Nat

@[expose] def encP (p : Pr) : PrK := (encM p.1, p.2)

@[expose] def mulPK (p q : PrK) : PrK := (mulMK p.1 (frobPowK p.2 q.1), (p.2 + q.2) % 3)

@[expose] def onePK : PrK := encP oneP

@[expose] def powPK (p : PrK) : Nat → PrK
  | 0 => onePK
  | n + 1 => mulPK p (powPK p n)

@[expose] def symPK (s : Nat) : PrK := encP (symP s)

@[expose] def wordPK (w : List Nat) : PrK := w.foldr (fun s p => mulPK (symPK s) p) onePK

@[expose] def eK (i : Nat) : PrK := wordPK (d42E.getD i [])

@[expose] def nK (j : Nat) : PrK := wordPK (d42N.getD j [])

@[expose] def nInvK (j : Nat) : PrK := wordPK (invWord (d42N.getD j []))

@[expose] def nListK : List PrK := (List.range (d42N1 + d42N2)).map nK

@[expose] def nInvListK : List PrK := (List.range (d42N1 + d42N2)).map nInvK

@[expose] def slpEltK (i : Nat) : PrK :=
  if i % 2 = 0 then nListK.getD (i / 2) onePK else nInvListK.getD (i / 2) onePK

@[expose] def slpPK (ids : List Nat) : PrK := ids.foldl (fun acc i => mulPK acc (slpEltK i)) onePK

@[expose] def d42SlpK (k : Nat) : Bool :=
  let x := d42Slp.getD k (0, [])
  x.2.all (fun i => decide (i < 2 * (d42N1 + d42N2))) && slpPK x.2 == encP (letterArr x.1, 0)

@[expose] def d42CheckK : Bool :=
  (List.range 3).all (fun i => powPK (eK i) 3 == onePK) &&
  mulPK (eK 0) (eK 1) == mulPK (eK 1) (eK 0) &&
  mulPK (eK 0) (eK 2) == mulPK (eK 2) (eK 0) &&
  mulPK (eK 1) (eK 2) == mulPK (eK 2) (eK 1) &&
  (List.range 3).all (fun a => (List.range 3).all fun b => (List.range 3).all fun c =>
    (a == 0 && b == 0 && c == 0) ||
      mulPK (mulPK (powPK (eK 0) a) (powPK (eK 1) b)) (powPK (eK 2) c) != onePK) &&
  (List.range (d42N1 + d42N2)).all (fun j => mulPK (nK j) (nInvK j) == onePK) &&
  (List.range d42N1).all (fun j => [0, 1].all fun g => (List.range 3).any fun s =>
    (List.range 3).any fun t =>
      mulPK (mulPK (nK j) (eK g)) (nInvK j) == mulPK (powPK (eK 0) s) (powPK (eK 1) t)) &&
  (List.range d42N2).all (fun j => [0, 2].all fun g => (List.range 3).any fun s =>
    (List.range 3).any fun t =>
      mulPK (mulPK (nK (d42N1 + j)) (eK g)) (nInvK (d42N1 + j)) ==
        mulPK (powPK (eK 0) s) (powPK (eK 2) t)) &&
  (List.range 18).all (fun k => d42Slp.any fun x => x.1 == k)

end CFSG.KC.D42K

end
