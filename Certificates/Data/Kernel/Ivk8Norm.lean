module

public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

namespace CFSG.KS.Ivk8Norm

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.PK

@[expose] def pkB (n : Nat) (p : Nat × Nat) : Bool :=
  (List.range n).all fun i =>
    Nat.blt (fd (wd n) p.1 i) n && Nat.blt (fd (wd n) p.2 i) n &&
      Nat.beq (fd (wd n) p.2 (fd (wd n) p.1 i)) i && Nat.beq (fd (wd n) p.1 (fd (wd n) p.2 i)) i

theorem pkOK_of_pkB {n : Nat} {p : Nat × Nat} (h : pkB n p = true) : PkOK n p := by
  intro i hi
  have h1 := List.all_eq_true.1 h i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h1
  exact ⟨h1.1.1.1, h1.1.1.2, h1.1.2, h1.2⟩

@[expose] def mkV (n : Nat) (p : Nat × Nat) (h : pkB n p = true) : VP n := ⟨p, pkOK_of_pkB h⟩

@[expose] def letV {n : Nat} (S : List (VP n)) (z : Int) : VP n :=
  if 0 < z then S.getD (z.toNat - 1) (oneV n) else invV (S.getD ((-z).toNat - 1) (oneV n))

@[expose] def evV {n : Nat} (S : List (VP n)) (w : List Int) : VP n :=
  w.foldr (fun z acc => mulV (letV S z) acc) (oneV n)

@[expose] def buildV {n : Nat} : List (VP n) → List (List Int) → List (VP n)
  | S, [] => S
  | S, w :: ws => buildV (S ++ [evV S w]) ws

@[expose] def ordV {n k : Nat} (Sc : List (VP n)) (base : Vector (Fin n) k) : Nat :=
  ((List.finRange k).map fun i => (levelV Sc base i).entries.length).prod

@[expose] def difV {n : Nat} (a b : VP n) : Bool :=
  (List.range n).any fun i => !Nat.beq (fd (wd n) a.1.1 i) (fd (wd n) b.1.1 i)

@[expose] def conjV {n : Nat} (c y : VP n) : VP n := mulV (mulV c y) (invV c)

@[expose] def neV {n : Nat} (z x : VP n) : Bool := difV z x && difV z (invV x)

@[expose] def movesV {n : Nat} (h x : VP n) : Bool := neV (conjV h x) x

@[expose] def movesAB {n : Nat} (A B x : VP n) : Bool := movesV A x || movesV B x

@[expose] def okY {n : Nat} (A B c y : VP n) : Bool :=
  difV (mulV y (mulV y y)) (oneV n) || !difV y (oneV n) || movesAB A B (conjV c y)

@[expose] def chk {n : Nat} (A B : VP n) (cs K : List (VP n)) : Bool :=
  cs.all fun c => K.all fun y => okY A B c y

@[expose] def kleinOK {n : Nat} (A B : VP n) : Bool :=
  !difV (mulV A A) (oneV n) && !difV (mulV B B) (oneV n) && !difV (mulV A B) (mulV B A) &&
    difV A (oneV n) && difV B (oneV n) && difV A B

@[expose] def conjOK {n : Nat} (r : VP n) (ps : List (VP n × VP n)) : Bool :=
  ps.all fun p => !difV (conjV p.1 r) p.2

@[expose] def commOK {n : Nat} (r : VP n) (S : List (VP n)) : Bool :=
  S.all fun s => !difV (mulV s r) (mulV r s)

end CFSG.KS.Ivk8Norm

end
