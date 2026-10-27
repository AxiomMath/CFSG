module

public import Certificates.Data.NPL587

public section

namespace CFSG.Quasithin.H13.NPLK

open CFSG.Quasithin.H13.NPL

@[expose] def wordL (w : List ℕ) : ℕ := w.foldl mulC (idC ())

@[expose] def memB (S : List ℕ) (c : ℕ) : Bool := S.any fun x => x == c

@[expose] def incB : ℕ → List ℕ → Bool
  | _, [] => true
  | a, b :: t => Nat.blt a b && incB b t

@[expose] def tgens (_ : Unit := ()) : List (Equiv.Perm (Fin 8)) :=
  [Equiv.swap 0 1, Equiv.swap 1 2, Equiv.swap 2 3, Equiv.swap 3 4, Equiv.swap 4 5,
    Equiv.swap 5 6, Equiv.swap 6 7]

@[expose] def tcodes (_ : Unit := ()) : List ℕ := (tgens ()).map encP

@[expose] def s0OK (gens s0 : List ℕ) (s0w : List (ℕ × List ℕ)) : Bool :=
  (gens == S0codes ()) && (s0w.map Prod.fst == s0) && (s0.length == 64) && incB 0 s0 &&
    (s0w.all fun e => (e.2.all fun a => memB gens a) && wordL e.2 == e.1) &&
    (s0.all fun c => gens.all fun g => memB s0 (mulC c g)) && memB s0 (idC ()) &&
    (gens.all fun g => mulC g g == idC ()) && (s0.all fun c => powC c 4 == idC ())

@[expose] def lettC (r o a : ℕ) : ℕ :=
  if a == 0 then r else if a == 1 then powC r (o - 1) else a

@[expose] def wordR (r o : ℕ) (w : List ℕ) : ℕ := wordL (w.map (lettC r o))

@[expose] def lettOK (gens : List ℕ) (w : List ℕ) : Bool :=
  w.all fun a => a == 0 || a == 1 || memB gens a

@[expose] def pairsOK (S : List ℕ) : List (ℕ × ℕ × List ℕ × List ℕ) → Bool
  | [] => true
  | a :: t => (t.all fun b => !memB S (mulC a.1 b.2.1)) && pairsOK S t

@[expose] def repOK (gens S : List ℕ) (e : ℕ × ℕ × List ℕ × List (ℕ × ℕ × List ℕ × List ℕ)) :
    Bool :=
  (e.2.1 == 5 || e.2.1 == 7) && powC e.1 e.2.1 == idC () &&
    (e.2.2.1.all fun a => memB (tcodes ()) a) && wordL e.2.2.1 == e.1 &&
    e.2.2.2.length == 8 &&
    (e.2.2.2.all fun x => lettOK gens x.2.2.1 && lettOK gens x.2.2.2 &&
      wordR e.1 e.2.1 x.2.2.1 == x.1 && wordR e.1 e.2.1 x.2.2.2 == x.2.1 &&
      mulC x.2.1 x.1 == idC ()) &&
    pairsOK S e.2.2.2

@[expose] def qOK (repc : List ℕ) (e : ℕ × ℕ × ℕ × ℕ) : Bool :=
  memB repc e.2.1 && powC e.2.1 e.2.2.1 == e.1 && powC e.1 e.2.2.2 == e.2.1 && !(e.1 == idC ())

@[expose] def tauC (q h : ℕ) : ℕ := mulC (mulC h q) (powC h 3)

@[expose] def covGo (S qc : List ℕ) (hi : ℕ) : ℕ → List (ℕ × ℕ) → Bool
  | prev, [] => prev == hi
  | prev, p :: t =>
    memB qc p.1 && memB S p.2 && Nat.blt prev (tauC p.1 p.2) && covGo S qc hi (tauC p.1 p.2) t

@[expose] def covOK (S qc : List ℕ) (lo hi : ℕ) (L : List (ℕ × ℕ)) : Bool := covGo S qc hi lo L

end CFSG.Quasithin.H13.NPLK

end
