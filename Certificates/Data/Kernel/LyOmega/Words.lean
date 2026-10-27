module

public import Certificates.Data.Kernel.LyOmega.Chart

public section

namespace CFSG.KC.LyOm

open CFSG.KC.Ord

@[expose] noncomputable def slpLet (C : BConsts) (A B Bi : Nat) (vals : List (Nat × Nat)) (j : Nat)
    (z : Int) : Nat × Nat :=
  if z = 1 then (A, A) else if z = -1 then (A, A) else if z = 2 then (B, Bi)
  else if z.natAbs ≤ 2 then (Bi, B)
  else if z.natAbs - 3 < j then
    (if 0 < z then vals.getD (z.natAbs - 3) (C.ONEF, C.ONEF)
      else ((vals.getD (z.natAbs - 3) (C.ONEF, C.ONEF)).2, (vals.getD (z.natAbs - 3) (C.ONEF, C.ONEF)).1))
  else (C.ONEF, C.ONEF)

@[expose] noncomputable def wordLanes (C : BConsts) (A B Bi : Nat) (vals : List (Nat × Nat))
    (j : Nat) (w : List Int) : Nat × Nat :=
  List.foldl (fun p z => (fun q : Nat × Nat => (fMul C p.1 q.1, fMul C q.2 p.2))
    (slpLet C A B Bi vals j z)) (C.ONEF, C.ONEF) w

@[expose] noncomputable def slpRun (C : BConsts) (A B Bi : Nat) :
    List (Nat × Nat) → List (List Int) → List (Nat × Nat) :=
  fun vals ws => List.rec (motive := fun _ => List (Nat × Nat) → List (Nat × Nat)) (fun v => v)
    (fun w _ ih v => ih (v ++ [wordLanes C A B Bi v (List.length v) w])) ws vals

@[expose] noncomputable def slpVals (C : BConsts) (A B Bi : Nat) (ws : List (List Int)) :
    List (Nat × Nat) :=
  slpRun C A B Bi [] ws

@[expose] def decLetter (n : Nat) : Int :=
  if n % 2 = 0 then Int.ofNat (n / 2) else -Int.ofNat (n / 2)

@[expose] def decWords (ws : List (List Nat)) : List (List Int) := ws.map (List.map decLetter)

@[expose] noncomputable def fPow (C : BConsts) (X n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) C.ONEF (fun _ acc => fMul C acc X) n

@[expose] noncomputable def relLanes (C : BConsts) (A B Bi : Nat) (V : List (Nat × Nat))
    (w : List Int) : Nat :=
  (wordLanes C A B Bi V (List.length V) w).1

@[expose] noncomputable def relsOK (C : BConsts) (A B Bi : Nat) (V : List (Nat × Nat))
    (rels : List (List Int × List Int)) : Bool :=
  rels.all fun r => Nat.beq (relLanes C A B Bi V r.1) (relLanes C A B Bi V r.2)

@[expose] noncomputable def nesOK (C : BConsts) (A B Bi : Nat) (V : List (Nat × Nat))
    (nes : List (List Int × List Int × Nat)) : Bool :=
  nes.all fun r => notB (Nat.beq (relLanes C A B Bi V r.1) (relLanes C A B Bi V r.2.1))

end CFSG.KC.LyOm

end
