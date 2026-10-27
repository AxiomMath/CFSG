module

public import Certificates.Data.Kernel.M24L2.D

public section

namespace CFSG.KC.M24L2

open CFSG.CGT.M24R CFSG.KC.Enum

@[expose] noncomputable def dQ : List (Nat × List (Fin 3)) := dTwin.all.reverse

@[expose] noncomputable def fcAllK : List FCConds :=
  let ws := dQ.map Prod.snd
  let ps := dQ.flatMap fun xw => (List.finRange 3).map fun k =>
    (xw.2 ++ [k], ((dQ.find? fun e => e.1 == mulC xw.1 (dC k)).map Prod.snd).getD [])
  (List.range 3).map fun j =>
    { wA := ws.filter fun w => maxL w == j && isTtK (evK dC w)
      wB := ws.filter fun w => maxL w == j && isBtK (evK dC w)
      wN := ws.filter fun w => maxL w == j && !(Nat.beq (evK dC w) idC)
      wP := ps.filter fun p => max (maxL p.1) (maxL p.2) == j &&
        Nat.beq (evK dC p.1) (evK dC p.2) }

@[expose] noncomputable def fcAllK2 : List FCConds :=
  let ps := dQ.flatMap fun xw => (List.finRange 3).map fun k =>
    (xw.2 ++ [k], ((dQ.find? fun e => e.1 == mulC xw.1 (dC k)).map Prod.snd).getD [])
  (List.range 3).map fun j =>
    { wA := (dQ.filter fun e => maxL e.2 == j && isTtK e.1).map Prod.snd
      wB := (dQ.filter fun e => maxL e.2 == j && isBtK e.1).map Prod.snd
      wN := (dQ.filter fun e => maxL e.2 == j && !(Nat.beq e.1 idC)).map Prod.snd
      wP := ps.filter fun p => max (maxL p.1) (maxL p.2) == j }

@[expose] noncomputable def goodCK (cs : FCConds) (u : Fin 3 → Nat) : Bool :=
  cs.wA.all (fun w => isBtK (evK u w)) && cs.wB.all (fun w => isTtK (evK u w)) &&
    cs.wP.all (fun p => Nat.beq (evK u p.1) (evK u p.2)) &&
    cs.wN.all fun w => !(Nat.beq (evK u w) idC)

@[expose] noncomputable def asgK (P : List Nat) : Fin 3 → Nat := fun k => P.getD k.val idC

@[expose] noncomputable def conjEqK (e v r : Nat) : Bool := Nat.beq (mulC e v) (mulC r e)

@[expose] noncomputable def mkRepsK (C G : List Nat) : List Nat :=
  G.foldl (fun reps v =>
    if reps.any fun r => C.any fun e => conjEqK e v r then reps else reps ++ [v]) []

@[expose] noncomputable def fcTreeK (dl : List Nat) (cs : List FCConds) (thc : List Nat) :
    Nat → List Nat → Bool
  | 0, P => P == thc
  | fuel + 1, P =>
    let j := P.length
    let C := dl.filter fun e => P.all fun p => commK e p
    let G := dl.filter fun v => goodCK (cs.getD j default) (asgK (P ++ [v]))
    let t := thc.getD j 0
    let reps := mkRepsK C (if G.contains t then t :: G else G)
    reps.all (fun r => decide (r < 1048576)) &&
      G.all (fun v => reps.any fun r => C.any fun e => conjEqK e v r) &&
      reps.all fun r => fcTreeK dl cs thc fuel (P ++ [r])

@[expose] noncomputable def thCodesK : List Nat := (List.finRange 3).map thC

@[expose] noncomputable def sortedK : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: l => Nat.blt a b && sortedK (b :: l)

@[expose] noncomputable def dLinB (m : Nat) : Bool :=
  [idC, b0C, b1C, b01C].any fun k =>
    Nat.beq (mulC (Nat.mul (nat_lit 16) m) (Nat.mul (nat_lit 16) (Nat.shiftRight b0C (nat_lit 4))))
      (mulC (Nat.mul (nat_lit 16) (Nat.shiftRight k (nat_lit 4))) (Nat.mul (nat_lit 16) m))

@[expose] noncomputable def dLM (D : List Nat) (m : Nat) : Bool :=
  bIf(dLinB m,
    allN 16 fun v => letN (Nat.add v (Nat.mul (nat_lit 16) m)) fun c =>
      bIf(normBK c, D.contains c, true), true)

@[expose] noncomputable def dLE (D : List Nat) (E : List (Nat × Nat × Nat)) : Bool :=
  dLM D (nat_lit 33825) && allL (fun e => letN e.1 fun m => dLM D m) E

end CFSG.KC.M24L2
