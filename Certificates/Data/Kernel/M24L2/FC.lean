module

public import Certificates.Data.Kernel.M24L2.D
public import Certificates.Data.Kernel.M24L2.FCPos

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

inductive FcT (α : Type) where
  | leaf : FcT α
  | node : FcT α → α → FcT α → FcT α

@[expose] def evensFc {α : Type} : List α → List α
  | [] => []
  | [x] => [x]
  | x :: _ :: l => x :: evensFc l

@[expose] def oddsFc {α : Type} : List α → List α
  | [] => []
  | [_] => []
  | _ :: y :: l => y :: oddsFc l

@[expose] def ofListFc {α : Type} : Nat → List α → FcT α
  | 0, _ => .leaf
  | _ + 1, [] => .leaf
  | n + 1, x :: l => .node (ofListFc n (evensFc l)) x (ofListFc n (oddsFc l))

@[expose] def treeFc {α : Type} (L : List α) : FcT α := ofListFc L.length L

@[expose] def getFc {α : Type} [Inhabited α] : FcT α → Nat → α
  | .leaf, _ => default
  | .node _ x _, 0 => x
  | .node l _ r, i + 1 => if i % 2 = 0 then getFc l (i / 2) else getFc r (i / 2)

@[expose] def fcSrcK (l : List (Nat × List (Fin 3))) : List ((Nat × List (Fin 3)) × Fin 3) :=
  l.flatMap fun xw => (List.finRange 3).map fun k => (xw, k)

@[expose] noncomputable def fcPosOk (T : FcT (Nat × List (Fin 3))) : Bool :=
  Nat.beq dQ.length 1152 && Nat.beq (fcSrcK dQ).length fcPosK.length &&
    (List.zipWith (fun s m => Nat.blt m 1152 && Nat.beq (getFc T m).1 (mulC s.1.1 (dC s.2)))
      (fcSrcK dQ) fcPosK).all id

@[expose] noncomputable def fcAllK3 : List FCConds :=
  let T := treeFc dQ
  let ps := List.zipWith (fun s m => (s.1.2 ++ [s.2], (getFc T m).2)) (fcSrcK dQ) fcPosK
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

@[expose] def nthFc {α : Type} : List α → Nat → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: l, n + 1 => nthFc l n

@[expose] noncomputable def condFcK (cs : FCConds) (u : Fin 3 → Nat) (k : Nat) : Bool :=
  bif Nat.beq (k % 4) 0 then (nthFc cs.wA (k / 4)).all fun w => isBtK (evK u w)
  else bif Nat.beq (k % 4) 1 then (nthFc cs.wB (k / 4)).all fun w => isTtK (evK u w)
  else bif Nat.beq (k % 4) 2 then
    (nthFc cs.wP (k / 4)).all fun p => Nat.beq (evK u p.1) (evK u p.2)
  else (nthFc cs.wN (k / 4)).all fun w => !(Nat.beq (evK u w) idC)

@[expose] def fcTupK (c : FCConds) :
    List (List (Fin 3)) × List (List (Fin 3)) × List (List (Fin 3)) × List (List (Fin 3) × List (Fin 3)) :=
  (c.wA, c.wB, c.wN, c.wP)

@[expose] noncomputable def goodFcK (cs : FCConds) (u : Fin 3 → Nat) : Bool :=
  cs.wA.all (fun w => isBtK (evK u w)) && cs.wB.all (fun w => isTtK (evK u w)) &&
    cs.wP.all (fun p => p.1 == p.2 || Nat.beq (evK u p.1) (evK u p.2)) &&
    cs.wN.all fun w => !(Nat.beq (evK u w) idC)

@[expose] noncomputable def flOkK (cs : FCConds) (P : List Nat) : List Nat → List Nat → Bool
  | [], [] => true
  | v :: dl, 0 :: fl => goodFcK cs (asgK (P ++ [v])) && flOkK cs P dl fl
  | v :: dl, (k + 1) :: fl => !condFcK cs (asgK (P ++ [v])) k && flOkK cs P dl fl
  | _, _ => false

@[expose] def selFc : List Nat → List Nat → List Nat
  | v :: dl, 0 :: fl => v :: selFc dl fl
  | _ :: dl, (_ + 1) :: fl => selFc dl fl
  | _, _ => []

@[expose] noncomputable def repsOkK (C : List Nat) :
    List Nat → List Nat → List (Bool × Nat × Nat) → Bool
  | _, [], [] => true
  | reps, v :: G, (a, r, e) :: rc =>
    C.contains e && conjEqK e v r &&
      bif a then Nat.beq r v && (reps.all fun x => C.all fun f => !conjEqK f v x) &&
        repsOkK C (reps ++ [v]) G rc
      else reps.contains r && repsOkK C reps G rc
  | _, _, _ => false

@[expose] def repsOfFc : List Nat → List (Bool × Nat × Nat) → List Nat
  | v :: G, (true, _, _) :: rc => v :: repsOfFc G rc
  | _ :: G, (false, _, _) :: rc => repsOfFc G rc
  | _, _ => []

@[expose] def recFc (R : List (List Nat × List Nat × List (Bool × Nat × Nat))) (P : List Nat) :
    List Nat × List (Bool × Nat × Nat) :=
  ((R.find? fun x => x.1 == P).map Prod.snd).getD ([], [])

@[expose] noncomputable def fcTreeR (dl : List Nat) (cs : List FCConds) (thc : List Nat)
    (R : List (List Nat × List Nat × List (Bool × Nat × Nat))) : Nat → List Nat → Bool
  | 0, P => P == thc
  | fuel + 1, P =>
    let x := recFc R P
    let C := dl.filter fun e => P.all fun p => commK e p
    let G := selFc dl x.1
    let t := thc.getD P.length 0
    let G' := if G.contains t then t :: G else G
    let reps := repsOfFc G' x.2
    flOkK (cs.getD P.length default) P dl x.1 && repsOkK C [] G' x.2 &&
      reps.all (fun r => decide (r < 1048576)) &&
      reps.all fun r => fcTreeR dl cs thc R fuel (P ++ [r])

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
