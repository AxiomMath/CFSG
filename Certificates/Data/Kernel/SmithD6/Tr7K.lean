module

public import Certificates.Data.SmithD6Tr7
public import Certificates.Data.Kernel.SmithD6.IdCheck
public import Certificates.Data.Kernel.SmithD6.Tr7Data
public import Certificates.Data.Kernel.PkTree

public section

namespace CFSG.KD.SmithD6

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KC.PkTree

@[expose] def tr7PairK (x y : Nat) : Nat × Nat :=
  (min x (min y (x ^^^ y)), min x (min y (x ^^^ y)) ^^^ max x (max y (x ^^^ y)))

@[expose] noncomputable def tr7LineOK (q : Nat × Nat) : Bool :=
  Nat.blt q.1 4096 && Nat.blt q.2 4096 && lineTree.memB (4096 * q.1 + q.2)

@[expose] noncomputable def tr7Lift (q : Nat × Nat) (x : Nat) : Nat := x ^^^ id7VecK q.1 q.2 x

@[expose] noncomputable def tr7Chain (ps : List (Nat × Nat)) (x : Nat) : Nat :=
  ps.foldr (fun p acc => tr7Lift (tr7PairK p.1 p.2) acc) x

@[expose] noncomputable def tr7ChainOK : List (Nat × Nat) → Nat → Bool
  | [], _ => true
  | p :: ps, x => tr7ChainOK ps x && tr7LineOK (tr7PairK p.1 p.2) &&
      id7VecOK (tr7PairK p.1 p.2).1 (tr7PairK p.1 p.2).2 (tr7Chain ps x)

@[expose] noncomputable def tr7ColsK (j : Nat) : List Nat :=
  (List.range 32).map fun c => tr7Chain (tr7RepLines j) (2 ^ c) ^^^ 2 ^ c

@[expose] noncomputable def tr7RepOK (j : Nat) : Bool :=
  (List.range 32).all fun c => tr7ChainOK (tr7RepLines j) (2 ^ c)

@[expose] noncomputable def tr7DimK (j : Nat) : Bool :=
  tr7RepOK j && tr7IndepOK ((tr7Bs (tr7ColsK j)).take 8) &&
    ((tr7Bs (tr7ColsK j)).take 8).all (· < 2 ^ 32) && decide (8 ≤ (tr7Bs (tr7ColsK j)).length) &&
    (if j == 2 || j == 6 then tr7ChainOK (tr7RepLines j) 1 && fB 1 (tr7Chain (tr7RepLines j) 1)
     else true)

@[expose] def tr7PairImg (p q : Nat × Nat) : Nat × Nat :=
  tr7PairK (sgl p.1 p.2 q.1) (sgl p.1 p.2 q.2)

@[expose] def tr7ImgChain (ps : List (Nat × Nat)) (q : Nat × Nat) : Nat × Nat :=
  ps.foldr (fun p acc => tr7PairImg (tr7PairK p.1 p.2) acc) q

@[expose] noncomputable def tr7ImgsOK : List (Nat × Nat) → Nat × Nat → Bool
  | [], q => tr7LineOK q
  | p :: ps, q => tr7ImgsOK ps q && tr7LineOK (tr7PairK p.1 p.2) &&
      tr7LineOK (tr7ImgChain (p :: ps) q)

@[expose] noncomputable def tr7ImgOK (ps : List (Nat × Nat)) (q : Nat × Nat) : Bool :=
  tr7ImgsOK ps q && tr7ImgChain ps q == q

@[expose] noncomputable def tr7MatOK (q : Nat × Nat) (bs M : List Nat) : Bool :=
  M.length == bs.length && (bs.zip M).all fun e =>
    decide (e.1 < 2 ^ 32) && id7VecOK q.1 q.2 e.1 && tr7XorSel bs e.2 == tr7Lift q e.1

@[expose] def tr7RedK (E : List Nat) (x : Nat) : Nat := E.foldl (fun x b => min x (x ^^^ b)) x

@[expose] def tr7Ins (r : Nat) : List Nat → List Nat
  | [] => [r]
  | b :: E => if b < r then r :: b :: E else b :: tr7Ins r E

@[expose] def tr7Add (E : List Nat) (v : Nat) : List Nat :=
  if tr7RedK E v = 0 then E else tr7Ins (tr7RedK E v) E

@[expose] def tr7CloseK (Ms : List (List Nat)) : Nat → List Nat → List Nat
  | 0, S => S
  | n + 1, S => tr7CloseK Ms n ((S.flatMap fun v => Ms.map fun M => tr7XorSel M v).foldl tr7Add S)

@[expose] def tr7J (a : Nat) : Nat := [0, 1, 3, 4, 5].getD a 0

@[expose] def tr7Dim (a : Nat) : Nat := [8, 12, 12, 16, 16].getD a 0

@[expose] noncomputable def tr7HeadK (a : Nat) : Bool :=
  tr7RepOK (tr7J a) && (tr7Bs (tr7ColsK (tr7J a))).length == tr7Dim a &&
    (tr7ColsK (tr7J a)).all (fun v => tr7Red (tr7Ech (tr7ColsK (tr7J a))) v == 0) &&
    (JTr.tr7M.getD a []).length == (tr7GenPairs (tr7J a)).length &&
    decide ((JTr.tr7M.getD a []).length ≤ 8) &&
    ((tr7GenPairs (tr7J a)).zip (JTr.tr7M.getD a [])).all (fun e =>
      tr7LineOK (tr7PairK e.1.1 e.1.2) && tr7ImgOK (tr7RepLines (tr7J a)) (tr7PairK e.1.1 e.1.2) &&
        tr7MatOK (tr7PairK e.1.1 e.1.2) (tr7Bs (tr7ColsK (tr7J a))) e.2) &&
    wtTree.memB (tr7Target (tr7J a)) &&
    tr7XorSel (tr7Bs (tr7ColsK (tr7J a))) (JTr.tr7T.getD a 0) == tr7Target (tr7J a) &&
    (JTr.tr7Reps.getD a []).all fun r =>
      tr7RedK (tr7CloseK (JTr.tr7M.getD a []) 4 [r]) (JTr.tr7T.getD a 0) == 0

@[expose] noncomputable def tr7SelK (bs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun b _ ih m => Nat.xor (nIf(Nat.beq (Nat.land m 1) 1, b, 0)) (ih (Nat.shiftRight m 1))) bs

@[expose] noncomputable def tr7MemK (x : Nat) (rs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun r _ ih => bIf(Nat.beq x r, true, ih)) rs

@[expose] noncomputable def tr7ForestOK (a d : Nat) : Bool :=
  pkTreeOK (2 ^ d) (2 ^ d / 64 + 1) 5 3 (JTr.tr7D.getD a 0) (JTr.tr7G.getD a 0) (Nat.blt 0)
    (fun x => tr7MemK x (JTr.tr7Reps.getD a [])) (fun g => Nat.blt g (JTr.tr7M.getD a []).length)
    (fun g y => tr7SelK ((JTr.tr7M.getD a []).getD g []) y)

end CFSG.KD.SmithD6

end
