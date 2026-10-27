module

public import Certificates.Data.CFSGNative.SectionRank.Local
public import Certificates.Data.CFSGNative.SectionRank.F2
public import Certificates.Data.CFSGNative.SectionRank.Fp
public import Certificates.Data.CFSGNative.SectionRank.F3

public section

namespace CFSG.SectionRank.Native

set_option compiler.extract_closed false

structure KeyFns (V : Type) where
  key : V → Nat
  base : Nat

@[expose] def kf2 (d : Nat) : KeyFns Nat where
  key v := v % 2 ^ d
  base := 2 ^ d

@[expose] def ofDigitsP (p : Nat) : List Nat → Nat
  | [] => 0
  | a :: l => a + p * ofDigitsP p l

@[expose] def kfP (p d : Nat) : KeyFns (Array Nat) where
  key v := ofDigitsP p ((List.range d).map fun j => v[j]! % p)
  base := p ^ d

@[expose] def kf3 (d : Nat) : KeyFns CFSG.F3.Native.V where
  key v := v.p % 2 ^ d + 2 ^ d * (v.m % 2 ^ d)
  base := 2 ^ d * 2 ^ d

structure Cover3Data (V : Type) where
  seedA : String
  seedB : String
  m : Nat
  nregs : Nat
  prog : List Op
  regs : List Nat
  ordv : List Nat
  ord : List Nat
  relCodes : List (List Nat)
  commCodes : List (List (List Nat × List Nat))
  starts : List V
  tree : String

@[expose] def treeAlphabet : String :=
  "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz+/"

@[expose] def treeDigits (s : String) : List Nat :=
  s.toList.map fun c => treeAlphabet.toList.idxOf c

@[expose] def treeOfDigits (m : Nat) (ds : List Nat) : Array Nat × Array Nat := Id.run do
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut p := 0
  for d in ds do
    for g in List.range m do
      if d / 2 ^ g % 2 = 1 then
        par := par.push p
        lab := lab.push g
    p := p + 1
  return (par, lab)

@[expose] def flipCode (c : Nat) : Nat := if c % 2 = 0 then c + 1 else c - 1

@[expose] def invRevCodes (w : List Nat) : List Nat := (w.map flipCode).reverse

@[expose] def commCode (u v : List Nat) : List Nat := u ++ v ++ invRevCodes u ++ invRevCodes v

@[expose] def commCodesWord (c : List (List Nat × List Nat)) : List Nat :=
  (c.map fun p => commCode p.1 p.2).flatten

@[expose] def Cover3Data.cw {V : Type} (D : Cover3Data V) (i : Nat) : List Nat :=
  if D.ord.getD i 0 = 0 then commCodesWord (D.commCodes.getD i []) else [2 * i]

section Check

variable {M V : Type} (O : Ops M V)

@[expose] def powN (X : M) (e : Nat) : M :=
  if e = 0 then O.one
  else if e = 1 then X
  else
    let Y := powN (O.mul X X) (e / 2)
    if e % 2 = 1 then O.mul X Y else Y
termination_by e
decreasing_by omega

@[expose] def opLtN (n : Nat) : Op → Bool
  | .mul i j k => decide (i < n) && decide (j < n) && decide (k < n)
  | .pow _ i k => decide (i < n) && decide (k < n)

@[expose] def stepN [Inhabited M] (R : Array M) : Op → Array M
  | .mul i j k => R.set! k (O.mul R[i]! R[j]!)
  | .pow e i k => R.set! k (powN O R[i]! e)

@[expose] def regsN [Inhabited M] (seedA seedB : String) (nregs : Nat) (prog : List Op) :
    Array M :=
  prog.foldl (stepN O)
    (Array.ofFn (n := nregs) fun r =>
      if r.val = 0 then O.decode seedA else if r.val = 1 then O.decode seedB else O.one)

@[expose] def evalCodes [Inhabited M] (gm gi : Array M) : List Nat → M
  | [] => O.one
  | c :: w => O.mul (if c % 2 = 0 then gm[c / 2 % gm.size]! else gi[c / 2 % gm.size]!)
      (evalCodes gm gi w)

@[expose] def stateKey (kf : KeyFns V) (st : List V) : Nat :=
  st.foldr (fun v acc => kf.key v + kf.base * acc) 0

@[expose] def orbStep [Inhabited M] (gens : Array M) (starts : List V) (par lab : Array Nat)
    (ws : Array (List V)) (i : Nat) : Array (List V) :=
  ws.push (if i = 0 then starts else (ws[par[i]!]!).map fun v => O.vmul v gens[lab[i]!]!)

@[expose] def orbStates [Inhabited M] (gens : Array M) (starts : List V) (par lab : Array Nat) (n : Nat) :
    Array (List V) :=
  (List.range n).foldl (orbStep O gens starts par lab) #[]

@[expose] def strictInc : List Nat → Bool
  | a :: b :: l => decide (a < b) && strictInc (b :: l)
  | _ => true

@[expose] def orbitOK [Inhabited M] (kf : KeyFns V) (gens : Array M) (starts : List V) (tree : Array Nat × Array Nat)
    (n : Nat) : Bool :=
  decide (0 < n) && (List.range n).all (fun i => decide (i = 0 ∨ tree.1[i]! < i)) &&
    (List.range n).all (fun i => decide (tree.2[i]! < gens.size)) &&
    strictInc (((orbStates O gens starts tree.1 tree.2 n).toList.map (stateKey kf)).mergeSort
      fun a b => decide (a ≤ b))

@[expose] def Cover3Data.gens [Inhabited M] (D : Cover3Data V) : Array M :=
  let R := regsN O D.seedA D.seedB D.nregs D.prog
  (List.range D.m).toArray.map fun i => R[D.regs.getD i 0]!

@[expose] def Cover3Data.ginvs [Inhabited M] (D : Cover3Data V) (gm : Array M) : Array M :=
  (List.range D.m).toArray.map fun i => powN O gm[i]! (D.ordv.getD i 1 - 1)

@[expose] def Cover3Data.check [Inhabited M] (kf : KeyFns V) (D : Cover3Data V)
    (n : Nat) : Bool :=
  let gm := D.gens O
  let gi := D.ginvs O gm
  decide (2 ≤ D.nregs) && D.prog.all (opLtN D.nregs) && decide (0 < D.m) &&
    (D.regs.all fun r => decide (r < D.nregs)) && decide (D.regs.length = D.m) &&
    (List.range D.m).all (fun i => decide (0 < D.ordv.getD i 0) &&
      O.eq (powN O gm[i]! (D.ordv.getD i 0)) O.one) &&
    D.relCodes.all (fun r => O.eq (evalCodes O gm gi r) O.one) &&
    (List.range D.m).all (fun i =>
      if D.ord.getD i 0 = 0 then O.eq (evalCodes O gm gi (D.cw i)) gm[i]!
      else decide (D.ord.getD i 0 = D.ordv.getD i 0) && decide (D.ord.getD i 0 % 3 ≠ 0)) &&
    orbitOK O kf gm D.starts (treeOfDigits D.m (treeDigits D.tree)) n

end Check

end CFSG.SectionRank.Native
