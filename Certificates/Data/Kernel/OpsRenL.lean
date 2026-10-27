module

public import Certificates.Data.Kernel.OpsLayMcert

public section

namespace CFSG.KC.OpsLayK

open CFSG.KC.LQT CFSG.SectionRank.Native

abbrev RChunk := Nat × List (List Nat) × List Nat

@[expose] def opOf : List Nat → Op
  | [0, i, j, k] => .mul i j k
  | [e + 1, i, _, k] => .pow (e + 1) i k
  | _ => .mul 0 0 0

@[expose] def isReg : Option Nat → Nat → Bool
  | some x, r => Nat.beq x r
  | none, _ => false

@[expose] def renSet (T : List (Option Nat)) (k t : Nat) : List (Option Nat) :=
  (T.map fun x => bif isReg x k then none else x).set t (some k)

@[expose] def renStep (T : List (Option Nat)) : Op → Op → Option (List (Option Nat))
  | .mul i j k, .mul a b t =>
    bif isReg (T.getD a none) i && isReg (T.getD b none) j && decide (t < T.length) then
      some (renSet T k t) else none
  | .pow e i k, .pow e' a t =>
    bif Nat.beq e e' && isReg (T.getD a none) i && decide (t < T.length) then
      some (renSet T k t) else none
  | _, _ => none

@[expose] def renChunk : List (Option Nat) → List Op → List (List Nat) →
    Option (List (Option Nat) × List Op)
  | T, P, [] => some (T, P)
  | T, o :: P, l :: ls =>
    match renStep T o (opOf l) with
    | some T' => renChunk T' P ls
    | none => none
  | _, [], _ :: _ => none

@[expose] def tabEq : List (Option Nat) → List Nat → Bool
  | [], [] => true
  | x :: T, r :: rs => isReg x r && tabEq T rs
  | _, _ => false

@[expose] def renRun (outs : List Nat) : List (Option Nat) → List Op → List RChunk → Bool
  | T, P, [] => P.isEmpty && tabEq T outs
  | T, P, (n, ls, out) :: cs =>
    decide (T.length ≤ n) &&
      match renChunk (T ++ List.replicate (n - T.length) none) P ls with
      | some (T', P') => renRun outs (out.map fun s => T'.getD s none) P' cs
      | none => false

@[expose] def renOK (outs : List Nat) (P : List Op) (cs : List RChunk) : Bool :=
  renRun outs [some 0, some 1] P cs

@[expose] def padR (c : Lay) (S : List Nat) (n : Nat) : List Nat :=
  S ++ List.replicate (n - S.length) c.ONE

@[expose] noncomputable def chunkV (c : Lay) (ch : RChunk) (S S' : List Nat) : Bool :=
  runC c (ch.2.1.map opOf) (padR c S ch.1) fun R => eqL (ch.2.2.map (getR c R)) S'

end CFSG.KC.OpsLayK

end
