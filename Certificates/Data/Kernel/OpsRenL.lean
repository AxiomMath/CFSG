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

@[expose] noncomputable def renGetD (T : List (Option Nat)) (s : Nat) : Option Nat :=
  List.rec (motive := fun _ => Nat → Option Nat) (fun _ => none)
    (fun x _ ih s => Nat.rec (motive := fun _ => Option Nat) x (fun s' _ => ih s') s) T s

@[expose] noncomputable def renLen (T : List (Option Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) T

@[expose] noncomputable def renClr (T : List (Option Nat)) (k : Nat) : List (Option Nat) :=
  List.rec (motive := fun _ => List (Option Nat)) []
    (fun x _ ih => (bif isReg x k then none else x) :: ih) T

@[expose] noncomputable def renSetAt (T : List (Option Nat)) (t : Nat) (v : Option Nat) :
    List (Option Nat) :=
  List.rec (motive := fun _ => Nat → List (Option Nat)) (fun _ => [])
    (fun x xs ih t => Nat.rec (motive := fun _ => List (Option Nat)) (v :: xs)
      (fun t' _ => x :: ih t') t) T t

@[expose] noncomputable def renSet (T : List (Option Nat)) (k t : Nat) : List (Option Nat) :=
  renSetAt (renClr T k) t (some k)

@[expose] noncomputable def renStep (T : List (Option Nat)) : Op → Op → Option (List (Option Nat))
  | .mul i j k, .mul a b t =>
    bif isReg (renGetD T a) i && isReg (renGetD T b) j && decide (t < renLen T) then
      some (renSet T k t) else none
  | .pow e i k, .pow e' a t =>
    bif Nat.beq e e' && isReg (renGetD T a) i && decide (t < renLen T) then
      some (renSet T k t) else none
  | _, _ => none

@[expose] noncomputable def renChunk : List (Option Nat) → List Op → List (List Nat) →
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

@[expose] noncomputable def renRun (outs : List Nat) : List (Option Nat) → List Op → List RChunk → Bool
  | T, P, [] => P.isEmpty && tabEq T outs
  | T, P, (n, ls, out) :: cs =>
    decide (T.length ≤ n) &&
      match renChunk (T ++ List.replicate (n - T.length) none) P ls with
      | some (T', P') => renRun outs (out.map fun s => T'.getD s none) P' cs
      | none => false

@[expose] noncomputable def renOK (outs : List Nat) (P : List Op) (cs : List RChunk) : Bool :=
  renRun outs [some 0, some 1] P cs

@[expose] def padR (c : Lay) (S : List Nat) (n : Nat) : List Nat :=
  S ++ List.replicate (n - S.length) c.ONE

@[expose] noncomputable def chunkV (c : Lay) (ch : RChunk) (S S' : List Nat) : Bool :=
  runC c (ch.2.1.map opOf) (padR c S ch.1) fun R => eqL (ch.2.2.map (getR c R)) S'

end CFSG.KC.OpsLayK

end
