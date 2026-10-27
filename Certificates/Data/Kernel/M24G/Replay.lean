module

public import Certificates.Data.Kernel.ONanSmall.KTree

public section

namespace CFSG.KC.M24G

open CFSG.KC.ONanSmall

@[expose] def findK (k : Nat) : KTree (Nat × Nat) → Option Nat
  | .leaf => none
  | .node l x r => if k = x.1 then some x.2 else if k < x.1 then findK k l else findK k r

@[expose] def posTree {α : Type} (key : α → Nat) (L : List α) : KTree (Nat × Nat) :=
  KTree.ofList Prod.fst ((L.zipIdx).map fun e => (key e.1, e.2))

@[expose] def sizeK {β : Type} : KTree β → Nat
  | .leaf => 0
  | .node l _ r => sizeK l + 1 + sizeK r

@[expose] def posAll {α : Type} (key : α → Nat) (pos : KTree (Nat × Nat)) : List α → Nat → Bool
  | [], _ => true
  | x :: L, i => (findK (key x) pos == some i) && posAll key pos L (i + 1)

@[expose] def posOK {α : Type} (key : α → Nat) (L : List α) (pos : KTree (Nat × Nat)) : Bool :=
  sizeK pos == L.length && posAll key pos L 0

@[expose] def idxK (pos : KTree (Nat × Nat)) (n k : Nat) : Nat :=
  match findK k pos with
  | some q => q
  | none => n

@[expose] def replayStep {α : Type} [DecidableEq α] (key : α → Nat) (pos : KTree (Nat × Nat))
    (x : α) (h : Nat) :
    List (α → α) → Nat → List α → List Nat → List Nat → Nat →
      Option (List α × List Nat × List Nat × Nat)
  | [], _, nw, np, ng, sz => some (nw, np, ng, sz)
  | s :: ss, j, nw, np, ng, sz =>
    match findK (key (s x)) pos with
    | none => none
    | some i =>
      if i < sz then replayStep key pos x h ss (j + 1) nw np ng sz
      else if i = sz then
        match nw, np, ng with
        | y :: nw', p :: np', g :: ng' =>
          if y = s x ∧ p = h ∧ g = j then replayStep key pos x h ss (j + 1) nw' np' ng' (sz + 1)
          else none
        | _, _, _ => none
      else none

@[expose] def replayGo {α : Type} [DecidableEq α] (key : α → Nat) (steps : List (α → α))
    (pos : KTree (Nat × Nat)) :
    Nat → List α → Nat → List α → List Nat → List Nat → Nat → Bool
  | 0, _, _, nw, np, ng, _ => nw.isEmpty && np.isEmpty && ng.isEmpty
  | f + 1, hs, h, nw, np, ng, sz =>
    if h < sz then
      match hs with
      | [] => false
      | x :: hs' =>
        match replayStep key pos x h steps 0 nw np ng sz with
        | none => false
        | some (nw', np', ng', sz') => replayGo key steps pos f hs' (h + 1) nw' np' ng' sz'
    else nw.isEmpty && np.isEmpty && ng.isEmpty

@[expose] def replayOK {α : Type} [DecidableEq α] (key : α → Nat) (steps : List (α → α))
    (base : α) (fuel : Nat) (L : List α) (par gen : List Nat) (pos : KTree (Nat × Nat)) : Bool :=
  posOK key L pos &&
    match L, par, gen with
    | x :: nw, p :: np, g :: ng =>
      decide (x = base) && p == 0 && g == 0 && replayGo key steps pos fuel L 0 nw np ng 1
    | _, _, _ => false

end CFSG.KC.M24G
