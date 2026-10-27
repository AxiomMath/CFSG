module

public import Certificates.Data.YamakiPres
public import Std.Data.HashMap

public section

namespace CFSG.ClassicalInvolution.Solomon73.Yamaki

open Matrix

@[expose] def codeOf (v : Fin 3 ⊕ Fin 3 → ZMod 2) : ℕ :=
  (v (.inl 0)).val + 2 * (v (.inl 1)).val + 4 * (v (.inl 2)).val + 8 * (v (.inr 0)).val +
    16 * (v (.inr 1)).val + 32 * (v (.inr 2)).val

@[expose] def matArr (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) : Array ℕ :=
  Array.ofFn (n := 64) fun n => codeOf (A *ᵥ vecOf n.val)

@[expose] def genA (_ : Unit := ()) : Array (Array ℕ) :=
  Array.ofFn (n := 12) fun i => matArr (yamakiMat i)

@[inline, expose] def allLt (n : ℕ) (p : ℕ → Bool) : Bool := Nat.all n fun i _ => p i

@[expose] def compA (t u : Array ℕ) : Array ℕ := Array.ofFn (n := 64) fun i => t[u[i.val]!]!

@[expose] def idA (_ : Unit := ()) : Array ℕ := Array.ofFn (n := 64) fun i => i.val

@[expose] def wordA (gs : Array (Array ℕ)) : List ℕ → Array ℕ
  | [] => idA ()
  | i :: w => compA gs[i]! (wordA gs w)

structure Enum where
  elems : Array (Array ℕ)
  parent : Array ℕ
  gen : Array ℕ
  index : Std.HashMap (Array ℕ) ℕ

@[expose] def bfsStep (gs : Array (Array ℕ)) (E : Enum) (q : ℕ) : Enum := Id.run do
  let x := E.elems[q]!
  let mut E := E
  for j in [0:gs.size] do
    let y := compA x gs[j]!
    if !E.index.contains y then
      let n := E.elems.size
      E := ⟨E.elems.push y, E.parent.push q, E.gen.push j, E.index.insert y n⟩
  return E

@[expose] def bfsEnum (gs : Array (Array ℕ)) (fuel : ℕ) : Enum := Id.run do
  let one := idA ()
  let mut E : Enum := ⟨#[one], #[0], #[0], ({} : Std.HashMap (Array ℕ) ℕ).insert one 0⟩
  for q in [0:fuel] do
    if q < E.elems.size then
      E := bfsStep gs E q
  return E

@[expose] def Enum.lookup (E : Enum) (t : Array ℕ) : Option ℕ :=
  match E.index[t]? with
  | some k => if k < E.elems.size ∧ E.elems[k]! = t then some k else none
  | none => none

@[expose] def treeOK (E : Enum) (gs : Array (Array ℕ)) : Bool :=
  decide (E.elems[0]? = some (idA ())) &&
    allLt E.elems.size fun i => decide (i = 0) ||
      (decide (E.parent[i]! < i) && decide (E.gen[i]! < gs.size) &&
        decide (E.elems[i]! = compA E.elems[E.parent[i]!]! gs[E.gen[i]!]!))

@[expose] def closedOK (E : Enum) (gs : Array (Array ℕ)) : Bool :=
  allLt E.elems.size fun i => allLt gs.size fun j => (E.lookup (compA E.elems[i]! gs[j]!)).isSome

@[expose] def nodupOK (E : Enum) : Bool :=
  allLt E.elems.size fun i => decide (E.lookup E.elems[i]! = some i)

@[expose] def enumOK (E : Enum) (gs : Array (Array ℕ)) : Bool :=
  treeOK E gs && closedOK E gs && nodupOK E

@[expose] def buildF (E : Enum) (hs : Array (Array ℕ)) : Array (Array ℕ) := Id.run do
  let mut F : Array (Array ℕ) := #[idA ()]
  for i in [1:E.elems.size] do
    F := F.push (compA F[E.parent[i]!]! hs[E.gen[i]!]!)
  return F

@[expose] def firstIndex (F : Array (Array ℕ)) : Std.HashMap (Array ℕ) ℕ :=
  (F.foldl (init := (({} : Std.HashMap (Array ℕ) ℕ), 0)) fun acc t =>
    (if acc.1.contains t then acc.1 else acc.1.insert t acc.2, acc.2 + 1)).1

@[expose] def injOK (F : Array (Array ℕ)) : Bool :=
  let m := firstIndex F
  allLt F.size fun i => decide (m[F[i]!]? = some i)

@[expose] def autOK (E : Enum) (gs hs F : Array (Array ℕ)) : Bool :=
  decide (F.size = E.elems.size) && decide (F[0]? = some (idA ())) &&
    (allLt E.elems.size fun i => decide (i = 0) ||
      decide (F[i]! = compA F[E.parent[i]!]! hs[E.gen[i]!]!)) &&
    (allLt E.elems.size fun i => allLt gs.size fun j =>
      match E.lookup (compA E.elems[i]! gs[j]!) with
      | some k => decide (F[k]! = compA F[i]! hs[j]!)
      | none => false) &&
    injOK F

@[expose] def appF (E : Enum) (F : Array (Array ℕ)) (t : Array ℕ) : Array ℕ :=
  F[(E.lookup t).getD 0]!

end CFSG.ClassicalInvolution.Solomon73.Yamaki
