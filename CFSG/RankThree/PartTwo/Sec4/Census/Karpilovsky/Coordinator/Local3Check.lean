module

public import Certificates.Data.CFSGNative.SectionRank.Elem3

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.SectionRank.Native

structure Local3Data (m : Nat) where
  seedA : String
  seedB : String
  oA : Nat
  oB : Nat
  defs : List (List Nat)
  gens : List (List Nat)
  ords : List Nat
  rels : List (List (Fin m × Bool))
  masks : String
  n : Nat

@[expose] def ofCodes (m : Nat) [NeZero m] (c : List Nat) : List (Fin m × Bool) :=
  c.map (fun x =>
    (⟨x / 2 % m, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))⟩, decide (x % 2 = 0)))

section Native

variable {M V : Type} [Inhabited M] (O : Ops M V)

@[expose] def evalLetters (L : Array M) : List Nat → M
  | [] => O.one
  | c :: w => O.mul L[c]! (evalLetters L w)

@[expose] def evalGen {m : Nat} (G Gi : Array M) : List (Fin m × Bool) → M
  | [] => O.one
  | (i, true) :: w => O.mul G[i.val]! (evalGen G Gi w)
  | (i, false) :: w => O.mul Gi[i.val]! (evalGen G Gi w)

@[expose] def seedLetters (A B : M) (oA oB : Nat) : Array M :=
  #[A, O.pow A (oA - 1), B, O.pow B (oB - 1)]

@[expose] def invCodes (w : List Nat) : List Nat := w.reverse.map (· ^^^ 1)

@[expose] def extendLetters (L : Array M) : List (List Nat) → Array M
  | [] => L
  | w :: ws => extendLetters ((L.push (evalLetters O L w)).push (evalLetters O L (invCodes w))) ws

@[expose] def defsOK : Nat → List (List Nat) → Bool
  | _, [] => true
  | n, w :: ws => w.all (fun c => decide (c < n)) && defsOK (n + 2) ws

@[expose] def treeOfMask (m : Nat) (ds : List Nat) : Array Nat × Array Nat :=
  (List.range ds.length).foldl (fun (acc : Array Nat × Array Nat) p =>
    (List.range m).foldl (fun (acc : Array Nat × Array Nat) g =>
      if ds[p]! / 2 ^ g % 2 = 1 then (acc.1.push p, acc.2.push g) else acc) acc) (#[0], #[0])

@[expose] def orbStep [Inhabited V] (gens : Array M) (w0 : V) (par lab : Array Nat)
    (ws : Array V) (i : Nat) : Array V :=
  ws.push (if i = 0 then w0 else O.vmul ws[par[i]!]! gens[lab[i]!]!)

@[expose] def orbVecs [Inhabited V] (gens : Array M) (w0 : V) (par lab : Array Nat) (n : Nat) :
    Array V :=
  (List.range n).foldl (orbStep O gens w0 par lab) #[]

@[expose] def strictInc : List Nat → Bool
  | a :: b :: l => decide (a < b) && strictInc (b :: l)
  | _ => true

@[expose] def orbitOK [Inhabited V] (key : V → Nat) (gens : Array M) (w0 : V) (par lab : Array Nat)
    (n : Nat) : Bool :=
  decide (0 < n) && (List.range n).all (fun i => decide (i = 0 ∨ par[i]! < i)) &&
    (List.range n).all (fun i => decide (lab[i]! < gens.size)) &&
    strictInc (((orbVecs O gens w0 par lab n).toList.map key).mergeSort fun a b => decide (a ≤ b))

@[expose] def local3Check [Inhabited V] (key : V → Nat) {m : Nat} (D : Local3Data m) (root : V) :
    Bool :=
  let A := O.decode D.seedA
  let B := O.decode D.seedB
  let L := extendLetters O (seedLetters O A B D.oA D.oB) D.defs
  let G : Array M := (D.gens.map (evalLetters O L)).toArray
  let Gi : Array M := (List.range m).toArray.map fun i => O.pow G[i]! (D.ords.getD i 0 - 1)
  let tree := treeOfMask m (D.masks.toList.map fun c => c.toNat - 48)
  decide (D.gens.length = m) && defsOK 4 D.defs &&
    D.gens.all (fun w => w.all fun c => decide (c < 4 + 2 * D.defs.length)) &&
    (List.range m).all (fun i => decide (D.ords.getD i 0 ≠ 0) &&
      decide (Nat.gcd (D.ords.getD i 0) 3 = 1) && O.eq (O.pow G[i]! (D.ords.getD i 0)) O.one) &&
    D.rels.all (fun r => O.eq (evalGen O G Gi r) O.one) &&
    orbitOK O key G root tree.1 tree.2 D.n

end Native

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
