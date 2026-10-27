module

public import Init

public section

namespace CFSG.KC.J4M4

@[expose] def eqL : List Nat → List Nat → Bool
  | [], [] => true
  | a :: l₁, b :: l₂ => Nat.beq a b && eqL l₁ l₂
  | _, _ => false

@[expose] def sortedB : List Nat → Bool
  | a :: b :: l => Nat.blt a b && sortedB (b :: l)
  | _ => true

@[expose] def mergeF : Nat → List Nat → List Nat → List Nat
  | 0, l₁, l₂ => l₁ ++ l₂
  | _ + 1, [], l₂ => l₂
  | _ + 1, a :: l₁, [] => a :: l₁
  | n + 1, a :: l₁, b :: l₂ =>
    bif Nat.ble a b then a :: mergeF n l₁ (b :: l₂) else b :: mergeF n (a :: l₁) l₂

@[expose] def splitA : List Nat → List Nat × List Nat
  | [] => ([], [])
  | a :: l => match splitA l with
    | (x, y) => (a :: y, x)

@[expose] def msortF : Nat → List Nat → List Nat
  | 0, l => l
  | _ + 1, [] => []
  | _ + 1, [a] => [a]
  | n + 1, a :: b :: l => match splitA (a :: b :: l) with
    | (x, y) => mergeF (l.length + 2) (msortF n x) (msortF n y)

@[expose] def msort (l : List Nat) : List Nat := msortF 20 l

@[expose] def subF : Nat → List Nat → List Nat → Bool
  | _, [], _ => true
  | 0, _ :: _, _ => false
  | _ + 1, _ :: _, [] => false
  | n + 1, a :: l₁, b :: l₂ =>
    bif Nat.beq a b then subF n l₁ (b :: l₂) else bif Nat.blt b a then subF n (a :: l₁) l₂ else false

@[expose] def layersOK (act : Nat → Nat → Nat) (ng : Nat) :
    List Nat → List (List (Nat × Nat × Nat)) → Bool
  | _, [] => true
  | B, ly :: rest =>
    ly.all (fun r => Nat.blt r.2.1 ng && Nat.beq (act r.2.1 r.2.2) r.1) &&
      subF (2 * ly.length + B.length + 1) (msort (ly.map fun r => r.2.2)) B &&
      layersOK act ng (msort (B ++ ly.map fun r => r.1)) rest

@[expose] def keysY (Y : List (List (Nat × Nat × Nat))) : List Nat :=
  Y.flatMap fun ly => ly.map fun r => r.1

@[expose] def certOK (act : Nat → Nat → Nat) (ng root : Nat) (L : List Nat)
    (Y : List (List (Nat × Nat × Nat))) : Bool :=
  Nat.ble Y.length 65 && sortedB L && eqL (msort (keysY Y)) L &&
    match Y with
    | [] => false
    | y₀ :: rest => eqL (y₀.map fun r => r.1) [root] && layersOK act ng [root] rest

@[expose] def layerOK (act : Nat → Nat → Nat) (ng : Nat) (B : List Nat)
    (ly : List (Nat × Nat × Nat)) : Bool :=
  ly.all (fun r => Nat.blt r.2.1 ng && Nat.beq (act r.2.1 r.2.2) r.1) &&
    subF (2 * ly.length + B.length + 1) (msort (ly.map fun r => r.2.2)) B

@[expose] def certHead (root : Nat) (L : List Nat) (Y : List (List (Nat × Nat × Nat))) : Bool :=
  Nat.ble Y.length 65 && sortedB L && eqL (msort (keysY Y)) L &&
    eqL ((Y.getD 0 []).map fun r => r.1) [root]

@[expose] def closeOK (act : Nat → Nat → Nat) (ng : Nat) (L : List Nat) : Bool :=
  (List.range ng).all fun s => eqL (msort (L.map (act s))) L

end CFSG.KC.J4M4
