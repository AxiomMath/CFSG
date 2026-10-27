module

public import Certificates.Data.CFSGNative.AS91.M24Syl

public section

set_option compiler.extract_closed false

namespace CFSG.Quasithin.H13.AS91.M24G.Native

@[expose] def kzeroId : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

@[expose] def kzeroMul (a b : Array Nat) : Array Nat := (Array.range 24).map fun i => a[b[i]!]!

@[expose] def kzeroKey (t : Array Nat) : Nat :=
  (List.range 24).foldl (fun acc i => (acc <<< 5) ||| t[i]!) 0

@[expose] def kzeroValid (t : Array Nat) : Bool := t.size == 24

@[expose] def kzeroUInv : List (Array Nat) :=
  [#[23, 21, 22, 20, 8, 9, 11, 10, 16, 19, 18, 17, 6, 7, 5, 4, 1, 3, 0, 2, 15, 12, 13, 14],
    #[7, 4, 5, 6, 12, 15, 14, 13, 20, 22, 21, 23, 17, 16, 18, 19, 9, 10, 11, 8, 2, 1, 0, 3],
    #[11, 10, 9, 8, 1, 0, 3, 2, 21, 22, 20, 23, 16, 18, 19, 17, 14, 15, 12, 13, 4, 5, 6, 7],
    #[0, 2, 1, 3, 10, 8, 11, 9, 16, 19, 18, 17, 21, 20, 22, 23, 5, 7, 4, 6, 15, 13, 14, 12]]

@[expose] def kzeroHs (_ : Unit := ()) : List (Array Nat × Array Nat) :=
  uTabs.zip kzeroUInv ++ kzeroUInv.zip uTabs

@[expose] def kzeroConj (p : Array Nat × Array Nat) (x : Array Nat) : Array Nat :=
  kzeroMul p.1 (kzeroMul x p.2)

@[expose] def kzeroSyl (_ : Unit := ()) : Array (Array Nat) × Array Nat × Array Nat :=
  bfs kzeroKey (s0Tabs.map kzeroMul) kzeroId 1100

@[expose] def kzeroK0 (S : Array (Array Nat)) (p : Array Nat × Array Nat) : List (Array Nat) :=
  S.toList.filter fun t => S.contains (kzeroConj p t)

@[expose] def kzeroK0List (_ : Unit := ()) : List (Array Nat) :=
  kzeroK0 (kzeroSyl ()).1 ((kzeroHs ()).getD 4 (#[], #[]))

structure KzEntry where
  tab : Array Nat
  kind : Nat
  a : Nat
  b : Nat
  deriving Inhabited

@[expose] def kzeroClose (hs : List (Array Nat × Array Nat)) (k : Array Nat) : Array KzEntry :=
  Id.run do
    let mut D : Array KzEntry := #[⟨k, 0, 0, 0⟩]
    let mut seen : Std.HashMap Nat Nat := (∅ : Std.HashMap Nat Nat).insert (kzeroKey k) 0
    let mut h := 0
    for _ in [0:200] do
      if h < D.size then
        let x := D[h]!.tab
        let mut j := 0
        for p in hs do
          let y := kzeroConj p x
          if !(seen.contains (kzeroKey y)) then
            seen := seen.insert (kzeroKey y) D.size
            D := D.push ⟨y, 1, j, h⟩
          j := j + 1
        h := h + 1
      else
        break
    let m := D.size
    let one := kzeroMul k k
    let mut S : Array Nat := #[]
    match seen[kzeroKey one]? with
    | some idx => S := S.push idx
    | none =>
      seen := seen.insert (kzeroKey one) D.size
      S := S.push D.size
      D := D.push ⟨one, 2, 0, 0⟩
    for i in [0:m] do
      if !(S.contains i) then
        let Sold := S
        for s in Sold do
          let y := kzeroMul D[s]!.tab D[i]!.tab
          match seen[kzeroKey y]? with
          | some idx => if !(S.contains idx) then S := S.push idx
          | none =>
            seen := seen.insert (kzeroKey y) D.size
            S := S.push D.size
            D := D.push ⟨y, 2, s, i⟩
    return D

@[expose] def kzeroDerivValid (hs : List (Array Nat × Array Nat)) (k : Array Nat)
    (D : Array KzEntry) : Bool :=
  decide (0 < D.size) && D[0]!.tab == k &&
    allLt D.size fun j => j == 0 ||
      (D[j]!.kind == 1 && decide (D[j]!.a < hs.length) && decide (D[j]!.b < j) &&
        D[j]!.tab == kzeroConj (hs.getD D[j]!.a (#[], #[])) D[D[j]!.b]!.tab) ||
      (D[j]!.kind == 2 && decide (D[j]!.a < j) && decide (D[j]!.b < j) &&
        D[j]!.tab == kzeroMul D[D[j]!.a]!.tab D[D[j]!.b]!.tab)

@[expose] def kzeroDerivOK (hs : List (Array Nat × Array Nat)) (K : List (Array Nat))
    (k : Array Nat) : Bool :=
  let D := kzeroClose hs k
  kzeroDerivValid hs k D && K.all fun x => (List.range D.size).any fun j => D[j]!.tab == x

@[expose] def kzeroUFix (_ : Unit := ()) : Bool :=
  uTabs.all fun g => imgSext g baseSext == baseSext

@[expose] def kzeroCheckOf (r : Array (Array Nat) × Array Nat × Array Nat) : Bool :=
  treeValid kzeroValid (s0Tabs.map kzeroMul) kzeroId r && decide (r.1.size = 1024) &&
    decide (r.1.toList.map kzeroKey).Nodup && kzeroUFix () &&
    (let hs := kzeroHs ()
     let K := kzeroK0 r.1 (hs.getD 4 (#[], #[]))
     decide (K.length = 64) && K.all fun k => k == kzeroId || kzeroDerivOK hs K k)

@[expose] def kzeroCheck (_ : Unit := ()) : Bool := kzeroCheckOf (kzeroSyl ())

end CFSG.Quasithin.H13.AS91.M24G.Native
