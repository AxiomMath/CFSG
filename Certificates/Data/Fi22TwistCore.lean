module

public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Std.Data.HashMap

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative

open CFSG.Monster.B.Co2.Native

set_option compiler.extract_closed false

@[expose] def relImgN (base : Array Nat) (i : Nat) (acc : Array Nat) (q m : Nat) : Nat :=
  if m < i then acc[base[m]!]! else acc[q]!

@[expose] def relOKDN (base : Array Nat) (ys : Array (Array Nat)) (rels : List (Nat × Nat × Nat))
    (i : Nat) (acc : Array Nat) (q : Nat) : Bool :=
  rels.all fun r => !(decide (max r.1 r.2.1 = i)) ||
    relImgN base i acc q r.2.1 == (ys[r.2.2]!)[relImgN base i acc q r.1]!

@[expose] def commAtN (n : Nat) (p x : Array Nat) : Bool := allLt n fun i => p[x[i]!]! == x[p[i]!]!

@[expose] def ptailN (n : Nat) (L : Array Level) (base : Array Nat) (gs ys : Array (Array Nat))
    (rels : List (Nat × Nat × Nat)) (mem : Array Nat → Bool) : Nat → Nat → Array Nat → Bool
  | 0, _, acc => !(gs.all (commAtN n acc)) || mem acc
  | fuel + 1, i, acc => allLt (L[i]!).pts.size fun k =>
      !(relOKDN base ys rels i acc (L[i]!).pts[k]!) ||
        ptailN n L base gs ys rels mem fuel (i + 1) (compA n acc (L[i]!).tr[k]!)

@[inline, expose] def apO (t : Option (Array Nat)) (p : Nat) : Nat :=
  match t with
  | none => p
  | some a => a[p]!

@[expose] def keys27 (n : Nat) (bs : List Nat) (x x2 y y2 z z2 : Array Nat) : List Nat :=
  ([none, some x, some x2].flatMap fun a => [none, some y, some y2].flatMap fun b =>
    [none, some z, some z2].map fun c =>
      bs.foldl (fun acc p => acc * n + apO a (apO b (apO c p))) 0).mergeSort
    (fun u v => decide (u ≤ v))

@[inline, expose] def conjAtN (n : Nat) (g x d : Array Nat) : Bool :=
  allLt n fun p => g[x[p]!]! == d[g[p]!]!

@[expose] def ord3N (n : Nat) (a : Array Nat) : Bool :=
  eqA n (compA n a (compA n a a)) (idA n) && !(eqA n a (idA n))

@[expose] def inNine (n : Nat) (x x2 y y2 z : Array Nat) : Bool :=
  [none, some x, some x2].any fun a => [none, some y, some y2].any fun b =>
    allLt n fun p => z[p]! == apO a (apO b p)

@[expose] def conjTab (n : Nat) (S G : Array (Array Nat)) (R : Array (List (Array Nat)))
    (repOf : Array Nat) : Array (Array Bool) :=
  (Array.range G.size).map fun c => S.map fun s => (R[repOf[c]!]!).any (conjAtN n G[c]! s)

@[expose] def commTab (n : Nat) (S : Array (Array Nat)) : Array (Array Bool) :=
  S.map fun a => S.map fun b => commAtN n a b

@[expose] def recOK3 (n : Nat) (bs : List Nat) (recs : Std.HashMap (List Nat) Nat)
    (cj : Array (Array Bool)) (i j l : Nat) (x x2 y y2 z z2 : Array Nat) : Bool :=
  match recs.get? (keys27 n bs x x2 y y2 z z2) with
  | none => false
  | some c => (cj[c]!)[i]! && (cj[c]!)[j]! && (cj[c]!)[l]!

@[expose] def tripZ (n : Nat) (bs : List Nat) (recs : Std.HashMap (List Nat) Nat)
    (cj cm : Array (Array Bool)) (S sq : Array (Array Nat)) (o3 : Array Bool) (i j : Nat) : Bool :=
  allLt S.size fun l => !o3[l]! || !(cm[i]!)[l]! || !(cm[j]!)[l]! ||
    inNine n S[i]! sq[i]! S[j]! sq[j]! S[l]! ||
    recOK3 n bs recs cj i j l S[i]! sq[i]! S[j]! sq[j]! S[l]! sq[l]!

@[expose] def triplesOK (n : Nat) (bs : List Nat) (S G : Array (Array Nat))
    (R : Array (List (Array Nat))) (repOf : Array Nat) (dRecs : List (List Nat × Nat)) : Bool :=
  let o3 := S.map (ord3N n)
  let sq := S.map fun a => compA n a a
  let cm := commTab n S
  let cj := conjTab n S G R repOf
  let recs : Std.HashMap (List Nat) Nat := dRecs.foldl (fun m r => m.insert r.1 r.2) {}
  allLt S.size fun i => !o3[i]! || allLt S.size fun j => !o3[j]! || !(cm[i]!)[j]! ||
    eqA n S[j]! S[i]! || eqA n S[j]! sq[i]! || tripZ n bs recs cj cm S sq o3 i j

end CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative
