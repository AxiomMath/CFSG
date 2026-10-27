module

public import Std.Data.HashMap
public import Std.Data.HashSet

public section

namespace Certificates.TcRes

set_option compiler.extract_closed false

@[expose] def tcrCartanE6 : Array Int :=
  #[2, 0, -1, 0, 0, 0, 0, 2, 0, -1, 0, 0, -1, 0, 2, -1, 0, 0, 0, -1, -1, 2, -1, 0, 0, 0, 0, -1,
    2, -1, 0, 0, 0, 0, -1, 2]

@[expose] def tcrCartanE8 : Array Int :=
  #[2, 0, -1, 0, 0, 0, 0, 0, 0, 2, 0, -1, 0, 0, 0, 0, -1, 0, 2, -1, 0, 0, 0, 0, 0, -1, -1, 2, -1,
    0, 0, 0, 0, 0, 0, -1, 2, -1, 0, 0, 0, 0, 0, 0, -1, 2, -1, 0, 0, 0, 0, 0, 0, -1, 2, -1, 0, 0,
    0, 0, 0, 0, -1, 2]

@[expose] def tcrReflV (cartan : Array Int) (rank i : Nat) (v : List Int) : List Int :=
  let k := (List.range rank).foldl (fun s j => s + cartan[rank * i + j]! * v.getD j 0) 0
  v.mapIdx fun m x => if m = i then x - k else x

@[expose] def tcrBasisV (rank i : Nat) : List Int :=
  (List.range rank).map fun m => if m = i then 1 else 0

@[expose] def tcrAddRoots (cartan : Array Int) (rank : Nat) (rs : List (List Int)) :
    List (List Int) :=
  (List.range rank).foldl (fun acc i =>
    rs.foldl (fun acc g =>
      let h := tcrReflV cartan rank i g
      if acc.contains h then acc else acc ++ [h]) acc) rs

@[expose] def tcrRootsOf (cartan : Array Int) (rank fuel : Nat) : List (List Int) :=
  (List.range fuel).foldl (fun rs _ => tcrAddRoots cartan rank rs)
    ((List.range rank).map (tcrBasisV rank))

@[expose] def tcrFormL (cartan : Array Int) (rank : Nat) (u v : List Int) : Int :=
  (List.range rank).foldl (fun s i =>
    s + u.getD i 0 *
      (List.range rank).foldl (fun t j => t + cartan[rank * i + j]! * v.getD j 0) 0) 0

@[expose] def tcrVsubmul (u : List Int) (c : Int) (v : List Int) : List Int :=
  List.zipWith (fun a b => a - c * b) u v

structure TcrSys where
  rank : Nat
  cartan : Array Int
  roots : Array (List Int)
  ip : Array (Array Int)
  neg : Array Nat
  refl : Array (Array Nat)
  basis : Array Nat
  posFlag : Array Bool
  adj : Array (List Nat)
  par : Array (Nat × Nat)
  idx : Std.HashMap (List Int) Nat

@[expose] def TcrSys.tcrN (S : TcrSys) : Nat := S.roots.size

@[expose] def tcrMkSys (cartan : Array Int) (rank fuel : Nat) : TcrSys :=
  let rs := (tcrRootsOf cartan rank fuel).toArray
  let n := rs.size
  let idx : Std.HashMap (List Int) Nat :=
    Std.HashMap.ofList ((List.range n).map fun i => (rs[i]!, i))
  let look : List Int → Nat := fun v => idx.getD v 0
  let ip : Array (Array Int) := Array.ofFn (n := n) fun i => Array.ofFn (n := n) fun j =>
    tcrFormL cartan rank rs[i]! rs[j]!
  let basis : Array Nat := Array.ofFn (n := rank) fun j => look (tcrBasisV rank j)
  let refl : Array (Array Nat) := Array.ofFn (n := n) fun g => Array.ofFn (n := n) fun v =>
    look (tcrVsubmul rs[v]! ip[v]![g]! rs[g]!)
  { rank := rank
    cartan := cartan
    roots := rs
    ip := ip
    neg := Array.ofFn (n := n) fun i => look (rs[i]!.map (fun x => - x))
    refl := refl
    basis := basis
    posFlag := Array.ofFn (n := n) fun i => rs[i]!.all (fun x => decide (0 ≤ x))
    adj := Array.ofFn (n := n) fun i => (List.range n).filter fun j => ip[i]![j]! != 0
    par := Array.ofFn (n := n) fun i =>
      if i.val < rank then (0, 0) else
        ((List.range i.val).findSome? fun i' => (List.range rank).findSome? fun k =>
          if refl[basis[k]!]![i']! == i.val then some (i', k) else none).getD (0, 0)
    idx := idx }

@[expose] def TcrSys.tcrOk (S : TcrSys) : Bool :=
  let rl := S.roots.toList
  (List.range S.rank).all (fun j => rl.contains (tcrBasisV S.rank j)) &&
  rl.all (fun r => (List.range S.rank).all fun i => rl.contains (tcrReflV S.cartan S.rank i r)) &&
  (List.range S.tcrN).all (fun i => (List.range S.tcrN).all fun j =>
    i == j || S.roots[i]! != S.roots[j]!) &&
  S.ip.size == S.tcrN && S.neg.size == S.tcrN && S.refl.size == S.tcrN && S.basis.size == S.rank &&
  S.posFlag.size == S.tcrN && S.adj.size == S.tcrN && S.par.size == S.tcrN &&
  (List.range S.tcrN).all (fun i => S.ip[i]!.size == S.tcrN && (List.range S.tcrN).all fun j =>
    S.ip[i]![j]! == tcrFormL S.cartan S.rank S.roots[i]! S.roots[j]!) &&
  (List.range S.tcrN).all (fun i => S.neg[i]! < S.tcrN &&
    S.roots[S.neg[i]!]! == S.roots[i]!.map (fun x => - x)) &&
  (List.range S.tcrN).all (fun g => S.refl[g]!.size == S.tcrN && (List.range S.tcrN).all fun v =>
    S.refl[g]![v]! < S.tcrN &&
      S.roots[S.refl[g]![v]!]! == tcrVsubmul S.roots[v]! S.ip[v]![g]! S.roots[g]!) &&
  (List.range S.rank).all (fun j => S.basis[j]! == j && S.roots[j]! == tcrBasisV S.rank j) &&
  (List.range S.tcrN).all (fun i => S.posFlag[i]! == S.roots[i]!.all (fun x => decide (0 ≤ x))) &&
  (List.range S.tcrN).all (fun i =>
    S.adj[i]! == (List.range S.tcrN).filter fun j => S.ip[i]![j]! != 0) &&
  (List.range S.tcrN).all (fun i => i < S.rank ||
    (S.par[i]!.1 < i && S.par[i]!.2 < S.rank &&
      S.refl[S.basis[S.par[i]!.2]!]![S.par[i]!.1]! == i))

@[expose] def tcrE6Sys (_ : Unit := ()) : TcrSys := tcrMkSys tcrCartanE6 6 12

@[expose] def tcrE8Sys (_ : Unit := ()) : TcrSys := tcrMkSys tcrCartanE8 8 30

@[expose] def tcrExtendTuples (S : TcrSys) (k : Nat) (pre : List Nat) : List (List Nat) :=
  (List.range S.tcrN).filterMap fun i =>
    if (List.range k).all (fun a => S.ip[i]![pre.getD a 0]! == S.cartan[k * S.rank + a]!) &&
        S.ip[i]![i]! == 2 then some (pre ++ [i]) else none

@[expose] def tcrAutTuples (S : TcrSys) : List (List Nat) :=
  (List.range S.rank).foldl (fun acc k => acc.flatMap (tcrExtendTuples S k)) [[]]

@[expose] def tcrLincomb (rank : Nat) (cs : List Int) (vs : List (List Int)) : List Int :=
  (List.zipWith (fun c v => v.map (fun x => c * x)) cs vs).foldl (List.zipWith (· + ·))
    (List.replicate rank 0)

@[expose] def tcrRbar6 : List Int := [1, 0, 2, 0, 1, 2]

@[expose] def tcrInCoset (S : TcrSys) (rbar : List Int) (ε : Int) (t : List Nat) : Bool :=
  let s := tcrLincomb S.rank rbar (t.map fun i => S.roots[i]!)
  (List.zipWith (fun a b => (a - ε * b) % 3 == 0) s rbar).all id

@[expose] def tcrAutE6 (S : TcrSys) (ε : Int) : List (List Nat) :=
  (tcrAutTuples S).filter (tcrInCoset S tcrRbar6 ε)

@[expose] def tcrExtendSkew (S : TcrSys) (k : Nat) (pre : List Nat) : List (List Nat) :=
  (List.range S.tcrN).filterMap fun i =>
    if (List.range k).all (fun a => S.ip[i]![pre.getD a 0]! == S.cartan[k * S.rank + a]!) &&
        S.ip[i]![i]! == 2 && S.ip[i]![S.basis[k]!]! == 0 &&
        (List.range k).all (fun a =>
          S.ip[i]![S.basis[a]!]! + S.ip[S.basis[k]!]![pre.getD a 0]! == 0)
      then some (pre ++ [i]) else none

@[expose] def tcrAutSkew (S : TcrSys) : List (List Nat) :=
  (List.range S.rank).foldl (fun acc k => acc.flatMap (tcrExtendSkew S k)) [[]]

@[expose] def tcrPermOf (S : TcrSys) (t : List Nat) : Array Nat :=
  let p0 : Array Nat := (List.range S.rank).foldl
    (fun a j => a.set! S.basis[j]! (t.getD j 0)) (Array.replicate S.tcrN 0)
  (List.range S.tcrN).foldl (fun a i =>
    if i < S.rank then a
    else a.set! i (S.refl[t.getD S.par[i]!.2 0]![a[S.par[i]!.1]!]!)) p0

@[expose] def tcrPermPow (S : TcrSys) (perm : Array Nat) : Nat → Array Nat
  | 0 => Array.ofFn (n := S.tcrN) fun i => i.val
  | e + 1 => let q := tcrPermPow S perm e
      Array.ofFn (n := S.tcrN) fun i => perm[q[i.val]!]!

@[expose] def tcrMaskOf (n : Nat) (l : List Nat) : Array Bool :=
  l.foldl (fun a i => a.set! i true) (Array.replicate n false)

@[expose] def tcrSameSet (n : Nat) (a b : List Nat) : Bool := tcrMaskOf n a == tcrMaskOf n b

@[expose] def tcrBfs (S : TcrSys) (ksMask : Array Bool) : Nat → List Nat → Array Bool → Array Bool
  | 0, _, vis => vis
  | _ + 1, [], vis => vis
  | fuel + 1, v :: rest, vis =>
    let r := S.adj[v]!.foldl (fun (st : Array Bool × List Nat) w =>
      if ksMask[w]! && !st.1[w]! then (st.1.set! w true, w :: st.2) else st) (vis, [])
    tcrBfs S ksMask fuel (rest ++ r.2) r.1

@[expose] def tcrCompOf (S : TcrSys) (ks : List Nat) (seed : Nat) : List Nat :=
  let ksMask := tcrMaskOf S.tcrN ks
  let vis := tcrBfs S ksMask S.tcrN [seed] ((Array.replicate S.tcrN false).set! seed true)
  (List.range S.tcrN).filter fun i => vis[i]!

@[expose] def tcrCompClosed (S : TcrSys) (ks cs : List Nat) (seed : Nat) : Bool :=
  let csMask := tcrMaskOf S.tcrN cs
  csMask[seed]! && cs.all (fun c => ks.all fun k => S.ip[c]![k]! == 0 || csMask[k]!)

@[expose] def tcrComps (S : TcrSys) (ks : List Nat) : List (List Nat) :=
  ks.foldl (fun acc s =>
    if acc.any (fun c => c.contains s) then acc else acc ++ [tcrCompOf S ks s]) []

@[expose] def tcrImgSet (perm : Array Nat) (cs : List Nat) : List Nat := cs.map fun i => perm[i]!

@[expose] def tcrOrbitLen (n : Nat) (perm : Array Nat) (cs : List Nat) (fuel : Nat) : Nat :=
  let m := tcrMaskOf n cs
  let rec go : Nat → Nat → List Nat → Nat
    | 0, _, _ => 0
    | k + 1, s, cur => let nxt := tcrImgSet perm cur
        if tcrMaskOf n nxt == m then s else go k (s + 1) nxt
  go fuel 1 cs

@[expose] def tcrPosOf (S : TcrSys) (psi : List Nat) : List Nat := psi.filter fun i => S.posFlag[i]!

@[expose] def tcrSimpleSys (S : TcrSys) (psi : List Nat) : List Nat :=
  let mask := tcrMaskOf S.tcrN psi
  let pos := tcrPosOf S psi
  pos.filter fun g => !(pos.any fun d =>
    S.ip[g]![d]! == 1 && mask[S.refl[d]![g]!]! && S.posFlag[S.refl[d]![g]!]!)

@[expose] def tcrMoveWord (S : TcrSys) : Nat → List Nat → List Nat → Option (List Nat)
  | 0, _, _ => none
  | f + 1, img, w =>
    match img.find? (fun v => !S.posFlag[v]!) with
    | none => some w
    | some v =>
      let g := S.neg[v]!
      tcrMoveWord S f (img.map fun v => S.refl[g]![v]!) (w ++ [g])

@[expose] def tcrInnerW (S : TcrSys) (pe : Array Nat) (psi delta : List Nat) : Bool :=
  let mask := tcrMaskOf S.tcrN psi
  match tcrMoveWord S 200 (delta.map fun g => pe[g]!) [] with
  | none => false
  | some w => w.all (fun g => mask[g]!) &&
      psi.all fun γ => w.foldl (fun v g => S.refl[g]![v]!) pe[γ]! == γ

@[expose] def tcrDetF : Nat → List (List Int) → Int
  | _, [] => 1
  | 0, _ => 0
  | k + 1, row :: rows =>
    (List.range row.length).foldl (fun s j =>
      s + (if j % 2 == 0 then 1 else -1) * row.getD j 0 *
        tcrDetF k (rows.map fun r => r.eraseIdx j)) 0

@[expose] def tcrMinorL (G : List (List Int)) (i j : Nat) : List (List Int) :=
  (G.eraseIdx i).map fun row => row.eraseIdx j

@[expose] def tcrVsubL (u v : List Int) : List Int := List.zipWith (· - ·) u v

@[expose] def tcrDotZZ : List Int → List Int → Int
  | a :: as, b :: bs => a * b + tcrDotZZ as bs
  | _, _ => 0

@[expose] def tcrCmul (cartan : Array Int) (rank : Nat) (v : List Int) : List Int :=
  (List.range rank).map fun i =>
    (List.range rank).foldl (fun t j => t + cartan[rank * i + j]! * v.getD j 0) 0

@[expose] def tcrColsOf (S : TcrSys) (pe : Array Nat) : List (List Int) :=
  (List.range S.rank).map fun k => S.roots[pe[S.basis[k]!]!]!

@[expose] def tcrOuterDisc (S : TcrSys) (cols : List (List Int)) (psi delta : List Nat) : Bool :=
  let r := delta.length
  let G : List (List Int) := delta.map fun a => delta.map fun b => S.ip[a]![b]!
  let det := tcrDetF r G
  let dv : Int := det.natAbs
  let sgn : Int := if det > 0 then 1 else -1
  let dvecs := delta.map fun a => S.roots[a]!
  let mus : List (List Int) := (List.range r).map fun i =>
    tcrLincomb S.rank ((List.range r).map fun j =>
      sgn * ((if (i + j) % 2 == 0 then 1 else -1) * tcrDetF (r - 1) (tcrMinorL G i j))) dvecs
  let cm := mus.map (tcrCmul S.cartan S.rank)
  let diffs := mus.map fun mu => tcrVsubL (tcrLincomb S.rank mu cols) mu
  dv != 0 &&
    (cm.all fun c => psi.all fun γ => tcrDotZZ c S.roots[γ]! % dv == 0) &&
    (cm.any fun c => diffs.any fun df => tcrDotZZ c df % (dv * dv) != 0)

inductive TcrKind
  | inner
  | suN
  | twoD
  | exc
  deriving DecidableEq

@[expose] def tcrKindOf (S : TcrSys) (pows : Array (Array Nat)) (e : Nat) (psi delta : List Nat)
    (r N : Nat) : Option TcrKind :=
  let pe := pows[e]!
  if tcrInnerW S pe psi delta then some .inner
  else if r == 6 && N == 72 then
    (if tcrOuterDisc S (tcrColsOf S pe) psi delta then some .exc else none)
  else if r == 4 && N == 24 then
    (if tcrOuterDisc S (tcrColsOf S pe) psi delta then
      let p2 := pows[2 * e]!
      (if tcrInnerW S p2 psi delta then some .twoD
       else if tcrOuterDisc S (tcrColsOf S p2) psi delta then some .exc else none)
    else none)
  else if 4 ≤ r && N == 2 * r * (r - 1) then
    (if tcrOuterDisc S (tcrColsOf S pe) psi delta then some .twoD else none)
  else if 2 ≤ r && N == r * (r + 1) then
    (if tcrOuterDisc S (tcrColsOf S pe) psi delta then some .suN else none)
  else some .inner

inductive TcrTg
  | A
  | twA
  | D
  | twD
  | E6
  | E7
  | E8
  | twE6
  | triD4
  deriving DecidableEq

structure TcrLab where
  t : TcrTg
  r : Nat
  n : Nat
  deriving DecidableEq

@[expose] def tcrComponentLabel (r N : Nat) (k : TcrKind) (n : Nat) : TcrLab :=
  match k with
  | .inner =>
    if N = r * (r + 1) then ⟨.A, r, n⟩
    else if N = 2 * r * (r - 1) then ⟨.D, r, n⟩
    else if r = 6 then ⟨.E6, 0, n⟩
    else if r = 7 then ⟨.E7, 0, n⟩
    else ⟨.E8, 0, n⟩
  | .suN => ⟨.twA, r, n⟩
  | .twoD => ⟨.twD, r, n⟩
  | .exc => if r = 6 then ⟨.twE6, 0, n⟩ else ⟨.triD4, 0, n⟩

@[expose] def tcrLabelClass (l : TcrLab) : List TcrLab :=
  l :: (match l.t with
    | .A => if l.r == 3 then [⟨.D, 3, l.n⟩]
        else if l.r == 1 && l.n % 2 == 0 then [⟨.twD, 2, l.n / 2⟩] else []
    | .D => if l.r == 3 then [⟨.A, 3, l.n⟩] else []
    | .twD => if l.r == 3 then [⟨.twA, 3, l.n⟩]
        else if l.r == 2 then [⟨.A, 1, 2 * l.n⟩] else []
    | .twA => if l.r == 3 then [⟨.twD, 3, l.n⟩] else []
    | _ => [])

@[expose] def tcrUntw (t : TcrTg) : Bool :=
  match t with
  | .A | .D | .E6 | .E7 | .E8 => true
  | _ => false

@[expose] def tcrSplitT (p : Nat) (l : TcrLab) : Bool :=
  (tcrUntw l.t && (2 ^ l.n - 1) % p == 0) ||
  (!tcrUntw l.t && l.t != .triD4 && (2 ^ l.n + 1) % p == 0) ||
  ((l.t == .twD || l.t == .triD4) && (2 ^ l.n - 1) % p == 0) ||
  (l.n == 1 && p == 3)

@[expose] def tcrHalfSplitT (p : Nat) (l : TcrLab) : Bool :=
  tcrSplitT p l ||
  ((l.t == .D || l.t == .E7 || l.t == .E8) && (2 ^ l.n + 1) % p == 0) ||
  (((l.t == .twA && l.r == 5) || l.t == .twE6) && (2 ^ l.n - 1) % p == 0) ||
  (l.t == .A && l.r == 5 && l.n == 2 && p == 5) ||
  (l.t == .A && l.r == 8 && l.n == 1 && p == 7) ||
  (l.t == .E6 && l.n == 1 && p == 7)

@[expose] def tcrVecsMod (p : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 => (List.range p).flatMap fun a => (tcrVecsMod p k).map (a :: ·)

@[expose] def tcrIsNorm (u : List Nat) : Bool :=
  match u.find? (fun x => x != 0) with
  | some 1 => true
  | _ => false

@[expose] def tcrNormVecs (p k : Nat) : List (List Nat) := (tcrVecsMod p k).filter tcrIsNorm

@[expose] def tcrDotNZ : List Nat → List Int → Int
  | a :: as, b :: bs => (a : Int) * b + tcrDotNZ as bs
  | _, _ => 0

@[expose] def tcrVanishing (S : TcrSys) (p : Nat) (us : List (List Nat)) : List Nat :=
  (List.range S.tcrN).filter fun i => us.all fun u => tcrDotNZ u S.roots[i]! % (p : Int) == 0

@[expose] def tcrKerCond (S : TcrSys) (p r : Nat) (t : List Nat) (u : List Nat) : Bool :=
  (List.range S.rank).all fun j =>
    (tcrDotNZ u S.roots[t.getD j 0]! - (r : Int) * (u.getD j 0 : Int)) % (p : Int) == 0

@[expose] def tcrNormVec (p : Nat) (v : List Nat) : List Nat :=
  match v.find? (fun x => x != 0) with
  | none => v
  | some a =>
    let c := ((List.range p).find? fun c => c * a % p == 1).getD 1
    v.map fun x => c * x % p

@[expose] def tcrPlaneLines (p : Nat) (u1 u2 : List Nat) : List (List Nat) :=
  (u1 :: (List.range p).map fun a => List.zipWith (fun x y => (a * x + y) % p) u1 u2).map
    (tcrNormVec p)

structure TcrCData where
  e : Nat
  r : Nat
  N : Nat
  ks : List TcrKind

instance : Inhabited TcrCData := ⟨⟨0, 0, 0, []⟩⟩

@[expose] def tcrKindsOf (r N : Nat) : List TcrKind :=
  [.inner] ++ (if (r == 6 && N == 72) || (r == 4 && N == 24) then [.exc] else []) ++
    (if 4 ≤ r && N == 2 * r * (r - 1) then [.twoD] else []) ++
    (if 2 ≤ r && N == r * (r + 1) then [.suN] else [])

@[expose] def tcrPermPows (S : TcrSys) (perm : Array Nat) : Array (Array Nat) :=
  (List.range 24).foldl (fun acc _ =>
    let q := acc.back!
    acc.push (Array.ofFn (n := S.tcrN) fun i => perm[q[i.val]!]!))
    #[Array.ofFn (n := S.tcrN) fun i => i.val]

@[expose] def tcrCdataOf (S : TcrSys) (perm : Array Nat) (pows : Array (Array Nat))
    (psi : List Nat) : Option TcrCData :=
  let e := tcrOrbitLen S.tcrN perm psi S.tcrN
  if e == 0 || 12 < e then none else
    let delta := tcrSimpleSys S psi
    (tcrKindOf S pows e psi delta delta.length psi.length).map fun k =>
      ⟨e, delta.length, psi.length, [k]⟩

@[expose] def tcrCdataOfA (S : TcrSys) (perm : Array Nat) (psi : List Nat) : Option TcrCData :=
  let e := tcrOrbitLen S.tcrN perm psi S.tcrN
  if e == 0 then none else
    let delta := tcrSimpleSys S psi
    some ⟨e, delta.length, psi.length, tcrKindsOf delta.length psi.length⟩

@[expose] def tcrLabsOf (d : TcrCData) (f : Nat) : List TcrLab :=
  d.ks.flatMap fun k => tcrLabelClass (tcrComponentLabel d.r d.N k (d.e * f))

@[expose] def tcrJOk (p : Nat) (flags : List Nat) (allowed : Nat → TcrCData → TcrCData → Bool)
    (dJ : TcrCData) (psiJ : List Nat) (n : Nat) (ls : List (List Nat × TcrCData)) : Bool :=
  flags.all fun f =>
    (List.range ls.length).all fun xi =>
      let x := ls.getD xi default
      let surv := !(tcrSameSet n x.1 psiJ) && (tcrLabsOf x.2 f).any (tcrSplitT p) &&
        (List.range ls.length).all fun di => di == xi ||
          (let ld := tcrLabsOf (ls.getD di default).2 f
           ld.any (fun l => (tcrLabsOf dJ f).contains l) || ld.any (tcrHalfSplitT p))
      !surv || allowed f dJ x.2

@[expose] def tcrPlaneOk (S : TcrSys) (perm : Array Nat) (cd : List Nat → Option TcrCData) (p : Nat)
    (flags : List Nat) (allowed : Nat → TcrCData → TcrCData → Bool) (K : List (List Nat))
    (lt : List (List Nat × List (List Nat × Option TcrCData))) (u1 u2 : List Nat) : Bool :=
  let phiP := tcrVanishing S p [u1, u2]
  let cs := tcrComps S phiP
  let es := cs.map fun c => tcrOrbitLen S.tcrN perm c S.tcrN
  cs.all (fun c => tcrCompClosed S phiP c (c.headD 0)) && es.all (fun e => e != 0) &&
  (!(es.any fun e => 2 ≤ e) ||
    (let lidx := (tcrPlaneLines p u1 u2).map fun v => K.findIdx? (fun w => w == v)
     lidx.all (fun o => o.isSome) &&
     (cs.zip es).all fun x =>
       x.2 < 2 ||
       match cd x.1 with
       | none => false
       | some dJ =>
         let g0 := x.1.headD 0
         let sel : List (Option (List Nat × Option TcrCData)) := lidx.map fun o =>
           ((lt.getD (o.getD 0) default).2).find? fun pc => pc.1.contains g0
         (sel.all fun o => match o with
           | some (_, some _) => true
           | _ => false) &&
         tcrJOk p flags allowed dJ x.1 S.tcrN (sel.filterMap fun o => match o with
           | some (c, some d) => some (c, d)
           | _ => none)))

@[expose] def tcrSweepK (S : TcrSys) (perm : Array Nat) (cd : List Nat → Option TcrCData) (p : Nat)
    (flags : List Nat) (allowed : Nat → TcrCData → TcrCData → Bool) (K : List (List Nat)) : Bool :=
  let lt : List (List Nat × List (List Nat × Option TcrCData)) := K.map fun ℓ =>
    let v := tcrVanishing S p [ℓ]
    (v, (tcrComps S v).map fun c => (c, cd c))
  lt.all (fun x => x.2.all fun c => tcrCompClosed S x.1 c.1 (c.1.headD 0)) &&
  (List.range K.length).all fun i => (List.range K.length).all fun j =>
    j ≤ i || tcrPlaneOk S perm cd p flags allowed K lt (K.getD i []) (K.getD j [])

@[expose] def tcrKernelLines (S : TcrSys) (nv : List (List Nat)) (p r : Nat) (t : List Nat) :
    List (List Nat) :=
  nv.filter (tcrKerCond S p r t)

@[expose] def tcrAllowedC1 (ε : Int) (f : Nat) (dJ dx : TcrCData) : Bool :=
  if ε == 1 && f == 1 then
    (dJ.r == 1 && dJ.N == 2 && dJ.e == 2 && dJ.ks == [.inner] &&
      ((dx.r == 2 && dx.N == 6 && dx.e == 2 && dx.ks == [.inner]) ||
       (dx.r == 4 && dx.N == 24 && dx.e == 1 && dx.ks == [.twoD]) ||
       (dx.r == 5 && dx.N == 30 && dx.e == 1 && dx.ks == [.inner]))) ||
    (dJ.r == 2 && dJ.N == 6 && dJ.e == 2 && dJ.ks == [.inner] &&
      dx.r == 5 && dx.N == 30 && dx.e == 1 && dx.ks == [.inner])
  else if ε == -1 && f == 1 then
    dJ.r == 1 && dJ.N == 2 && dJ.e == 3 && dJ.ks == [.inner] &&
      ((dx.r == 2 && dx.N == 6 && dx.e == 3 && dx.ks == [.suN]) ||
       (dx.r == 4 && dx.N == 24 && dx.e == 1 && dx.ks == [.exc]) ||
       (dx.r == 5 && dx.N == 30 && dx.e == 1 && dx.ks == [.suN]))
  else if ε == -1 && f == 2 then
    dJ.r == 1 && dJ.N == 2 && dJ.e == 2 && dJ.ks == [.inner] &&
      ((dx.r == 2 && dx.N == 6 && dx.e == 2 && dx.ks == [.inner]) ||
       (dx.r == 4 && dx.N == 24 && dx.e == 1 && dx.ks == [.twoD]))
  else false

@[expose] def tcrSweepPhiC1 (S : TcrSys) (nv : List (List Nat)) (ε : Int) (r : Nat)
    (flags : List Nat) (t : List Nat) : Bool :=
  let K := tcrKernelLines S nv 3 r t
  K.length < 2 ||
    (let perm := tcrPermOf S t
     let pows := tcrPermPows S perm
     tcrSweepK S perm (tcrCdataOf S perm pows) 3 flags (tcrAllowedC1 ε) K)

@[expose] def tcrBlockC1 (S : TcrSys) (nv : List (List Nat)) (ε : Int) (r : Nat)
    (flags : List Nat) : Bool :=
  (tcrAutE6 S ε).all fun t => tcrSweepPhiC1 S nv ε r flags t

@[expose] def tcrCheckC1 (_ : Unit := ()) : Bool :=
  let S := tcrE6Sys ()
  let nv := tcrNormVecs 3 6
  S.tcrOk && tcrBlockC1 S nv 1 2 [1, 3] && tcrBlockC1 S nv (-1) 2 [1, 3] &&
    tcrBlockC1 S nv (-1) 1 [2]

@[expose] def tcrConjTuple (S : TcrSys) (i : Nat) (t : List Nat) : List Nat :=
  let perm := tcrPermOf S t
  let g := S.basis[i]!
  (List.range S.rank).map fun j => S.refl[g]![perm[S.refl[g]![S.basis[j]!]!]!]!

@[expose] def tcrClassOrbit (S : TcrSys) (t0 : List Nat) : Array (List Nat × Nat × Nat) :=
  let rec go : Nat → Nat → Array (List Nat × Nat × Nat) → Std.HashSet (List Nat) →
      Array (List Nat × Nat × Nat)
    | 0, _, arr, _ => arr
    | fuel + 1, pos, arr, seen =>
      if pos < arr.size then
        let t := arr[pos]!.1
        let st := (List.range S.rank).foldl
          (fun (st : Array (List Nat × Nat × Nat) × Std.HashSet (List Nat)) i =>
            let t' := tcrConjTuple S i t
            if st.2.contains t' then st else (st.1.push (t', i, pos), st.2.insert t'))
          (arr, seen)
        go fuel (pos + 1) st.1 st.2
      else arr
  go 20000 0 #[(t0, 0, 0)] ((Std.HashSet.emptyWithCapacity 32768).insert t0)

@[expose] def tcrTransportOk (S : TcrSys) : Bool :=
  let A := tcrAutSkew S
  match A with
  | [] => false
  | t0 :: _ =>
    let orb := tcrClassOrbit S t0
    let hs : Std.HashSet (List Nat) := Std.HashSet.ofList (orb.toList.map fun x => x.1)
    orb[0]!.1 == t0 &&
    (List.range orb.size).all (fun pos => pos == 0 ||
      (orb[pos]!.2.2 < pos && orb[pos]!.2.1 < S.rank &&
        tcrConjTuple S orb[pos]!.2.1 orb[orb[pos]!.2.2]!.1 == orb[pos]!.1)) &&
    A.all fun t => hs.contains t

@[expose] def tcrCheckC2 (_ : Unit := ()) : Bool :=
  let S := tcrE8Sys ()
  let t0 := (tcrAutSkew S).headD []
  let perm := tcrPermOf S t0
  let nv := tcrNormVecs 5 8
  let none3 : Nat → TcrCData → TcrCData → Bool := fun _ _ _ => false
  S.tcrOk && tcrTransportOk S &&
  tcrSweepK S perm (tcrCdataOfA S perm) 5 [1, 5] none3 (tcrKernelLines S nv 5 2 t0) &&
  tcrSweepK S perm (tcrCdataOfA S perm) 5 [3] none3 (tcrKernelLines S nv 5 3 t0)

@[expose] def tcrJOkG (split half : TcrLab → Bool) (flags : List Nat)
    (allowed : Nat → TcrCData → TcrCData → Bool) (dJ : TcrCData) (psiJ : List Nat) (n : Nat)
    (ls : List (List Nat × TcrCData)) : Bool :=
  flags.all fun f =>
    (List.range ls.length).all fun xi =>
      let x := ls.getD xi default
      let surv := !(tcrSameSet n x.1 psiJ) && (tcrLabsOf x.2 f).any split &&
        (List.range ls.length).all fun di => di == xi ||
          (let ld := tcrLabsOf (ls.getD di default).2 f
           ld.any (fun l => (tcrLabsOf dJ f).contains l) || ld.any half)
      !surv || allowed f dJ x.2

@[expose] def tcrBareiss (M0 : Array (Array Int)) : Int :=
  let n := M0.size
  let st := (List.range (n - 1)).foldl
    (fun (st : Array (Array Int) × Int × Int × Bool) k =>
      if st.2.2.2 then st else
      match (List.range (n - k)).find? (fun i => st.1[k + i]![k]! != 0) with
      | none => (st.1, st.2.1, st.2.2.1, true)
      | some i0 =>
        let M1 := if i0 == 0 then st.1 else (st.1.set! k st.1[k + i0]!).set! (k + i0) st.1[k]!
        let sign1 := if i0 == 0 then st.2.2.1 else - st.2.2.1
        let pivot := M1[k]![k]!
        let M2 := Array.ofFn (n := n) fun i =>
          if i.val ≤ k then M1[i.val]! else
            Array.ofFn (n := n) fun j =>
              if j.val ≤ k then M1[i.val]![j.val]! else
                (M1[i.val]![j.val]! * pivot - M1[i.val]![k]! * M1[k]![j.val]!) / st.2.1
        (M2, pivot, sign1, false))
    (M0, 1, 1, false)
  if st.2.2.2 then 0 else if n == 0 then 1 else st.2.2.1 * st.1[n - 1]![n - 1]!

@[expose] def tcrColMatrix (S : TcrSys) (cols : List Nat) : Array (Array Int) :=
  Array.ofFn (n := S.rank) fun i => (cols.map fun c => S.roots[c]!.getD i.val 0).toArray

@[expose] def tcrAdj (B : Array (Array Int)) : Array (Array Int) :=
  let n := B.size
  Array.ofFn (n := n) fun i => Array.ofFn (n := n) fun j =>
    let minor : Array (Array Int) := (((List.range n).filter (· != j.val)).map fun r =>
      (((List.range n).filter (· != i.val)).map fun c => B[r]![c]!).toArray).toArray
    (if (i.val + j.val) % 2 == 0 then 1 else -1) * tcrBareiss minor

@[expose] def tcrMatMul (A B : Array (Array Int)) : Array (Array Int) :=
  let n := A.size
  Array.ofFn (n := n) fun i => Array.ofFn (n := n) fun j =>
    (List.range n).foldl (fun s k => s + A[i]![k]! * B[k]![j]!) 0

@[expose] def tcrScalarMat (n : Nat) (d : Int) : Array (Array Int) :=
  Array.ofFn (n := n) fun i => Array.ofFn (n := n) fun j => if i.val == j.val then d else 0

@[expose] def tcrMatVec (A : Array (Array Int)) (v : List Int) : List Int :=
  (List.range A.size).map fun i =>
    (List.range A.size).foldl (fun s k => s + A[i]![k]! * v.getD k 0) 0

@[expose] def tcrStrip (q : Nat) : Nat → Nat → Nat
  | 0, m => m
  | f + 1, m => if m != 0 && m % q == 0 then tcrStrip q f (m / q) else m

@[expose] def tcrSmooth (n : Nat) : Bool :=
  n != 0 && tcrStrip 5 200 (tcrStrip 3 200 (tcrStrip 2 200 n)) == 1

@[expose] def tcrGMul (x y : Int × Int) : Int × Int :=
  (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1)

@[expose] def tcrGNorm (x : Int × Int) : Nat := (x.1 * x.1 + x.2 * x.2).natAbs

@[expose] def tcrGCross (x1 x2 y1 y2 : Int × Int) : Int × Int :=
  let u := tcrGMul x1 y2
  let v := tcrGMul x2 y1
  (u.1 - v.1, u.2 - v.2)

@[expose] def tcrIndep (S : TcrSys) (idxs : List Nat) : Bool :=
  tcrBareiss ((idxs.map fun i => (idxs.map fun j => S.ip[i]![j]!).toArray).toArray) != 0

@[expose] def tcrSplitFree (l : TcrLab) : Bool :=
  (tcrUntw l.t && l.n % 4 == 0) || (!tcrUntw l.t && l.t != .triD4 && l.n % 4 == 2) ||
  ((l.t == .twD || l.t == .triD4) && l.n % 4 == 0)

@[expose] def tcrHalfFree (l : TcrLab) : Bool :=
  tcrSplitFree l || ((l.t == .D || l.t == .E7 || l.t == .E8) && l.n % 4 == 2) ||
  (((l.t == .twA && l.r == 5) || l.t == .twE6) && l.n % 4 == 0)

@[expose] def tcrPairBody (S : TcrSys) (perm : Array Nat) (a b : Nat) (cols : List Nat) : Bool :=
  let n := S.tcrN
  let B := tcrColMatrix S cols
  let d := tcrBareiss B
  let X := tcrAdj B
  let ys : Array (List Int) := Array.ofFn (n := n) fun e => tcrMatVec X S.roots[e.val]!
  let w : Nat → (Int × Int) × (Int × Int) := fun e =>
    ((ys[e]!.getD 4 0, ys[e]!.getD 5 0), (ys[e]!.getD 6 0, ys[e]!.getD 7 0))
  let cross : Nat → Nat → Int × Int := fun e e' => tcrGCross (w e).1 (w e).2 (w e').1 (w e').2
  let sig := (List.range n).filter fun e => (w e).1 == (0, 0) && (w e).2 == (0, 0)
  let sroots := [a, b, S.refl[b]![a]!, S.neg[a]!, S.neg[b]!, S.neg[S.refl[b]![a]!]!]
  let sigMask := tcrMaskOf n sig
  let out := (List.range n).filter fun e => !sigMask[e]!
  let reps := out.foldl (fun reps e =>
    if reps.any (fun r => cross e r == (0, 0)) then reps else reps ++ [e]) []
  let cls := reps.map fun r => out.filter fun e => cross e r == (0, 0)
  let ldata : List (List Nat × Option TcrCData) := cls.map fun c =>
    let ks := (List.range n).filter fun e => sigMask[e]! || c.contains e
    let comp := tcrCompOf S ks a
    (comp, if tcrCompClosed S ks comp a then tcrCdataOfA S perm comp else none)
  tcrMatMul B X == tcrScalarMat S.rank d && d != 0 && tcrSmooth d.natAbs &&
  tcrSameSet n sig (sroots ++ sroots.map fun x => perm[x]!) &&
  (out.all fun e => let we := w e
    (we.1 != (0, 0) && tcrSmooth (tcrGNorm we.1)) ||
      (we.2 != (0, 0) && tcrSmooth (tcrGNorm we.2))) &&
  (List.range reps.length).all (fun i => (List.range reps.length).all fun j => j ≤ i ||
    (let c := cross (reps.getD i 0) (reps.getD j 0); c != (0, 0) && tcrSmooth (tcrGNorm c))) &&
  (tcrComps S sig).all (fun c => tcrCompClosed S sig c (c.headD 0)) &&
  (tcrComps S sig).any (fun c => tcrSameSet n c sroots) &&
  ldata.all (fun x => x.2.isSome) &&
  (match tcrCdataOfA S perm sroots with
   | none => false
   | some dJ =>
     tcrJOkG tcrSplitFree tcrHalfFree [1] (fun _ _ _ => false) dJ sroots n
       ((ldata.filterMap fun x => x.2.map fun dd => (x.1, dd)) ++ [(sroots, dJ)]))

@[expose] def tcrPairC3 (S : TcrSys) (perm : Array Nat) (a b : Nat) : Bool :=
  let first := [a, perm[a]!, b, perm[b]!]
  match (List.range S.tcrN).find? fun g => tcrIndep S (first ++ [g, perm[g]!]) with
  | none => false
  | some g =>
    match (List.range S.tcrN).find? fun dd =>
        tcrIndep S (first ++ [g, perm[g]!, dd, perm[dd]!]) with
    | none => false
    | some dd => tcrPairBody S perm a b (first ++ [g, perm[g]!, dd, perm[dd]!])

@[expose] def tcrRootLines (S : TcrSys) (perm : Array Nat) : List Nat :=
  (List.range S.tcrN).filter fun e =>
    [e, perm[e]!, S.neg[e]!, S.neg[perm[e]!]!].all fun x => e ≤ x

@[expose] def tcrMinorsOk (S : TcrSys) (perm : Array Nat) : Bool :=
  let L := tcrRootLines S perm
  L.length == 60 &&
  (List.range 60).all fun i => (List.range 60).all fun j => j ≤ i ||
    (List.range 60).all fun k => k ≤ j || (List.range 60).all fun l => l ≤ k ||
      (let e1 := L.getD i 0
       let e2 := L.getD j 0
       let e3 := L.getD k 0
       let e4 := L.getD l 0
       let g := tcrBareiss ((([e1, perm[e1]!, e2, perm[e2]!, e3, perm[e3]!, e4, perm[e4]!].map
         fun x => ([e1, perm[e1]!, e2, perm[e2]!, e3, perm[e3]!, e4, perm[e4]!].map
           fun y => S.ip[x]![y]!).toArray)).toArray)
       [0, 1, 4, 16, 25, 64, 81, 256].contains g)

@[expose] def tcrPairsC3 (S : TcrSys) (perm : Array Nat) : Bool :=
  (List.range S.tcrN).all fun a => (List.range S.tcrN).all fun b =>
    !(S.ip[a]![b]! == -1 && S.ip[a]![perm[a]!]! == 0 && S.ip[a]![perm[b]!]! == 0 &&
      S.ip[b]![perm[a]!]! == 0 && S.ip[b]![perm[b]!]! == 0) || tcrPairC3 S perm a b

@[expose] def tcrCheckC3 (_ : Unit := ()) : Bool :=
  let S := tcrE8Sys ()
  let t0 := (tcrAutSkew S).headD []
  let perm := tcrPermOf S t0
  S.tcrOk && tcrTransportOk S && tcrMinorsOk S perm && tcrPairsC3 S perm

end Certificates.TcRes

end
