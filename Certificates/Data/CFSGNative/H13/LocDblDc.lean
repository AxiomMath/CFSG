module

public import Std.Data.HashMap
public import Std.Data.HashSet

public section

namespace CFSG.Quasithin.H13.LocDbl.DcNative

@[expose] def img (s : Array Nat) (p : Nat) : Nat := s.getD p 0

@[expose] def keyNat (n r : Nat) (T : List Nat) : Nat :=
  (T.take r).foldl (fun acc q => acc * n + q) 0

@[expose] def evalW (T : Array (Array Nat)) (w : List Nat) (p : Nat) : Nat :=
  w.foldr (fun l q => img (T.getD l #[]) q) p

@[expose] def tabW (n : Nat) (T : Array (Array Nat)) (w : List Nat) : Array Nat :=
  (Array.range n).map (evalW T w)

@[expose] def invL (l : Nat) : Nat := if l < 2 then l + 2 else l - 2

@[expose] def invW (w : List Nat) : List Nat := (w.map invL).reverse

@[expose] def ptsStep (G : Array (Array Nat)) (par lab : Array Nat) (q : Nat) (acc : Array Nat)
    (k : Nat) : Array Nat :=
  acc.push (if k = 0 then q else img (G.getD (lab.getD k 0) #[]) (acc.getD (par.getD k 0) 0))

@[expose] def ptsArr (G : Array (Array Nat)) (par lab : Array Nat) (N q : Nat) : Array Nat :=
  (List.range N).foldl (ptsStep G par lab q) #[]

@[expose] def enumOK (N : Nat) (G : Array (Array Nat)) (par lab : Array Nat) : Bool :=
  (List.range N).all fun k =>
    k == 0 || (decide (par.getD k 0 < k) && decide (lab.getD k 0 < G.size))

@[expose] def rowKeys (n : Nat) (B : List Nat) (G : Array (Array Nat)) (par lab : Array Nat)
    (N : Nat) : List Nat :=
  let P := B.map (ptsArr G par lab N)
  (List.range N).map fun k => keyNat n B.length (P.map fun A => A.getD k 0)

@[expose] def strictInc : List Nat → Bool
  | a :: b :: l => decide (a < b) && strictInc (b :: l)
  | _ => true

@[expose] def distinctNat (l : List Nat) : Bool :=
  strictInc (l.mergeSort fun a b => decide (a ≤ b))

@[expose] def conjKeys (n : Nat) (B : List Nat) (G : Array (Array Nat)) (par lab : Array Nat)
    (N : Nat) (Xi Y : Array Nat) : List Nat :=
  let P := B.map fun b => ptsArr G par lab N (img Y b)
  (List.range N).map fun k => keyNat n B.length (P.map fun A => img Xi (A.getD k 0))

@[expose] def hitCount (S : Std.HashSet Nat) (ks : List Nat) : Nat :=
  (ks.filter fun k => S.contains k).length

@[expose] def noHit (S : Std.HashSet Nat) (ks : List Nat) : Bool :=
  ks.all fun k => !S.contains k

@[expose] def wt (i j : Nat) : Nat :=
  let z := i * 1000003 + j + 1
  z * z % 1000000007 * z % 1000000007

@[expose] def dcInv (n : Nat) (lb X : Array Nat) : Nat :=
  ((List.range n).map fun q => wt (lb.getD q 0) (lb.getD (img X q) 0)).sum

@[expose] def labOK (n : Nat) (lb : Array Nat) (G : Array (Array Nat)) : Bool :=
  G.all fun s => (List.range n).all fun q => lb.getD (img s q) 0 == lb.getD q 0

@[expose] def edgeLetter (RT RTi AB : Array (Array Nat)) (w : List Nat) (l p : Nat) : Nat :=
  if l < RT.size then img (RT.getD l #[]) p
  else if l < RT.size + RTi.size then img (RTi.getD (l - RT.size) #[]) p
  else if l = RT.size + RTi.size then evalW AB w p
  else evalW AB (invW w) p

@[expose] def evalE (RT RTi AB : Array (Array Nat)) (w e : List Nat) (p : Nat) : Nat :=
  e.foldr (fun l q => edgeLetter RT RTi AB w l q) p

@[expose] def edgeOK (B : List Nat) (RT RTi AB : Array (Array Nat)) (reps : Array (List Nat))
    (ed : Nat × Nat × List Nat) : Bool :=
  decide (ed.1 < reps.size) && decide (ed.2.1 < reps.size) &&
    ed.2.2.all (fun l => decide (l < RT.size + RTi.size + 2)) &&
    B.all fun b => evalW AB (reps.getD ed.2.1 []) b ==
      evalE RT RTi AB (reps.getD ed.1 []) ed.2.2 b

@[expose] def inTreeOK (m c0 : Nat) (edges : Array (Nat × Nat × List Nat))
    (inEdge dIn : Array Nat) : Bool :=
  (List.range m).all fun i => i == c0 ||
    (decide (inEdge.getD i 0 < edges.size) &&
      ((edges.getD (inEdge.getD i 0) (0, 0, [])).1 == i) &&
      decide (dIn.getD (edges.getD (inEdge.getD i 0) (0, 0, [])).2.1 0 < dIn.getD i 0))

@[expose] def outTreeOK (c0 : Nat) (reach : List Nat) (edges : Array (Nat × Nat × List Nat))
    (outEdge dOut : Array Nat) : Bool :=
  reach.all fun j => j == c0 ||
    (decide (outEdge.getD j 0 < edges.size) &&
      ((edges.getD (outEdge.getD j 0) (0, 0, [])).2.1 == j) &&
      reach.contains (edges.getD (outEdge.getD j 0) (0, 0, [])).1 &&
      decide (dOut.getD (edges.getD (outEdge.getD j 0) (0, 0, [])).1 0 < dOut.getD j 0))

@[expose] def rowOf (P : List (Array Nat)) (k : Nat) : List Nat := P.map fun A => A.getD k 0

@[expose] def closedStep (n : Nat) (B : List Nat) (G : Array (Array Nat)) (P : List (Array Nat))
    (M : Std.HashMap Nat Nat) (N k t : Nat) : Bool :=
  match M.get? (keyNat n B.length ((rowOf P k).map (img (G.getD t #[])))) with
  | some k' => decide (k' < N) && (rowOf P k).map (img (G.getD t #[])) == rowOf P k'
  | none => false

@[expose] def closedOK (n : Nat) (B : List Nat) (G : Array (Array Nat)) (par lab : Array Nat)
    (N : Nat) : Bool :=
  let P := B.map (ptsArr G par lab N)
  let M : Std.HashMap Nat Nat :=
    Std.HashMap.ofList ((List.range N).map fun k => (keyNat n B.length (rowOf P k), k))
  (List.range N).all fun k => (List.range G.size).all fun t => closedStep n B G P M N k t

@[expose] def unionLB (kss : List (List Nat)) : Nat :=
  (kss.foldl (fun (acc : Nat × Std.HashSet Nat) ks =>
    (acc.1 + (ks.filter fun k => !acc.2.contains k).length, acc.2.insertMany ks)) (0, ∅)).1

@[expose] def bfsEnumL (n : Nat) (B : List Nat) (G : Array (Array Nat)) (cap : Nat) :
    Array Nat × Array Nat := Id.run do
  let mut rows : Array (List Nat) := #[B]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut seen : Std.HashSet Nat := (∅ : Std.HashSet Nat).insert (keyNat n B.length B)
  let mut i := 0
  for _ in [0:cap] do
    if i < rows.size then
      let r := rows[i]!
      for t in [0:G.size] do
        let r' := r.map (img (G.getD t #[]))
        let k := keyNat n B.length r'
        if !seen.contains k then
          seen := seen.insert k
          rows := rows.push r'
          par := par.push i
          lab := lab.push t
      i := i + 1
  return (par, lab)

@[expose] def orbitLabels (n : Nat) (G : Array (Array Nat)) : Array Nat := Id.run do
  let mut lb : Array Nat := Array.replicate n n
  let mut c := 0
  for s in [0:n] do
    if lb.getD s 0 == n then
      lb := lb.set! s c
      let mut q : Array Nat := #[s]
      let mut h := 0
      for _ in [0:n] do
        if h < q.size then
          let x := q.getD h 0
          h := h + 1
          for t in [0:G.size] do
            let y := img (G.getD t #[]) x
            if lb.getD y 0 == n then
              lb := lb.set! y c
              q := q.push y
      c := c + 1
  return lb

@[expose] def invTab (s : Array Nat) : Array Nat := Id.run do
  let mut r : Array Nat := Array.replicate s.size 0
  for i in [0:s.size] do
    r := r.set! (s.getD i 0) i
  return r

@[expose] def digits (s : String) : List Nat :=
  s.toList.map fun c => c.toNat - '0'.toNat

@[expose] def parseWords (s : String) : Array (List Nat) :=
  ((s.splitOn ",").filter (· ≠ "")).toArray.map digits

@[expose] def parseNats (s : String) : Array Nat :=
  ((s.splitOn " ").filterMap String.toNat?).toArray

@[expose] def parseEdges (s : String) : Array (Nat × Nat × List Nat) :=
  ((s.splitOn ",").filter (· ≠ "")).toArray.map fun e =>
    match e.splitOn " " with
    | [a, b, w] => (a.toNat!, b.toNat!, digits w)
    | _ => (0, 0, [])

structure DcData where
  n : Nat
  B : List Nat
  AB : Array (Array Nat)
  RT : Array (Array Nat)
  RTi : Array (Array Nat)
  NR : Nat
  rpar : Array Nat
  rlab : Array Nat
  lb : Array Nat
  reps : Array (List Nat)
  edges : Array (Nat × Nat × List Nat)
  c0 : Nat
  inEdge : Array Nat
  dIn : Array Nat
  reach : List Nat
  outEdge : Array Nat
  dOut : Array Nat
  Vs : List (List (List Nat) × Array Nat × Array Nat × Nat)
  order : Nat

namespace DcData

variable (D : DcData)

@[expose] def rKeys : List Nat := rowKeys D.n D.B D.RT D.rpar D.rlab D.NR

@[expose] def rSet : Std.HashSet Nat := Std.HashSet.ofList D.rKeys

@[expose] def X (j : Nat) : Array Nat := tabW D.n D.AB (D.reps.getD j [])

@[expose] def Xi (j : Nat) : Array Nat := tabW D.n D.AB (invW (D.reps.getD j []))

@[expose] def massWith (S : Std.HashSet Nat) (j : Nat) : Nat :=
  D.NR * (D.NR / hitCount S (conjKeys D.n D.B D.RT D.rpar D.rlab D.NR (D.Xi j) (D.X j)))

@[expose] def VG (ws : List (List Nat)) : Array (Array Nat) :=
  D.RT ++ (ws.map (tabW D.n D.AB)).toArray

@[expose] def vKeys (V : List (List Nat) × Array Nat × Array Nat × Nat) : List Nat :=
  rowKeys D.n D.B (D.VG V.1) V.2.1 V.2.2.1 V.2.2.2

@[expose] def chkBasic : Bool :=
  D.B.all (fun b => decide (b < D.n)) && D.AB.size == 4 && D.RT.size == D.RTi.size &&
    D.reps.all (fun w => w.all fun l => decide (l < 4)) && decide (D.c0 < D.reps.size) &&
    D.reach.all (fun j => decide (j < D.reps.size)) && decide (D.Vs.length ≤ 3) &&
    D.Vs.all (fun V => V.1.all fun w => w.all fun l => decide (l < 4))

@[expose] def chkR : Bool :=
  enumOK D.NR D.RT D.rpar D.rlab && distinctNat D.rKeys &&
    closedOK D.n D.B D.RT D.rpar D.rlab D.NR && decide (0 < D.NR)

@[expose] def chkInv : Bool :=
  D.AB.size == 4 && D.RTi.size == D.RT.size &&
    (List.range D.n).all (fun q => img (D.AB.getD 2 #[]) (img (D.AB.getD 0 #[]) q) == q &&
      img (D.AB.getD 3 #[]) (img (D.AB.getD 1 #[]) q) == q) &&
    (List.range D.RT.size).all fun t => (List.range D.n).all fun q =>
      img (D.RTi.getD t #[]) (img (D.RT.getD t #[]) q) == q

@[expose] def chkLab : Bool := labOK D.n D.lb D.RT

@[expose] def chkDistWith (S : Std.HashSet Nat) : Bool :=
  let invs := ((List.range D.reps.size).map fun j => dcInv D.n D.lb (D.X j)).toArray
  (List.range D.reps.size).all fun i => (List.range D.reps.size).all fun j =>
    decide (j ≤ i) || invs.getD i 0 != invs.getD j 0 ||
      noHit S (conjKeys D.n D.B D.RT D.rpar D.rlab D.NR (D.Xi i) (D.X j))

@[expose] def chkDist : Bool := D.chkDistWith D.rSet

@[expose] def chkEdges : Bool :=
  D.edges.all (edgeOK D.B D.RT D.RTi D.AB D.reps) &&
    inTreeOK D.reps.size D.c0 D.edges D.inEdge D.dIn &&
    outTreeOK D.c0 D.reach D.edges D.outEdge D.dOut && distinctNat D.reach

@[expose] def chkVs : Bool :=
  D.Vs.all fun V => enumOK V.2.2.2 (D.VG V.1) V.2.1 V.2.2.1 && distinctNat (D.vKeys V) &&
    closedOK D.n D.B (D.VG V.1) V.2.1 V.2.2.1 V.2.2.2 && decide (0 < V.2.2.2) &&
      decide (V.2.2.2 < D.order)

@[expose] def chkMassWith (S : Std.HashSet Nat) : Bool :=
  let ms := ((List.range D.reps.size).map (D.massWith S)).toArray
  decide (D.order < 2 * (D.reach.map fun j => ms.getD j 0).sum) &&
    decide (D.order ≤ ms.toList.sum + unionLB (D.Vs.map D.vKeys))

@[expose] def chkMass : Bool := D.chkMassWith D.rSet

@[expose] def chkAll : Bool :=
  D.chkInv && D.chkBasic && D.chkR && D.chkLab && D.chkDist && D.chkEdges && D.chkVs && D.chkMass

end DcData

end CFSG.Quasithin.H13.LocDbl.DcNative
