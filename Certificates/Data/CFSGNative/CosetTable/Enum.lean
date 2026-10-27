module

public section

namespace CFSG.CosetTable

@[expose] def allBelow (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => p n && allBelow p n

@[expose] def countBelowAux (p : Nat → Bool) : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => countBelowAux p n (if p n then acc + 1 else acc)

@[expose] def countBelow (p : Nat → Bool) (n : Nat) : Nat := countBelowAux p n 0

@[expose] def invWord (inv : Array Nat) (w : List Nat) : List Nat :=
  w.reverse.map fun x => inv.getD x 0

structure Params where
  L : Nat
  inv : Array Nat
  scans : Array (List (List Nat × List Nat))
  subs : List (List Nat × List Nat)
  rels : List (List Nat × List Nat) := []

structure St where
  tab : Array Nat
  fwd : Array Nat
  par : Array Nat
  next : Nat
  ded : Array Nat
  queue : Array Nat
  qi : Nat
  overflow : Bool

@[expose] def St.init (L cap : Nat) : St where
  tab := Array.replicate ((cap + 1) * L) 0
  fwd := Array.range (cap + 1)
  par := Array.replicate (cap + 1) 0
  next := 2
  ded := #[]
  queue := #[]
  qi := 0
  overflow := false

@[expose] def walk (L : Nat) (tab : Array Nat) : Nat → Nat → Nat → List Nat → Nat × Nat
  | _, k, c, [] => (k, c)
  | 0, k, c, _ :: _ => (k, c)
  | lim + 1, k, c, x :: w =>
    let d := tab.getD (c * L + x) 0
    if d == 0 then (k, c) else walk L tab lim (k + 1) d w

@[expose] def find (fwd : Array Nat) : Nat → Nat → Nat
  | 0, c => c
  | fuel + 1, c =>
    let d := fwd.getD c c
    if d == c then c else find fwd fuel d

@[expose] def merge (st : St) (a b : Nat) : St :=
  let ra := find st.fwd st.next a
  let rb := find st.fwd st.next b
  if ra == rb || st.next ≤ ra || st.next ≤ rb then st
  else if ra < rb then
    { st with fwd := st.fwd.set! rb ra, queue := st.queue.push rb }
  else
    { st with fwd := st.fwd.set! ra rb, queue := st.queue.push ra }

@[expose] def coincLetter (P : Params) (st : St) (g x : Nat) : St :=
  let d := st.tab.getD (g * P.L + x) 0
  if d == 0 then st else
  let ix := P.inv.getD x 0
  let st := if st.tab.getD (d * P.L + ix) 0 == g then
      { st with tab := st.tab.set! (d * P.L + ix) 0 } else st
  let mu := find st.fwd st.next g
  let nu := find st.fwd st.next d
  let e := st.tab.getD (mu * P.L + x) 0
  if e != 0 then merge st nu e
  else
    let e' := st.tab.getD (nu * P.L + ix) 0
    if e' != 0 then merge st mu e'
    else { st with tab := (st.tab.set! (mu * P.L + x) nu).set! (nu * P.L + ix) mu,
                   ded := st.ded.push (mu * P.L + x) }

@[expose] def coincRow (P : Params) (g : Nat) : Nat → St → St
  | 0, st => st
  | n + 1, st => coincRow P g n (coincLetter P st g (P.L - (n + 1)))

@[expose] def coincQueue (P : Params) : Nat → St → St
  | 0, st => st
  | fuel + 1, st =>
    if st.qi < st.queue.size then
      let g := st.queue.getD st.qi 0
      coincQueue P fuel (coincRow P g P.L { st with qi := st.qi + 1 })
    else { st with queue := #[], qi := 0 }

@[expose] def coincidence (P : Params) (st : St) (a b : Nat) : St :=
  coincQueue P (st.next * (P.L + 1) + 1) (merge st a b)

@[expose] def deduce (P : Params) (st : St) (f x b : Nat) : St :=
  if f < st.next && b < st.next && x < P.L then
    { st with tab := (st.tab.set! (f * P.L + x) b).set! (b * P.L + P.inv.getD x 0) f,
              ded := st.ded.push (f * P.L + x) }
  else st

@[expose] def define (P : Params) (st : St) (a x : Nat) : St :=
  let b := st.next
  if 0 < a && a < b && x < P.L && b < st.par.size then
    { st with tab := (st.tab.set! (a * P.L + x) b).set! (b * P.L + P.inv.getD x 0) a,
              par := st.par.set! b (a * P.L + x), next := b + 1,
              ded := st.ded.push (a * P.L + x) }
  else { st with overflow := true }

inductive Scan where
  | closed : Scan
  | coinc (f b : Nat) : Scan
  | deduct (f x b : Nat) : Scan
  | gap (f x : Nat) : Scan

@[expose] def scanWord (L : Nat) (tab : Array Nat) (a : Nat) (w w' : List Nat) : Scan :=
  let r := w.length
  let (i, f) := walk L tab r 0 a w
  if i == r then (if f == a then .closed else .coinc f a)
  else
    let (j, b) := walk L tab (r - i) 0 a w'
    if j == r - i then (if f == b then .closed else .coinc f b)
    else if j + 1 == r - i then .deduct f (w.getD i 0) b
    else .gap f (w.getD i 0)

@[expose] def scan (P : Params) (st : St) (a : Nat) (w w' : List Nat) : St :=
  match scanWord P.L st.tab a w w' with
  | .closed => st
  | .coinc f b => coincidence P st f b
  | .deduct f x b => deduce P st f x b
  | .gap _ _ => st

@[expose] def scanAll (P : Params) (a : Nat) : List (List Nat × List Nat) → St → St
  | [], st => st
  | p :: ps, st =>
    if st.fwd.getD a a == a then scanAll P a ps (scan P st a p.1 p.2) else st

@[expose] def processDed (P : Params) : Nat → St → St
  | 0, st => st
  | fuel + 1, st =>
    match st.ded.back? with
    | none => st
    | some e =>
      let st := { st with ded := st.ded.pop }
      let a := e / P.L
      if st.fwd.getD a a == a then
        processDed P fuel (scanAll P a (P.scans.getD (e % P.L) []) st)
      else processDed P fuel st

@[expose] def fillWord (P : Params) (w w' : List Nat) : Nat → St → St
  | 0, st => st
  | fuel + 1, st =>
    match scanWord P.L st.tab 1 w w' with
    | .closed => st
    | .coinc f b => coincidence P st f b
    | .deduct f x b => deduce P st f x b
    | .gap f x =>
      let st := define P st f x
      if st.overflow then st else fillWord P w w' fuel st

@[expose] def fillSubs (P : Params) (fuel : Nat) : List (List Nat × List Nat) → St → St
  | [], st => st
  | p :: ps, st =>
    fillSubs P fuel ps (processDed P fuel (fillWord P p.1 p.2 (p.1.length + 1) st))

@[expose] def fillRow (P : Params) (fuel c : Nat) : Nat → St → St
  | 0, st => st
  | n + 1, st =>
    if st.overflow || st.fwd.getD c c != c then st
    else
      let x := P.L - (n + 1)
      if st.tab.getD (c * P.L + x) 0 == 0 then
        fillRow P fuel c n (processDed P fuel (define P st c x))
      else fillRow P fuel c n st

@[expose] def felsch (P : Params) (fuel : Nat) : Nat → Nat → St → St
  | 0, _, st => st
  | n + 1, c, st =>
    if c < st.next && !st.overflow then felsch P fuel n (c + 1) (fillRow P fuel c P.L st)
    else st

@[expose] def enumerate (P : Params) (cap : Nat) : St :=
  let fuel := 64 * (cap + 1) * (P.L + 1)
  felsch P fuel (cap + 1) 1 (fillSubs P fuel P.subs (St.init P.L cap))

@[expose] def rotations (w : List Nat) : List (List Nat) :=
  (List.range w.length).map fun k => w.drop k ++ w.take k

@[expose] def dedup : List (List Nat) → List (List Nat)
  | [] => []
  | w :: ws => let ws' := dedup ws; if ws'.contains w then ws' else w :: ws'

@[expose] def mkParams (L : Nat) (inv : Array Nat) (rels subs : List (List Nat)) : Params :=
  let all := (dedup ((rels ++ rels.map (invWord inv)).flatMap rotations)).mergeSort
    fun u v => u.length ≤ v.length
  { L := L, inv := inv,
    scans := (Array.range L).map fun x =>
      (all.filter fun w => w.head? == some x).map fun w => (w, invWord inv w),
    subs := subs.map fun w => (w, invWord inv w),
    rels := rels.map fun w => (w, invWord inv w) }

@[expose] def hltWord (P : Params) (c : Nat) (w w' : List Nat) : Nat → St → St
  | 0, st => st
  | fuel + 1, st =>
    if st.fwd.getD c c != c then st else
    match scanWord P.L st.tab c w w' with
    | .closed => st
    | .coinc f b => coincidence P st f b
    | .deduct f x b => deduce P st f x b
    | .gap f x =>
      let st := define P st f x
      if st.overflow then st else hltWord P c w w' fuel st

@[expose] def hltRow (P : Params) (fuel c : Nat) : List (List Nat × List Nat) → St → St
  | [], st => st
  | p :: ps, st =>
    if st.overflow then st
    else hltRow P fuel c ps (processDed P fuel (hltWord P c p.1 p.2 (p.1.length + 1) st))

@[expose] def hlt (P : Params) (fuel : Nat) : Nat → Nat → St → St
  | 0, _, st => st
  | n + 1, c, st =>
    if c < st.next && !st.overflow then hlt P fuel n (c + 1) (hltRow P fuel c P.rels st)
    else st

@[expose] def enumerateHLT (P : Params) (cap : Nat) : St :=
  let fuel := 64 * (cap + 1) * (P.L + 1)
  felsch P fuel (cap + 1) 1 (hlt P fuel (cap + 1) 1 (fillSubs P fuel P.subs (St.init P.L cap)))

@[expose] def St.live (st : St) (c : Nat) : Bool :=
  0 < c && c < st.next && st.fwd.getD c c == c

@[expose] def St.liveCount (st : St) : Nat := countBelow st.live st.next

@[expose] def St.complete (L : Nat) (st : St) : Bool :=
  st.live 1 && allBelow (fun c => !st.live c ||
    allBelow (fun x => st.live (st.tab.getD (c * L + x) 0)) L) st.next

@[expose] def check (P : Params) (cap n : Nat) : Bool :=
  let st := enumerate P cap
  !st.overflow && st.complete P.L && st.liveCount == n

@[expose] def checkHLT (P : Params) (cap n : Nat) : Bool :=
  let st := enumerateHLT P cap
  !st.overflow && st.complete P.L && st.liveCount == n

end CFSG.CosetTable
