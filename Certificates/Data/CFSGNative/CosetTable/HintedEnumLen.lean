module

public import Certificates.Data.CFSGNative.CosetTable.Enum
public import Certificates.Data.CFSGNative.CosetTable.EnumCLen

public section

namespace CFSG.CosetTable

@[expose] def scanWordL (L : Nat) (tab : Array Nat) (a : Nat) (w w' : List Nat) (r : Nat) : Scan :=
  let (i, f) := walk L tab r 0 a w
  if i == r then (if f == a then .closed else .coinc f a)
  else
    let (j, b) := walk L tab (r - i) 0 a w'
    if j == r - i then (if f == b then .closed else .coinc f b)
    else if j + 1 == r - i then .deduct f (w.getD i 0) b
    else .gap f (w.getD i 0)

@[expose] def scanL (P : Params) (st : St) (a : Nat) (w w' : List Nat) (r : Nat) : St :=
  match scanWordL P.L st.tab a w w' r with
  | .closed => st
  | .coinc f b => coincidence P st f b
  | .deduct f x b => deduce P st f x b
  | .gap _ _ => st

@[expose] def scanAllL (P : Params) (a : Nat) : LScan → St → St
  | [], st => st
  | p :: ps, st =>
    if st.fwd.getD a a == a then scanAllL P a ps (scanL P st a p.1 p.2.1 p.2.2) else st

@[expose] def processDedL (P : Params) (S : Array LScan) : Nat → St → St
  | 0, st => st
  | fuel + 1, st =>
    match st.ded.back? with
    | none => st
    | some e =>
      let st := { st with ded := st.ded.pop }
      let a := e / P.L
      if st.fwd.getD a a == a then
        processDedL P S fuel (scanAllL P a (S.getD (e % P.L) []) st)
      else processDedL P S fuel st

@[expose] def fillSubsL (P : Params) (S : Array LScan) (fuel : Nat) :
    List (List Nat × List Nat) → St → St
  | [], st => st
  | p :: ps, st =>
    fillSubsL P S fuel ps (processDedL P S fuel (fillWord P p.1 p.2 (p.1.length + 1) st))

@[expose] def fillRowL (P : Params) (S : Array LScan) (fuel c : Nat) : Nat → St → St
  | 0, st => st
  | n + 1, st =>
    if st.overflow || st.fwd.getD c c != c then st
    else
      let x := P.L - (n + 1)
      if st.tab.getD (c * P.L + x) 0 == 0 then
        fillRowL P S fuel c n (processDedL P S fuel (define P st c x))
      else fillRowL P S fuel c n st

@[expose] def felschL (P : Params) (S : Array LScan) (fuel : Nat) : Nat → Nat → St → St
  | 0, _, st => st
  | n + 1, c, st =>
    if c < st.next && !st.overflow then felschL P S fuel n (c + 1) (fillRowL P S fuel c P.L st)
    else st

@[expose] def hltWordL (P : Params) (c : Nat) (w w' : List Nat) (r : Nat) : Nat → St → St
  | 0, st => st
  | fuel + 1, st =>
    if st.fwd.getD c c != c then st else
    match scanWordL P.L st.tab c w w' r with
    | .closed => st
    | .coinc f b => coincidence P st f b
    | .deduct f x b => deduce P st f x b
    | .gap f x =>
      let st := define P st f x
      if st.overflow then st else hltWordL P c w w' r fuel st

@[expose] def defStepL (P : Params) (S : Array LScan) (fuel c x : Nat) (st : St) : St :=
  if st.tab.getD (c * P.L + x) 0 == 0 then processDedL P S fuel (define P st c x) else st

@[expose] def defPathL (P : Params) (S : Array LScan) (fuel : Nat) :
    Nat → List Nat → St → St × Nat
  | c, [], st => (st, find st.fwd st.next c)
  | c, x :: w, st =>
    let c := find st.fwd st.next c
    let st := defStepL P S fuel c x st
    let d := st.tab.getD (c * P.L + x) 0
    if d == 0 then (st, c) else defPathL P S fuel d w st

@[expose] def hltHintL (P : Params) (S : Array LScan) (fuel : Nat) (p : List Nat × List Nat)
    (st : St) : St :=
  if p ∈ P.rels then processDedL P S fuel (hltWordL P 1 p.1 p.2 p.1.length (p.1.length + 1) st)
  else st

@[expose] def fillRowLimL (P : Params) (S : Array LScan) (fuel c lim : Nat) : Nat → St → St
  | 0, st => st
  | n + 1, st =>
    if st.overflow || st.fwd.getD c c != c then st
    else
      let x := lim - (n + 1)
      if st.tab.getD (c * P.L + x) 0 == 0 then
        fillRowLimL P S fuel c lim n (processDedL P S fuel (define P st c x))
      else fillRowLimL P S fuel c lim n st

@[expose] def felschLimL (P : Params) (S : Array LScan) (fuel lim : Nat) :
    Nat → Nat → St → St
  | 0, _, st => st
  | n + 1, c, st =>
    if c < st.next && !st.overflow then
      felschLimL P S fuel lim n (c + 1) (fillRowLimL P S fuel c lim lim st)
    else st

@[expose] def Params.restrictL (P : Params) (idx : List Nat) : Params :=
  if idx.isEmpty then P
  else { P with scans :=
    (mkParams P.L P.inv (idx.map fun i => (P.rels.getD i ([], [])).1) []).scans }

@[expose] def pushColumnL (P : Params) (x : Nat) : Nat → St → St
  | 0, st => st
  | c + 1, st =>
    pushColumnL P x c
      (if 0 < c && st.fwd.getD c c == c && st.tab.getD (c * P.L + x) 0 != 0 then
        { st with ded := st.ded.push (c * P.L + x) }
      else st)

@[expose] def runBlockL (P : Params) (cap fuel : Nat) (path : List Nat) (rels : List (List Nat))
    (lim : Nat) (scan : List Nat) (st : St) : St :=
  let Q := P.restrictL scan
  let S := scansLen Q
  let r := defPathL Q S fuel 1 path st
  felschLimL Q S fuel lim (cap + 1) r.2
    (rels.foldl (fun st w => hltHintL Q S fuel (w, invWord Q.inv w) st) r.1)

@[expose] def enumerateHintedL (P : Params) (cap : Nat)
    (blocks : List (List Nat × List (List Nat) × Nat × List Nat)) (late : Nat)
    (lateScan : List Nat) (kCol : Nat) (kScan : List Nat) : St :=
  let fuel := 64 * (cap + 1) * (P.L + 1)
  let S := scansLen P
  let st := blocks.foldl (fun st b => runBlockL P cap fuel b.1 b.2.1 b.2.2.1 b.2.2.2 st)
    (fillSubsL P S fuel P.subs (St.init P.L cap))
  let QL := P.restrictL lateScan
  let st := felschLimL QL (scansLen QL) fuel late (cap + 1) 1 st
  let Q := P.restrictL kScan
  felschL P S fuel (cap + 1) 1 (processDedL Q (scansLen Q) fuel (pushColumnL Q kCol st.next st))

@[expose] def checkHintedL (P : Params)
    (blocks : List (List Nat × List (List Nat) × Nat × List Nat)) (late : Nat)
    (lateScan : List Nat) (kCol : Nat) (kScan : List Nat) (cap n : Nat) : Bool :=
  let st := enumerateHintedL P cap blocks late lateScan kCol kScan
  !st.overflow && st.complete P.L && st.liveCount == n

end CFSG.CosetTable
