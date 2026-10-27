module

public import Certificates.Data.CFSGNative.CosetTable.Enum

public noncomputable section

namespace CFSG.CosetTable

structure WStore where
  n : Nat
  t : Nat

@[expose] def WStore.get (b : WStore) (i : Nat) : Nat :=
  if i < b.n then (b.t >>> (64 + 32 * i)) % 2 ^ 32 else 0

@[expose] def WStore.mix (s i v : Nat) : Nat :=
  (s * 6364136223846793005 + i * 1442695040888963407 + v + 1) % 2 ^ 64

@[expose] def WStore.set (b : WStore) (i v : Nat) : WStore :=
  if i < b.n then
    { n := b.n,
      t := b.t ^^^ (((b.t >>> (64 + 32 * i)) % 2 ^ 32 ^^^ v % 2 ^ 32) <<< (64 + 32 * i)) ^^^
        (b.t % 2 ^ 64 ^^^ WStore.mix (b.t % 2 ^ 64) i v) }
  else b

@[expose] def WStore.getL (b : WStore) (c : Nat) : Nat := b.get c ^^^ c

@[expose] def WStore.setL (b : WStore) (c v : Nat) : WStore := b.set c (v ^^^ c)

structure StW where
  tab : WStore
  fwd : WStore
  par : WStore
  next : Nat
  ded : Array Nat
  queue : Array Nat
  qi : Nat
  overflow : Bool

@[expose] def StW.init (L cap : Nat) : StW where
  tab := ⟨(cap + 1) * L, 1⟩
  fwd := ⟨cap + 1, 2⟩
  par := ⟨cap + 1, 3⟩
  next := 2
  ded := #[]
  queue := #[]
  qi := 0
  overflow := false

@[expose] def walkWS (L : Nat) (tab : WStore) : Nat → Nat → Nat → List Nat → Nat × Nat
  | _, k, c, [] => (k, c)
  | 0, k, c, _ :: _ => (k, c)
  | lim + 1, k, c, x :: w =>
    let d := tab.get (c * L + x)
    if d == 0 then (k, c) else walkWS L tab lim (k + 1) d w

@[expose] def findWS (fwd : WStore) : Nat → Nat → Nat
  | 0, c => c
  | fuel + 1, c =>
    let d := fwd.getL c
    if d == c then c else findWS fwd fuel d

@[expose] def mergeW (st : StW) (a b : Nat) : StW :=
  let ra := findWS st.fwd st.next a
  let rb := findWS st.fwd st.next b
  if ra == rb || st.next ≤ ra || st.next ≤ rb then st
  else if ra < rb then
    { st with fwd := st.fwd.setL rb ra, queue := st.queue.push rb }
  else
    { st with fwd := st.fwd.setL ra rb, queue := st.queue.push ra }

@[expose] def coincLetterW (P : Params) (st : StW) (g x : Nat) : StW :=
  let d := st.tab.get (g * P.L + x)
  if d == 0 then st else
  let ix := P.inv.getD x 0
  let st := if st.tab.get (d * P.L + ix) == g then
      { st with tab := st.tab.set (d * P.L + ix) 0 } else st
  let mu := findWS st.fwd st.next g
  let nu := findWS st.fwd st.next d
  let e := st.tab.get (mu * P.L + x)
  if e != 0 then mergeW st nu e
  else
    let e' := st.tab.get (nu * P.L + ix)
    if e' != 0 then mergeW st mu e'
    else { st with tab := (st.tab.set (mu * P.L + x) nu).set (nu * P.L + ix) mu,
                   ded := st.ded.push (mu * P.L + x) }

@[expose] def coincRowW (P : Params) (g : Nat) : Nat → StW → StW
  | 0, st => st
  | n + 1, st => coincRowW P g n (coincLetterW P st g (P.L - (n + 1)))

@[expose] def coincQueueW (P : Params) : Nat → StW → StW
  | 0, st => st
  | fuel + 1, st =>
    if st.qi < st.queue.size then
      let g := st.queue.getD st.qi 0
      coincQueueW P fuel (coincRowW P g P.L { st with qi := st.qi + 1 })
    else { st with queue := #[], qi := 0 }

@[expose] def coincidenceW (P : Params) (st : StW) (a b : Nat) : StW :=
  coincQueueW P (st.next * (P.L + 1) + 1) (mergeW st a b)

@[expose] def deduceW (P : Params) (st : StW) (f x b : Nat) : StW :=
  if f < st.next && b < st.next && x < P.L then
    { st with tab := (st.tab.set (f * P.L + x) b).set (b * P.L + P.inv.getD x 0) f,
              ded := st.ded.push (f * P.L + x) }
  else st

@[expose] def defineW (P : Params) (st : StW) (a x : Nat) : StW :=
  let b := st.next
  if 0 < a && a < b && x < P.L && b < st.par.n then
    { st with tab := (st.tab.set (a * P.L + x) b).set (b * P.L + P.inv.getD x 0) a,
              par := st.par.set b (a * P.L + x), next := b + 1,
              ded := st.ded.push (a * P.L + x) }
  else { st with overflow := true }

@[expose] def scanWordW (L : Nat) (tab : WStore) (a : Nat) (w w' : List Nat) : Scan :=
  let r := w.length
  let (i, f) := walkWS L tab r 0 a w
  if i == r then (if f == a then .closed else .coinc f a)
  else
    let (j, b) := walkWS L tab (r - i) 0 a w'
    if j == r - i then (if f == b then .closed else .coinc f b)
    else if j + 1 == r - i then .deduct f (w.getD i 0) b
    else .gap f (w.getD i 0)

@[expose] def scanW (P : Params) (st : StW) (a : Nat) (w w' : List Nat) : StW :=
  match scanWordW P.L st.tab a w w' with
  | .closed => st
  | .coinc f b => coincidenceW P st f b
  | .deduct f x b => deduceW P st f x b
  | .gap _ _ => st

@[expose] def scanAllW (P : Params) (a : Nat) : List (List Nat × List Nat) → StW → StW
  | [], st => st
  | p :: ps, st =>
    if st.fwd.getL a == a then scanAllW P a ps (scanW P st a p.1 p.2) else st

@[expose] def processDedW (P : Params) : Nat → StW → StW
  | 0, st => st
  | fuel + 1, st =>
    match st.ded.back? with
    | none => st
    | some e =>
      let st := { st with ded := st.ded.pop }
      let a := e / P.L
      if st.fwd.getL a == a then
        processDedW P fuel (scanAllW P a (P.scans.getD (e % P.L) []) st)
      else processDedW P fuel st

@[expose] def fillWordW (P : Params) (w w' : List Nat) : Nat → StW → StW
  | 0, st => st
  | fuel + 1, st =>
    match scanWordW P.L st.tab 1 w w' with
    | .closed => st
    | .coinc f b => coincidenceW P st f b
    | .deduct f x b => deduceW P st f x b
    | .gap f x =>
      let st := defineW P st f x
      if st.overflow then st else fillWordW P w w' fuel st

@[expose] def fillSubsW (P : Params) (fuel : Nat) : List (List Nat × List Nat) → StW → StW
  | [], st => st
  | p :: ps, st =>
    fillSubsW P fuel ps (processDedW P fuel (fillWordW P p.1 p.2 (p.1.length + 1) st))

@[expose] def fillRowW (P : Params) (fuel c : Nat) : Nat → StW → StW
  | 0, st => st
  | n + 1, st =>
    if st.overflow || st.fwd.getL c != c then st
    else
      let x := P.L - (n + 1)
      if st.tab.get (c * P.L + x) == 0 then
        fillRowW P fuel c n (processDedW P fuel (defineW P st c x))
      else fillRowW P fuel c n st

@[expose] def felschW (P : Params) (fuel : Nat) : Nat → Nat → StW → StW
  | 0, _, st => st
  | n + 1, c, st =>
    if c < st.next && !st.overflow then felschW P fuel n (c + 1) (fillRowW P fuel c P.L st)
    else st

@[expose] def enumerateW (P : Params) (cap : Nat) : StW :=
  let fuel := 64 * (cap + 1) * (P.L + 1)
  felschW P fuel (cap + 1) 1 (fillSubsW P fuel P.subs (StW.init P.L cap))

@[expose] def StW.liveW (st : StW) (c : Nat) : Bool :=
  0 < c && c < st.next && st.fwd.getL c == c

@[expose] def StW.liveCountW (st : StW) : Nat := countBelow st.liveW st.next

@[expose] def StW.completeW (L : Nat) (st : StW) : Bool :=
  st.liveW 1 && allBelow (fun c => !st.liveW c ||
    allBelow (fun x => st.liveW (st.tab.get (c * L + x))) L) st.next

@[expose] def checkW (P : Params) (cap n : Nat) : Bool :=
  let st := enumerateW P cap
  !st.overflow && st.completeW P.L && st.liveCountW == n

@[expose] def insW (a : List Nat) : List (List Nat) → List (List Nat)
  | [] => [a]
  | b :: m => if a.length ≤ b.length then a :: b :: m else b :: insW a m

@[expose] def msortW : List (List Nat) → List (List Nat)
  | [] => []
  | a :: l => insW a (msortW l)

@[expose] def invArrW (m : Nat) : Array Nat :=
  ((List.range (2 * m)).map fun c => cond (Nat.beq (Nat.mod c 2) 0) (Nat.succ c) (Nat.pred c)).toArray

@[expose] def mkParamsW (L : Nat) (inv : Array Nat) (rels subs : List (List Nat)) : Params :=
  let all := msortW (dedup ((rels ++ rels.map (invWord inv)).flatMap rotations))
  { L := L, inv := inv,
    scans := ((List.range L).map fun x =>
      (all.filter fun w => w.head? == some x).map fun w => (w, invWord inv w)).toArray,
    subs := subs.map fun w => (w, invWord inv w),
    rels := rels.map fun w => (w, invWord inv w) }

end CFSG.CosetTable
