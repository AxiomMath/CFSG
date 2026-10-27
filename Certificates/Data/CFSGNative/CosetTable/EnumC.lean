module

public import Certificates.Data.CFSGNative.CosetTable.Enum

public section

namespace CFSG.CosetTable

@[expose, inline] def getWord (b : ByteArray) (i : Nat) : Nat :=
  if i * 4 + 4 ≤ b.size then
    (b.get! (i * 4)).toNat + 256 * (b.get! (i * 4 + 1)).toNat +
      65536 * (b.get! (i * 4 + 2)).toNat + 16777216 * (b.get! (i * 4 + 3)).toNat
  else 0

@[expose, inline] def setWord (b : ByteArray) (i v : Nat) : ByteArray :=
  if i * 4 + 4 ≤ b.size then
    (((b.set! (i * 4) v.toUInt8).set! (i * 4 + 1) (v / 256).toUInt8).set! (i * 4 + 2)
      (v / 65536).toUInt8).set! (i * 4 + 3) (v / 16777216).toUInt8
  else b

@[expose, inline] def getLink (b : ByteArray) (c : Nat) : Nat := getWord b c ^^^ c

@[expose, inline] def setLink (b : ByteArray) (c v : Nat) : ByteArray := setWord b c (v ^^^ c)

@[expose] def zeroBytes : Nat → ByteArray → ByteArray
  | 0, b => b
  | k + 1, b => zeroBytes k (b.push 0)

@[expose] def zeroWords (n : Nat) : ByteArray :=
  zeroBytes (4 * n) (ByteArray.emptyWithCapacity (4 * n))

structure StC where
  tab : ByteArray
  fwd : ByteArray
  par : ByteArray
  next : Nat
  ded : Array Nat
  queue : Array Nat
  qi : Nat
  overflow : Bool

@[expose] def StC.init (L cap : Nat) : StC where
  tab := zeroWords ((cap + 1) * L)
  fwd := zeroWords (cap + 1)
  par := zeroWords (cap + 1)
  next := 2
  ded := #[]
  queue := #[]
  qi := 0
  overflow := false

@[expose] def walkC (L : Nat) (tab : ByteArray) : Nat → Nat → Nat → List Nat → Nat × Nat
  | _, k, c, [] => (k, c)
  | 0, k, c, _ :: _ => (k, c)
  | lim + 1, k, c, x :: w =>
    let d := getWord tab (c * L + x)
    if d == 0 then (k, c) else walkC L tab lim (k + 1) d w

@[expose] def findC (fwd : ByteArray) : Nat → Nat → Nat
  | 0, c => c
  | fuel + 1, c =>
    let d := getLink fwd c
    if d == c then c else findC fwd fuel d

@[expose] def mergeC (st : StC) (a b : Nat) : StC :=
  let ra := findC st.fwd st.next a
  let rb := findC st.fwd st.next b
  if ra == rb || st.next ≤ ra || st.next ≤ rb then st
  else if ra < rb then
    { st with fwd := setLink st.fwd rb ra, queue := st.queue.push rb }
  else
    { st with fwd := setLink st.fwd ra rb, queue := st.queue.push ra }

@[expose] def coincLetterC (P : Params) (st : StC) (g x : Nat) : StC :=
  let d := getWord st.tab (g * P.L + x)
  if d == 0 then st else
  let ix := P.inv.getD x 0
  let st := if getWord st.tab (d * P.L + ix) == g then
      { st with tab := setWord st.tab (d * P.L + ix) 0 } else st
  let mu := findC st.fwd st.next g
  let nu := findC st.fwd st.next d
  let e := getWord st.tab (mu * P.L + x)
  if e != 0 then mergeC st nu e
  else
    let e' := getWord st.tab (nu * P.L + ix)
    if e' != 0 then mergeC st mu e'
    else { st with tab := setWord (setWord st.tab (mu * P.L + x) nu) (nu * P.L + ix) mu,
                   ded := st.ded.push (mu * P.L + x) }

@[expose] def coincRowC (P : Params) (g : Nat) : Nat → StC → StC
  | 0, st => st
  | n + 1, st => coincRowC P g n (coincLetterC P st g (P.L - (n + 1)))

@[expose] def coincQueueC (P : Params) : Nat → StC → StC
  | 0, st => st
  | fuel + 1, st =>
    if st.qi < st.queue.size then
      let g := st.queue.getD st.qi 0
      coincQueueC P fuel (coincRowC P g P.L { st with qi := st.qi + 1 })
    else { st with queue := #[], qi := 0 }

@[expose] def coincidenceC (P : Params) (st : StC) (a b : Nat) : StC :=
  coincQueueC P (st.next * (P.L + 1) + 1) (mergeC st a b)

@[expose] def deduceC (P : Params) (st : StC) (f x b : Nat) : StC :=
  if f < st.next && b < st.next && x < P.L then
    { st with tab := setWord (setWord st.tab (f * P.L + x) b) (b * P.L + P.inv.getD x 0) f,
              ded := st.ded.push (f * P.L + x) }
  else st

@[expose] def defineC (P : Params) (st : StC) (a x : Nat) : StC :=
  let b := st.next
  if 0 < a && a < b && x < P.L && b < st.par.size / 4 then
    { st with tab := setWord (setWord st.tab (a * P.L + x) b) (b * P.L + P.inv.getD x 0) a,
              par := setWord st.par b (a * P.L + x), next := b + 1,
              ded := st.ded.push (a * P.L + x) }
  else { st with overflow := true }

@[expose] def scanWordC (L : Nat) (tab : ByteArray) (a : Nat) (w w' : List Nat) : Scan :=
  let r := w.length
  let (i, f) := walkC L tab r 0 a w
  if i == r then (if f == a then .closed else .coinc f a)
  else
    let (j, b) := walkC L tab (r - i) 0 a w'
    if j == r - i then (if f == b then .closed else .coinc f b)
    else if j + 1 == r - i then .deduct f (w.getD i 0) b
    else .gap f (w.getD i 0)

@[expose] def scanC (P : Params) (st : StC) (a : Nat) (w w' : List Nat) : StC :=
  match scanWordC P.L st.tab a w w' with
  | .closed => st
  | .coinc f b => coincidenceC P st f b
  | .deduct f x b => deduceC P st f x b
  | .gap _ _ => st

@[expose] def scanAllC (P : Params) (a : Nat) : List (List Nat × List Nat) → StC → StC
  | [], st => st
  | p :: ps, st =>
    if getLink st.fwd a == a then scanAllC P a ps (scanC P st a p.1 p.2) else st

@[expose] def processDedC (P : Params) : Nat → StC → StC
  | 0, st => st
  | fuel + 1, st =>
    match st.ded.back? with
    | none => st
    | some e =>
      let st := { st with ded := st.ded.pop }
      let a := e / P.L
      if getLink st.fwd a == a then
        processDedC P fuel (scanAllC P a (P.scans.getD (e % P.L) []) st)
      else processDedC P fuel st

@[expose] def fillWordC (P : Params) (w w' : List Nat) : Nat → StC → StC
  | 0, st => st
  | fuel + 1, st =>
    match scanWordC P.L st.tab 1 w w' with
    | .closed => st
    | .coinc f b => coincidenceC P st f b
    | .deduct f x b => deduceC P st f x b
    | .gap f x =>
      let st := defineC P st f x
      if st.overflow then st else fillWordC P w w' fuel st

@[expose] def fillSubsC (P : Params) (fuel : Nat) : List (List Nat × List Nat) → StC → StC
  | [], st => st
  | p :: ps, st =>
    fillSubsC P fuel ps (processDedC P fuel (fillWordC P p.1 p.2 (p.1.length + 1) st))

@[expose] def fillRowC (P : Params) (fuel c : Nat) : Nat → StC → StC
  | 0, st => st
  | n + 1, st =>
    if st.overflow || getLink st.fwd c != c then st
    else
      let x := P.L - (n + 1)
      if getWord st.tab (c * P.L + x) == 0 then
        fillRowC P fuel c n (processDedC P fuel (defineC P st c x))
      else fillRowC P fuel c n st

@[expose] def felschC (P : Params) (fuel : Nat) : Nat → Nat → StC → StC
  | 0, _, st => st
  | n + 1, c, st =>
    if c < st.next && !st.overflow then felschC P fuel n (c + 1) (fillRowC P fuel c P.L st)
    else st

@[expose] def enumerateC (P : Params) (cap : Nat) : StC :=
  let fuel := 64 * (cap + 1) * (P.L + 1)
  felschC P fuel (cap + 1) 1 (fillSubsC P fuel P.subs (StC.init P.L cap))

@[expose] def hltWordC (P : Params) (c : Nat) (w w' : List Nat) : Nat → StC → StC
  | 0, st => st
  | fuel + 1, st =>
    if getLink st.fwd c != c then st else
    match scanWordC P.L st.tab c w w' with
    | .closed => st
    | .coinc f b => coincidenceC P st f b
    | .deduct f x b => deduceC P st f x b
    | .gap f x =>
      let st := defineC P st f x
      if st.overflow then st else hltWordC P c w w' fuel st

@[expose] def hltRowC (P : Params) (fuel c : Nat) : List (List Nat × List Nat) → StC → StC
  | [], st => st
  | p :: ps, st =>
    if st.overflow then st
    else hltRowC P fuel c ps (processDedC P fuel (hltWordC P c p.1 p.2 (p.1.length + 1) st))

@[expose] def hltC (P : Params) (fuel : Nat) : Nat → Nat → StC → StC
  | 0, _, st => st
  | n + 1, c, st =>
    if c < st.next && !st.overflow then hltC P fuel n (c + 1) (hltRowC P fuel c P.rels st) else st

@[expose] def enumerateHLTC (P : Params) (cap : Nat) : StC :=
  let fuel := 64 * (cap + 1) * (P.L + 1)
  felschC P fuel (cap + 1) 1 (hltC P fuel (cap + 1) 1 (fillSubsC P fuel P.subs (StC.init P.L cap)))

@[expose] def StC.liveC (st : StC) (c : Nat) : Bool :=
  0 < c && c < st.next && getLink st.fwd c == c

@[expose] def StC.liveCountC (st : StC) : Nat := countBelow st.liveC st.next

@[expose] def StC.completeC (L : Nat) (st : StC) : Bool :=
  st.liveC 1 && allBelow (fun c => !st.liveC c ||
    allBelow (fun x => st.liveC (getWord st.tab (c * L + x))) L) st.next

@[expose] def checkC (P : Params) (cap n : Nat) : Bool :=
  let st := enumerateC P cap
  !st.overflow && st.completeC P.L && st.liveCountC == n

@[expose] def checkHLTC (P : Params) (cap n : Nat) : Bool :=
  let st := enumerateHLTC P cap
  !st.overflow && st.completeC P.L && st.liveCountC == n

end CFSG.CosetTable
