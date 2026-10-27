module

public import Certificates.Data.CFSGNative.CosetTable.EnumC

public section

namespace CFSG.CosetTable

abbrev LScan := List (List Nat × List Nat × Nat)

@[expose] def withLen (ps : List (List Nat × List Nat)) : LScan :=
  ps.map fun p => (p.1, p.2, p.1.length)

@[expose] def scansLen (P : Params) : Array LScan := P.scans.map withLen

@[expose] def scanWordCL (L : Nat) (tab : ByteArray) (a : Nat) (w w' : List Nat) (r : Nat) : Scan :=
  let (i, f) := walkC L tab r 0 a w
  if i == r then (if f == a then .closed else .coinc f a)
  else
    let (j, b) := walkC L tab (r - i) 0 a w'
    if j == r - i then (if f == b then .closed else .coinc f b)
    else if j + 1 == r - i then .deduct f (w.getD i 0) b
    else .gap f (w.getD i 0)

@[expose] def scanCL (P : Params) (st : StC) (a : Nat) (w w' : List Nat) (r : Nat) : StC :=
  match scanWordCL P.L st.tab a w w' r with
  | .closed => st
  | .coinc f b => coincidenceC P st f b
  | .deduct f x b => deduceC P st f x b
  | .gap _ _ => st

@[expose] def scanAllCL (P : Params) (a : Nat) : LScan → StC → StC
  | [], st => st
  | p :: ps, st =>
    if getLink st.fwd a == a then scanAllCL P a ps (scanCL P st a p.1 p.2.1 p.2.2) else st

@[expose] def processDedCL (P : Params) (S : Array LScan) : Nat → StC → StC
  | 0, st => st
  | fuel + 1, st =>
    match st.ded.back? with
    | none => st
    | some e =>
      let st := { st with ded := st.ded.pop }
      let a := e / P.L
      if getLink st.fwd a == a then
        processDedCL P S fuel (scanAllCL P a (S.getD (e % P.L) []) st)
      else processDedCL P S fuel st

@[expose] def fillSubsCL (P : Params) (S : Array LScan) (fuel : Nat) :
    List (List Nat × List Nat) → StC → StC
  | [], st => st
  | p :: ps, st =>
    fillSubsCL P S fuel ps (processDedCL P S fuel (fillWordC P p.1 p.2 (p.1.length + 1) st))

@[expose] def fillRowCL (P : Params) (S : Array LScan) (fuel c : Nat) : Nat → StC → StC
  | 0, st => st
  | n + 1, st =>
    if st.overflow || getLink st.fwd c != c then st
    else
      let x := P.L - (n + 1)
      if getWord st.tab (c * P.L + x) == 0 then
        fillRowCL P S fuel c n (processDedCL P S fuel (defineC P st c x))
      else fillRowCL P S fuel c n st

@[expose] def felschCL (P : Params) (S : Array LScan) (fuel : Nat) : Nat → Nat → StC → StC
  | 0, _, st => st
  | n + 1, c, st =>
    if c < st.next && !st.overflow then felschCL P S fuel n (c + 1) (fillRowCL P S fuel c P.L st)
    else st

@[expose] def enumerateCL (P : Params) (S : Array LScan) (cap : Nat) : StC :=
  let fuel := 64 * (cap + 1) * (P.L + 1)
  felschCL P S fuel (cap + 1) 1 (fillSubsCL P S fuel P.subs (StC.init P.L cap))

@[expose] def hltWordCL (P : Params) (c : Nat) (w w' : List Nat) (r : Nat) : Nat → StC → StC
  | 0, st => st
  | fuel + 1, st =>
    if getLink st.fwd c != c then st else
    match scanWordCL P.L st.tab c w w' r with
    | .closed => st
    | .coinc f b => coincidenceC P st f b
    | .deduct f x b => deduceC P st f x b
    | .gap f x =>
      let st := defineC P st f x
      if st.overflow then st else hltWordCL P c w w' r fuel st

@[expose] def hltRowCL (P : Params) (S : Array LScan) (fuel c : Nat) : LScan → StC → StC
  | [], st => st
  | p :: ps, st =>
    if st.overflow then st
    else hltRowCL P S fuel c ps
      (processDedCL P S fuel (hltWordCL P c p.1 p.2.1 p.2.2 (p.2.2 + 1) st))

@[expose] def hltCL (P : Params) (S : Array LScan) (R : LScan) (fuel : Nat) :
    Nat → Nat → StC → StC
  | 0, _, st => st
  | n + 1, c, st =>
    if c < st.next && !st.overflow then hltCL P S R fuel n (c + 1) (hltRowCL P S fuel c R st)
    else st

@[expose] def enumerateHLTCL (P : Params) (S : Array LScan) (R : LScan) (cap : Nat) : StC :=
  let fuel := 64 * (cap + 1) * (P.L + 1)
  felschCL P S fuel (cap + 1) 1
    (hltCL P S R fuel (cap + 1) 1 (fillSubsCL P S fuel P.subs (StC.init P.L cap)))

@[expose] def checkCL (P : Params) (cap n : Nat) : Bool :=
  let st := enumerateCL P (scansLen P) cap
  !st.overflow && st.completeC P.L && st.liveCountC == n

@[expose] def checkHLTCL (P : Params) (cap n : Nat) : Bool :=
  let st := enumerateHLTCL P (scansLen P) (withLen P.rels) cap
  !st.overflow && st.completeC P.L && st.liveCountC == n

end CFSG.CosetTable
