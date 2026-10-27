module

public import Certificates.Data.CFSGNative.Fischer.Hyperoval
public import Certificates.Data.CFSGNative.F4.T46Simple
public import Std.Data.HashMap

public section

namespace CFSG.Fischer.Native

open CFSG.F4.Native CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose] def clStep (F : Flags) : Flags :=
  let M := members F
  M.foldl (fun a u => let T := tvTabs[u]!; M.foldl (fun a v => a.set! (ap T v) true) a) F

@[expose] def clIter : Nat → Flags → Flags
  | 0, F => F
  | k + 1, F => clIter k (clStep F)

@[expose] def lamSel (_ : Unit) : Array Nat := #[76, 307, 51, 217, 67]

@[expose] def lamStart (lns : Array (Array Nat)) (j : Nat) : Flags :=
  Array.ofFn (n := 693) fun p => p.val == 0 ||
    (List.range 5).any fun i => p.val == (lns[i]!)[1 + j / 4 ^ i % 4]!

@[noinline, expose] def lamOf (lns : Array (Array Nat)) : Array Flags :=
  Array.ofFn (n := 1024) fun j => clIter 3 (lamStart lns j.val)

@[expose] def lamTab (_ : Unit) : Array Flags := lamOf ((lamSel ()).map (lineC 0))

@[noinline, expose] def lamOK (P : Array Flags) (LT : Array (Array Nat)) (lam : Array Flags) :
    Bool :=
  let p0 := P[0]!
  let sel := lamSel ()
  sel.size == 5 && allIn 0 5 (fun i => sel[i]! < 693 && sel[i]! != 0 && p0[sel[i]!]!) &&
    lam.size == 1024 &&
    allIn 0 1024 fun j =>
      let F := lam[j]!
      F[0]! && allIn 0 693 (fun z => !F[z]! || p0[z]!) &&
        allIn 0 693 fun y => !p0[y]! || y == 0 || LT[y]!.any fun z => z != 0 && F[z]!

@[expose] def gWords (_ : Unit) : Array (List Nat) := Id.run do
  let T := tvTabs
  let mut w : Array (List Nat) := Array.replicate 693 []
  let mut seen : Array Bool := (Array.replicate 693 false).set! 0 true
  let mut queue : Array Nat := #[0]
  for h in [0:693] do
    if h < queue.size then
      let x := queue[h]!
      for k in [0:31] do
        let p := 23 * k
        let y := ap T[p]! x
        if !seen[y]! then
          seen := seen.set! y true
          w := w.set! y (p :: w[x]!)
          queue := queue.push y
    else break
  return w

@[expose] def tvWordTab (w : List Nat) : Table :=
  w.foldr (fun p T => compT 693 tvTabs[p]! T) (idT 693)

@[noinline, expose] def wordInvs (W : Array (List Nat)) : Array Table :=
  Array.ofFn (n := 693) fun x => invT 693 (tvWordTab W[x.val]!)

@[noinline, expose] def wordsOK (W : Array (List Nat)) (gI : Array Table) : Bool :=
  W.size == 693 && gI.size == 693 &&
    allIn 0 693 fun x =>
      let w := W[x]!
      let T := tvWordTab w
      w.all (· < 693) && ap T 0 == x && invOK 693 T gI[x]!

structure HCtx where
  P : Array Flags
  pl : Array (Array Nat)
  lam : Array Flags
  lamIdx : Array (List Nat)
  gI : Array Table

@[expose] def cands (C : HCtx) (x : Nat) (I X : Flags) : List Nat :=
  let g := C.gI[x]!
  let pl := C.pl[x]!
  let A := pl.filterMap fun y => if I[y]! then some (ap g y) else none
  let B := pl.filterMap fun y => if X[y]! then some (ap g y) else none
  let base := match A.find? (· != 0) with
    | some a => C.lamIdx[a]!
    | none => List.range 1024
  base.filter fun j => let L := C.lam[j]!; A.all (fun a => L[a]!) && B.all (fun b => !L[b]!)

@[expose] def extI (C : HCtx) (F : List (Nat × Nat)) (I : Flags) : Flags :=
  F.foldl (fun I e =>
    let g := C.gI[e.1]!
    let L := C.lam[e.2]!
    C.pl[e.1]!.foldl (fun I y => if L[ap g y]! then I.set! y true else I) I) I

@[expose] def extX (C : HCtx) (F : List (Nat × Nat)) (X : Flags) : Flags :=
  F.foldl (fun X e =>
    let g := C.gI[e.1]!
    let L := C.lam[e.2]!
    C.pl[e.1]!.foldl (fun X y => if L[ap g y]! then X else X.set! y true) X) X

@[expose] def pickMin : List (Nat × List Nat) → Option (Nat × List Nat)
  | [] => none
  | c :: cs => match pickMin cs with
    | none => some c
    | some d => if c.2.length ≤ d.2.length then some c else some d

@[expose] def branchAll (rec : Flags → Flags → Option (List Flags)) (C : HCtx) (x : Nat)
    (I X : Flags) : List Nat → Option (List Flags)
  | [] => some []
  | j :: js =>
    match rec (extI C [(x, j)] I) (extX C [(x, j)] X), branchAll rec C x I X js with
    | some a, some b => some (a ++ b)
    | _, _ => none

@[expose] def forcedOf (cs : List (Nat × List Nat)) : List (Nat × Nat) :=
  cs.filterMap fun c => match c.2 with
    | [j] => some (c.1, j)
    | _ => none

@[expose] def hstep (C : HCtx) (rec : Flags → Flags → Option (List Flags)) (I X : Flags) :
    Option (List Flags) :=
  if anyIn 693 (fun p => I[p]! && X[p]!) then some []
  else if allIn 0 693 (fun p => I[p]! || X[p]!) then some [I]
  else
    let xs := filterRange (fun x => I[x]! && C.pl[x]!.any fun y => !(I[y]! || X[y]!)) 693 []
    let cs := xs.map fun x => (x, cands C x I X)
    if cs.any (fun c => c.2.isEmpty) then some []
    else
      let forced := forcedOf cs
      if !forced.isEmpty then rec (extI C forced I) (extX C forced X)
      else match pickMin cs with
        | none => none
        | some d => branchAll rec C d.1 I X d.2

@[expose] def hsearch (C : HCtx) : Nat → Flags → Flags → Option (List Flags)
  | 0, _, _ => none
  | n + 1, I, X => hstep C (hsearch C n) I X

@[inline, expose] def setBitW (a : Array UInt64) (q : Nat) : Array UInt64 :=
  a.modify (q / 64) fun w => w ||| ((1 : UInt64) <<< (q % 64).toUInt64)

@[expose] def packImg (T : Table) (M : List Nat) : Array UInt64 :=
  M.foldl (fun a p => setBitW a (ap T p)) (Array.replicate 11 0)

@[expose] def packList (M : List Nat) : Array UInt64 :=
  M.foldl setBitW (Array.replicate 11 0)

@[noinline, expose] def famIndex (H : Array Flags) : Std.HashMap (Array UInt64) Nat :=
  (List.range H.size).foldl (fun m k => m.insert (packList (members H[k]!)) k) ∅

@[inline, expose] def findIn (ix : Std.HashMap (Array UInt64) Nat) (n : Nat)
    (key : Array UInt64) : Nat := ix.getD key n

@[noinline, expose] def orbitEnum (R : Flags) (gs gi : Array Table) (cap : Nat) :
    Array Flags × Array Nat × Array Nat := Id.run do
  let mut sets : Array Flags := #[R]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut index : Std.HashMap (Array UInt64) Nat :=
    (∅ : Std.HashMap _ _).insert (packList (members R)) 0
  for h in [0:cap] do
    if h < sets.size then
      let M := members sets[h]!
      for l in [0:gs.size] do
        let key := packImg gs[l]! M
        if !index.contains key then
          index := index.insert key sets.size
          sets := sets.push (imgFlags gi[l]! sets[h]!)
          par := par.push h
          lab := lab.push l
    else break
  return (sets, par, lab)

@[expose] def hypGens (_ : Unit) : Array Table := #[t46XT, t46YT]

@[expose] def hypGensInv (_ : Unit) : Array Table := #[t46XT, compT 693 t46YT t46YT]

@[expose] def hypEnum (c : Nat) : Array Flags × Array Nat × Array Nat :=
  orbitEnum (rootFlags c) (hypGens ()) (hypGensInv ()) 1408

@[expose] def hypSets (c : Nat) : Array Flags := (hypEnum c).1

@[noinline, expose] def hypOrbitOK (R : Flags) (gs gi : Array Table)
    (o : Array Flags × Array Nat × Array Nat) (ix : Std.HashMap (Array UInt64) Nat)
    (off : Nat) : Bool :=
  let H := o.1
  let par := o.2.1
  let lab := o.2.2
  gs.size == 2 && gi.size == 2 && invOK 693 gs[0]! gi[0]! && invOK 693 gs[1]! gi[1]! &&
    H.size == 1408 && par.size == 1408 && lab.size == 1408 && H[0]! == R &&
    allIn 0 1408 (fun k => (members H[k]!).length == 126) &&
    allIn 1 1408 (fun k =>
      par[k]! < k && lab[k]! < 2 && H[k]! == imgFlags gi[lab[k]!]! H[par[k]!]!) &&
    allIn 0 1408 fun k =>
      let M := members H[k]!
      allIn 0 2 fun l =>
        let i := findIn ix 4224 (packImg gs[l]! M)
        off ≤ i && i < off + 1408 && H[i - off]! == imgFlags gi[l]! H[k]!

@[noinline, expose] def rootOK (P : Array Flags) (LT : Array (Array Nat)) (R : Flags) : Bool :=
  R.size == 693 &&
    allIn 0 693 (fun x =>
      let px := P[x]!
      allIn 0 693 fun y => !(decide (x < y) && px[y]!) ||
        (let c := (LT[x * 693 + y]!.toList.filter (R[·]!)).length; c == 0 || c == 2)) &&
    (members R).all fun x => let T := tvTabs[x]!; allIn 0 693 fun q => R[q]! == R[ap T q]!

@[noinline, expose] def famOK (H : Array Flags) (ix : Std.HashMap (Array UInt64) Nat) : Bool :=
  H.size == 4224 && allIn 0 4224 fun k => findIn ix 4224 (packList (members H[k]!)) == k

@[noinline, expose] def searchOK (C : HCtx) (H : Array Flags)
    (ix : Std.HashMap (Array UInt64) Nat) (fuel : Nat) : Bool :=
  let p0 := C.P[0]!
  allIn 0 1024 fun j =>
    let L := C.lam[j]!
    match hsearch C fuel L (Array.ofFn (n := 693) fun p => p0[p.val]! && !L[p.val]!) with
    | none => false
    | some R => decide (R.length ≤ 1) && R.all fun F =>
      let i := findIn ix 4224 (packList (members F))
      i < 4224 && H[i]! == F

@[noinline, expose] def mkCtx (P : Array Flags) (W : Array (List Nat)) (lam : Array Flags) :
    HCtx :=
  { P := P, pl := perpLists P, lam := lam,
    lamIdx := Array.ofFn (n := 693) fun p => filterRange (fun j => lam[j]![p.val]!) 1024 [],
    gI := wordInvs W }

@[noinline, expose] def hypChecks (P : Array Flags) (LT : Array (Array Nat))
    (W : Array (List Nat)) (lam : Array Flags) (gs gi : Array Table)
    (o₀ o₁ o₂ : Array Flags × Array Nat × Array Nat) : Bool :=
  let C := mkCtx P W lam
  let H := o₀.1 ++ o₁.1 ++ o₂.1
  let ix := famIndex H
  lamOK P LT lam && wordsOK W C.gI &&
    rootOK P LT (rootFlags 1) && rootOK P LT (rootFlags 2) && rootOK P LT (rootFlags 3) &&
    hypOrbitOK (rootFlags 1) gs gi o₀ ix 0 && hypOrbitOK (rootFlags 2) gs gi o₁ ix 1408 &&
    hypOrbitOK (rootFlags 3) gs gi o₂ ix 2816 && famOK H ix && searchOK C H ix 40

@[expose] def hypCertificate (_ : Unit) : Bool :=
  let P := perpTab ()
  hypChecks P (lineTab P) (gWords ()) (lamTab ()) (hypGens ()) (hypGensInv ()) (hypEnum 1)
    (hypEnum 2) (hypEnum 3)

end CFSG.Fischer.Native
