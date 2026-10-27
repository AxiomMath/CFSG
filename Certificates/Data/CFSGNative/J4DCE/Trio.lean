module

public import Certificates.Data.CFSGNative.YGroups.DCE.EngineB
public import Std.Data.HashMap

public section

namespace CFSG.J4DCE.Native

open CFSG.YGroups.DCE CFSG.Monster.B.Co2.Native

@[expose] def xTab : Array Nat :=
  #[3, 6, 16, 0, 12, 8, 1, 14, 5, 18, 17, 20, 4, 15, 7, 13, 2, 10, 9, 23, 11, 22, 21, 19]

@[expose] def yTab : Array Nat :=
  #[5, 13, 14, 0, 9, 3, 6, 7, 2, 17, 10, 11, 15, 20, 8, 16, 12, 4, 22, 19, 1, 21, 23, 18]

@[expose] def yiTab : Array Nat :=
  #[3, 20, 8, 5, 17, 0, 6, 7, 14, 4, 10, 11, 16, 1, 2, 12, 15, 9, 23, 19, 13, 21, 18, 22]

@[expose] def maskOf (l : List Nat) : Nat := l.foldl (fun acc i => acc ||| (1 <<< i)) 0

@[expose] def sort3 (a b c : Nat) : Nat × Nat × Nat :=
  if a ≤ b then
    if b ≤ c then (a, b, c) else if a ≤ c then (a, c, b) else (c, a, b)
  else
    if a ≤ c then (b, a, c) else if b ≤ c then (b, c, a) else (c, b, a)

@[expose] def baseTrio (_ : Unit := ()) : Nat × Nat × Nat :=
  sort3 (maskOf [4, 6, 8, 14, 15, 16, 18, 21]) (maskOf [1, 2, 5, 7, 9, 12, 13, 22])
    (maskOf [0, 3, 10, 11, 17, 19, 20, 23])

@[expose] def imgMask (σ : ByteArray) (m : Nat) : Nat :=
  (List.range 24).foldl (fun acc i => if m.testBit i then acc ||| (1 <<< bget σ i) else acc) 0

@[expose] def imgMaskTab (t : Array Nat) (m : Nat) : Nat :=
  (List.range 24).foldl (fun acc i => if m.testBit i then acc ||| (1 <<< t[i]!) else acc) 0

@[inline, expose] def key (t : Nat × Nat × Nat) : Nat := (t.1 <<< 48) ||| (t.2.1 <<< 24) ||| t.2.2

@[expose] def imgTrioTab (g : Array Nat) (t : Nat × Nat × Nat) : Nat × Nat × Nat :=
  sort3 (imgMaskTab g t.1) (imgMaskTab g t.2.1) (imgMaskTab g t.2.2)

@[expose] def bfsTrios (fuel : Nat) : Array (Nat × Nat × Nat) := Id.run do
  let mut list : Array (Nat × Nat × Nat) := #[baseTrio]
  let mut seen : Std.HashMap Nat Nat := (∅ : Std.HashMap Nat Nat).insert (key baseTrio) 0
  let mut h := 0
  for _ in [0:fuel] do
    if h < list.size then
      let t := list[h]!
      h := h + 1
      for g in [xTab, yTab] do
        let u := imgTrioTab g t
        if !(seen.contains (key u)) then
          seen := seen.insert (key u) list.size
          list := list.push u
    else
      break
  return list

@[expose] def trioList (_ : Unit := ()) : Array (Nat × Nat × Nat) := bfsTrios 4000

@[expose] def nTrios (_ : Unit := ()) : Nat := 3795

@[expose] def trioMap (_ : Unit := ()) : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := ∅
  for i in [0:trioList.size] do
    m := m.insert (key trioList[i]!) i
  return m

@[expose] def lookup (t : Nat × Nat × Nat) : Nat :=
  match trioMap[key t]? with
  | some q => if q < nTrios && trioList[q]! == t then q else nTrios
  | none => nTrios

@[expose] def act (σ : ByteArray) (p : Nat) : Nat :=
  if p < nTrios then
    let t := trioList[p]!
    lookup (sort3 (imgMask σ t.1) (imgMask σ t.2.1) (imgMask σ t.2.2))
  else nTrios

@[expose] def actAll (σ : ByteArray) : ByteArray := B.u32ofFn nTrios 8 (act σ)

@[expose] def lookupCheck (_ : Unit := ()) : Bool :=
  trioList.size == nTrios && allLt nTrios fun q => lookup trioList[q]! == q

@[expose] def masksCheck (_ : Unit := ()) : Bool :=
  allLt nTrios fun q =>
    let t := trioList[q]!
    decide (t.1 < t.2.1) && decide (t.2.1 < t.2.2) && decide (t.2.2 < 2 ^ 24)

@[expose] def closedCheck (σ : ByteArray) : Bool := allLt nTrios fun p => decide (act σ p < nTrios)

@[expose] def treeCheck (par gen : Array Nat) : Bool :=
  par.size == nTrios && gen.size == nTrios &&
    allLt nTrios fun p => p == 0 || (decide (par[p]! < p) && decide (gen[p]! < 2) &&
      act (bofArr 24 (if gen[p]! == 0 then xTab else yTab)) par[p]! == p)

@[expose] def bfsTree (_ : Unit := ()) : Array Nat × Array Nat := Id.run do
  let mut par : Array Nat := Array.replicate nTrios 0
  let mut gen : Array Nat := Array.replicate nTrios 0
  let mut done : Array Bool := (Array.replicate nTrios false).set! 0 true
  let xb := bofArr 24 xTab
  let yb := bofArr 24 yTab
  for p in [0:nTrios] do
    for gi in [0:2] do
      let q := act (if gi == 0 then xb else yb) p
      if q < nTrios && !done[q]! then
        done := done.set! q true
        par := par.set! q p
        gen := gen.set! q gi
  return (par, gen)

@[expose] def letterBytes (l : Nat) : ByteArray :=
  bofArr 24 (if l < 2 then xTab else if l == 2 then yTab else yiTab)

@[expose] def wordBytes (w : List Nat) : ByteArray :=
  w.foldl (fun acc l => bcomp 24 acc (letterBytes l)) (bid 24)

@[expose] def w1Word : List Nat := [2, 0, 2, 0, 3, 0, 3, 0, 2, 0, 2, 0, 2]

@[expose] def trioChecks (_ : Unit := ()) : Bool :=
  lookupCheck && masksCheck && closedCheck (bofArr 24 xTab) && closedCheck (bofArr 24 yTab) &&
    closedCheck (bofArr 24 yiTab) && treeCheck bfsTree.1 bfsTree.2 &&
    act (bofArr 24 xTab) 0 == 0 && act (wordBytes w1Word) 0 == 0

@[expose] def invWordC (w : List Nat) : List Nat :=
  w.reverse.map fun l => if l % 2 == 0 then l + 1 else l - 1

@[expose] def hWord : List Nat := [2, 0, 3, 0, 2, 0, 3, 0]

@[expose] def cWord (_ : Unit := ()) : List Nat := hWord ++ [2] ++ invWordC hWord

@[expose] def uWord : List Nat := [2, 0, 2, 0, 2, 0, 2]

@[expose] def dWord (_ : Unit := ()) : List Nat := uWord ++ uWord ++ uWord

@[expose] def kWord (_ : Unit := ()) : List Nat :=
  [0, 2, 0, 2, 0, 2] ++ [2] ++ [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] ++ [2]

@[expose] def relWords (_ : Unit := ()) : List (List (List Nat) × List Nat) :=
  [([[], cWord, cWord ++ cWord], []),
    ([cWord, cWord ++ cWord, []], []),
    ([cWord ++ cWord, [], cWord], []),
    ([dWord, dWord ++ invWordC kWord, dWord ++ dWord, dWord ++ dWord ++ invWordC kWord],
      invWordC (dWord ++ dWord)),
    ([dWord ++ invWordC kWord, dWord ++ dWord, dWord ++ dWord ++ invWordC kWord,
      dWord ++ dWord ++ dWord], invWordC (dWord ++ dWord)),
    ([dWord ++ dWord, dWord ++ dWord ++ invWordC kWord, dWord ++ dWord ++ dWord,
      dWord ++ dWord ++ dWord ++ invWordC kWord], invWordC (dWord ++ dWord)),
    ([dWord ++ dWord ++ invWordC kWord, dWord ++ dWord ++ dWord,
      dWord ++ dWord ++ dWord ++ invWordC kWord, dWord ++ dWord ++ dWord ++ dWord],
      invWordC (dWord ++ dWord))]

@[expose] def relEntries (_ : Unit := ()) : Array (Array ByteArray × ByteArray) :=
  (relWords.map fun e => ((e.1.map wordBytes).toArray, wordBytes e.2)).toArray

@[expose] def relPoints (_ : Unit := ()) : List (List Nat) :=
  relWords.map fun e => e.1.map fun w => act (wordBytes w) 0

end CFSG.J4DCE.Native
