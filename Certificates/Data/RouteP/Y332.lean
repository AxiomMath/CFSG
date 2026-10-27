module

public import Certificates.Data.RouteP.Objects
public import Certificates.Data.CFSGNative.HN.LevelChain

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

open CFSG.Sporadic.Th.Native CFSG.Sporadic.LevelChain.Native

set_option compiler.extract_closed false

@[expose, irreducible] def coverY332Text : String := include_str "CoverY332.txt"

@[expose] def y332Lines (_ : Unit := ()) : Array (List Int) :=
  slpLines coverStabText ++ slpLines coverY332Text

@[expose] def y332Prog (_ : Unit := ()) : List Instr := compileSLP 2 (y332Lines ())

@[expose] def y332Regs (_ : Unit := ()) : Array Table :=
  mTabs () ++ Array.replicate 111 (idT degree)

@[expose] def y332Run (_ : Unit := ()) : Array Table × Bool :=
  runSLP degree (y332Prog ()) (y332Regs ())

@[expose] def y332Reg (j : Nat) : Nat := if j < 9 then 33 + 2 * j else j + 41

@[expose] def y332Starts : Array Nat := #[0, 9, 19, 29, 39, 49, 59, 69, 71]

@[expose] def y332Base : Array Nat := #[15, 18, 27, 30, 3, 6, 9, 12]

@[expose] def y332Sizes : Array Nat := #[28160, 3159, 288, 7, 12, 5, 4, 3]

@[expose] def y332LevelNums (s : String) : Array (Array Nat) :=
  ((s.splitOn "\n").filter fun l => l.startsWith "LEVEL ").toArray.map fun l =>
    ((l.splitOn " ").filterMap String.toNat?).toArray

@[expose] def y332DataOK (_ : Unit := ()) : Bool :=
  let lv := y332LevelNums coverY332Text
  (y332Lines ()).size == 110 &&
  lineNums coverY332Text "OUT Y332 " 2 == #[34, 36, 38, 40, 42, 44, 46, 48, 50] &&
  lineNums coverY332Text "CHAIN Y332 ORDER " 3 == #[129123503308800] &&
  y332Sizes.foldl (· * ·) 1 == 129123503308800 &&
  lv.size == 8 &&
  allIn 0 8 fun i =>
    lv[i]! == #[i + 1, y332Base[i]! + 1, y332Sizes[i]!] ++
      (Array.range (y332Starts[i + 1]! - y332Starts[i]!)).map fun t =>
        y332Reg (y332Starts[i]! + t) + 1

@[expose] def y332Gens (tabs : Array Table) : Array Table :=
  (Array.range 71).map fun j => tabs[y332Reg j]!

@[expose] def y332Letters (gens : Array Table) : Array Table :=
  Array.ofFn (n := 142) fun i =>
    if i.val % 2 = 0 then gens[i.val / 2]! else invT degree gens[i.val / 2]!

@[expose] def y332NineOK (g9 : Array Table) (ws : List (List Int)) : Bool :=
  g9.size == 9 && allIn 0 9 (fun j => ap g9[j]! 0 == 0 && ap g9[j]! 1479 == 1479) &&
    relatorsOK degree g9 (g9.map (invT degree)) ws

@[expose] def y332TreesOK (letters : Array Table) (trees : Array CFSG.Perm.Native.Tree) : Bool :=
  letters.size == 2 * y332Starts[8]! &&
    allIn 0 71 (fun j => invOK degree letters[2 * j]! letters[2 * j + 1]!) &&
    trees.size == 8 &&
    allIn 0 8 (fun i => CFSG.Perm.Native.treeOK degree y332Base[i]! trees[i]! letters
      (levelLv y332Starts i)) &&
    allIn 1 8 (fun i => allIn y332Starts[i]! y332Starts[i + 1]! fun j =>
      ap letters[2 * j]! y332Base[i - 1]! == y332Base[i - 1]!) &&
    allIn 0 8 (fun i => trees[i]!.pts.size == y332Sizes[i]!)

@[expose] def y332Idx (e : Nat) : Nat :=
  if 51 ≤ e then e - 42 else if 34 ≤ e ∧ e ≤ 50 ∧ e % 2 = 0 then (e - 34) / 2 else 1000

@[expose] def y332Word (l : List Int) : List Int :=
  (pairsOf l).flatMap fun p =>
    List.replicate p.2.natAbs
      (if p.2 < 0 then -((y332Idx p.1 : Int) + 1) else (y332Idx p.1 : Int) + 1)

@[expose] def y332NestOK (gens : Array Table) (lines : Array (List Int)) : Bool :=
  let ginv := gens.map (invT degree)
  allIn 1 8 fun i => allIn y332Starts[i]! y332Starts[i + 1]! fun j =>
    let w := y332Word lines[j + 39]!
    w.all (fun z => decide (y332Starts[i - 1]! + 1 ≤ z.natAbs) &&
      decide (z.natAbs ≤ y332Starts[i]!)) &&
      eqTab degree (wordT degree (letterTab degree gens ginv) w) gens[j]!

@[expose] def y332OKAt (run : Array Table × Bool) (ws : List (List Int)) : Bool :=
  let gens := y332Gens run.1
  let letters := y332Letters gens
  run.2 && run.1.size == 113 && progOK 113 (y332Prog ()) && y332DataOK () && gens.size == 71 &&
    y332NineOK (gens.extract 0 9) ws &&
    y332TreesOK letters (levelTrees degree letters y332Starts y332Base) &&
    y332NestOK gens (y332Lines ())

@[expose] def y332OK (ws : List (List Int)) : Bool := y332OKAt (y332Run ()) ws

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
