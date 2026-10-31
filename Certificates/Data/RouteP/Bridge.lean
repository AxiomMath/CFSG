module

public import Certificates.Data.CFSGNative.Th.Tables

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

open CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose, irreducible] def coverGensText : String := include_str "CoverGens.txt"

@[expose, irreducible] def presText : String := include_str "CoverPresentation.txt"

@[expose, irreducible] def bridgeText : String := include_str "CoverBridge.txt"

@[expose, irreducible] def bridgeGensText : String := include_str "CoverBridgeGens.txt"

abbrev degree : Nat := 920808

@[expose] def numLines (s : String) : Array (Array UInt32) := Id.run do
  let b := s.toUTF8
  let mut out : Array (Array UInt32) := #[]
  let mut cur : Array UInt32 := #[]
  let mut num : UInt32 := 0
  let mut inNum := false
  let mut comment := false
  let mut atStart := true
  for i in [0:b.size] do
    let c := b.get! i
    if comment then
      if c == 10 then
        comment := false
        atStart := true
    else if atStart && c == 35 then
      comment := true
    else
      atStart := false
      if c ≥ 48 && c ≤ 57 then
        num := num * 10 + (c - 48).toUInt32
        inNum := true
      else
        if inNum then
          cur := cur.push num
          num := 0
          inNum := false
        if c == 10 then
          if !cur.isEmpty then
            out := out.push cur
            cur := #[]
          atStart := true
  if inNum then
    cur := cur.push num
  if !cur.isEmpty then
    out := out.push cur
  return out

@[expose] def expandRight (pb kap : Array UInt32) : Table :=
  Array.ofFn (n := degree) fun N =>
    UInt32.ofNat (3 * ((pb[N.val / 3]!).toNat - 1) + (N.val % 3 + (kap[N.val / 3]!).toNat) % 3)

@[expose] def mTabs (_ : Unit := ()) : Array Table :=
  let ls := numLines coverGensText
  #[invT degree (expandRight ls[0]! ls[1]!), invT degree (expandRight ls[2]! ls[3]!)]

@[expose] def slpLines (s : String) : Array (List Int) :=
  ((s.splitOn "\n").filter fun l => l.startsWith "L ").toArray.map fun l =>
    ((l.splitOn " ").drop 1).filterMap fun t => if t.isEmpty then none else t.toInt?

@[expose] def pairsOf : List Int → List (Nat × Int)
  | i :: e :: rest => (i.toNat, e) :: pairsOf rest
  | _ => []

@[expose] def powInstrs (s i : Nat) (e : Int) : List Instr :=
  if e = -1 then [.iv i s]
  else if e < 0 then [.iv i s, .pwr (-e).toNat s s]
  else [.pwr e.toNat i s]

@[expose] def lineInstrs (t scratch : Nat) : List (Nat × Int) → List Instr
  | [] => [.pwr 0 t t]
  | (i, e) :: rest =>
    powInstrs t (i - 1) e ++ rest.flatMap fun p =>
      if p.2 = 1 then [.mu t (p.1 - 1) t]
      else powInstrs scratch (p.1 - 1) p.2 ++ [.mu t scratch t]

@[expose] def compileSLP (g : Nat) (ls : Array (List Int)) : List Instr :=
  (List.range ls.size).flatMap fun l => lineInstrs (g + l) (g + ls.size) (pairsOf ls[l]!)

@[expose] def progOK (r : Nat) (prog : List Instr) : Bool :=
  prog.all fun
    | .mu i j k => decide (i < r) && decide (j < r) && decide (k < r)
    | .pwr _ i k => decide (i < r) && decide (k < r)
    | .iv i k => decide (i < r) && decide (k < r)

@[expose] def xTabs (_ : Unit := ()) : Array Table :=
  let ls := slpLines presText ++ slpLines bridgeText
  let regs := mTabs () ++ Array.replicate (ls.size + 1) (idT degree)
  let res := (runSLP degree (compileSLP 2 ls) regs).1
  (Array.range 11).map fun i => res[28 + i]!

@[expose] def zTabs (_ : Unit := ()) : Array Table :=
  let one := idT degree
  let shift : Table :=
    Array.ofFn (n := degree) fun N => UInt32.ofNat (3 * (N.val / 3) + (N.val % 3 + 2) % 3)
  (Array.range 11).map fun k => if k = 10 then shift else one

@[expose] def genTabs (_ : Unit := ()) : Array Table := xTabs () ++ zTabs ()

@[expose] def letterTab (n : Nat) (gs gsInv : Array Table) (l : Int) : Table :=
  if 0 < l ∧ (l - 1).toNat < gs.size then gs[(l - 1).toNat]!
  else if l < 0 ∧ (-l - 1).toNat < gsInv.size then gsInv[(-l - 1).toNat]!
  else idT n

@[expose] def eqTab (n : Nat) (S T : Table) : Bool := allIn 0 n fun i => ap S i == ap T i

@[expose] def permOK (n : Nat) (T : Table) : Bool :=
  let R := invT n T
  allIn 0 n fun i => decide (ap T i < n) && decide (ap R i < n) && ap R (ap T i) == i &&
    ap T (ap R i) == i

@[expose] def tabsOK (n : Nat) (ts : Array Table) : Bool := ts.all (permOK n)

@[expose] def relatorsOK (n : Nat) (gs gsInv : Array Table) (ws : List (List Int)) : Bool :=
  let one := idT n
  ws.all fun w => eqTab n (wordT n (letterTab n gs gsInv) w) one

@[expose] def fixOK (gs : Array Table) : Bool :=
  [0, 1, 2, 3, 4, 5, 6, 7, 9, 10].all fun i => ap gs[i]! 0 == 0

@[expose] def moveOK (gs : Array Table) : Bool := ap gs[21]! 0 != 0

@[expose] def slpOK (n : Nat) (xs ms : Array Table) : Bool :=
  let ls := slpLines bridgeGensText
  let prog := compileSLP 11 ls
  let regs := xs ++ Array.replicate (ls.size + 1) (idT n)
  let res := runSLP n prog regs
  xs.size == 11 && decide (14 < regs.size) && progOK regs.size prog && res.2 && ms.size == 2 &&
    eqTab n res.1[13]! ms[0]! && eqTab n res.1[14]! ms[1]!

@[expose] def treeCheck (n : Nat) (g₁ g₂ : Table) : Bool :=
  let r := localBFS n 0 g₁ g₂
  r.1.size == n && treeOK n n 0 r.1 r.2.1 (ap r.2.2) g₁ g₂

@[expose] def bridgeOKAt (gs ms : Array Table) (ws : List (List Int)) : Bool :=
  gs.size == 22 && ms.size == 2 && tabsOK degree gs && tabsOK degree ms &&
    relatorsOK degree gs (gs.map (invT degree)) ws && fixOK gs && moveOK gs &&
    slpOK degree (gs.extract 0 11) ms && treeCheck degree ms[0]! ms[1]!

@[expose] def bridgeOK (ws : List (List Int)) : Bool := bridgeOKAt (genTabs ()) (mTabs ()) ws

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
