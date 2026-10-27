module

public import CFSG.Sporadic.Fi24.OctadData
public import CFSG.Sporadic.FischerOddCore.CommTerm
public import CFSG.Sporadic.FischerOddCore.Fi23WitCheck
public meta import CFSG.Sporadic.Fi24.OctadData
public meta import CFSG.Sporadic.FischerOddCore.CommTerm
public meta import CFSG.Sporadic.FischerOddCore.Fi23WitCheck
public meta import CFSG.Sporadic.Fi24.ExtCert
public import CFSG.Sporadic.Fi24.ExtCert
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi24.Native

@[expose] def fi24GenT (A Ai B Bi : Table) (z : Int) : Table :=
  if z = 1 then A else if z = -1 then Ai else if z = 2 then B else Bi

@[expose] def fi24Fix (P : Table) : Nat := (List.range nPts).countP fun i => ap P i == i

@[expose] def fi24BrayT (R G Gi : Table) (e : Nat) (odd : Bool) : Table :=
  if odd then compT nPts G (powT nPts e (compT nPts R (compT nPts Gi (compT nPts R G))))
  else powT nPts e (compT nPts R (compT nPts Gi (compT nPts R G)))

@[expose] def fi24LeafWords : Array (List Int) := #[
  [-3, 11, 2, 6, 9, 1, -7, 2, -2, 1],
  [11, -10, 1, 1, -5, 3, -10, 9, 2],
  [2, 10, 10, -8, -13, -8, -6, 4, 12, -2],
  [-8, -12, 5, -2, -3, -3, 7, 11, -13, -6, -10, -10],
  [-2, 8, -1, -11, -5, -11, -1, 6],
  [-2, 1, -13, 3, -7, 8, -3, -7, -3, -9, -12, -6]]

@[expose] def fi24LeafExp : Array (Array (Nat × Bool)) := #[
  #[(13, true), (14, true), (13, true), (12, false), (19, true), (8, true)],
  #[(13, true), (16, true), (8, true), (9, false), (14, false), (11, false)],
  #[(14, false), (8, true), (19, true), (9, false), (30, false), (13, false)]]

@[expose] def fi24Term0 : CommTerm :=
  .comm
    (.comm (.comm (.comm (.leaf 5) (.leaf 1)) (.comm (.leaf 4) (.leaf 1)))
      (.comm (.comm (.leaf 1) (.leaf 3)) (.comm (.leaf 5) (.leaf 1))))
    (.comm (.comm (.comm (.leaf 1) (.leaf 4)) (.comm (.leaf 3) (.leaf 2)))
      (.comm (.comm (.leaf 5) (.leaf 0)) (.comm (.leaf 0) (.leaf 2))))

@[expose] def fi24Term1 : CommTerm :=
  .comm
    (.comm (.comm (.comm (.leaf 0) (.leaf 5)) (.comm (.leaf 2) (.leaf 5)))
      (.comm (.comm (.leaf 2) (.leaf 3)) (.comm (.leaf 5) (.leaf 1))))
    (.comm (.comm (.comm (.leaf 4) (.leaf 0)) (.comm (.leaf 1) (.leaf 4)))
      (.comm (.comm (.leaf 2) (.leaf 1)) (.comm (.leaf 5) (.leaf 4))))

@[expose] def fi24Term (c : Nat) : CommTerm := if c = 1 then fi24Term1 else fi24Term0

@[expose] def fi24LeafG (L : Array Table) (tP : Table) (j : Nat) : Table :=
  wordT nPts (letterR L tP) fi24LeafWords[j]!

@[expose] def fi24LeafT (L : Array Table) (tP R : Table) (c j : Nat) : Table :=
  fi24BrayT R (fi24LeafG L tP j) (invT nPts (fi24LeafG L tP j)) ((fi24LeafExp[c]!)[j]!).1
    ((fi24LeafExp[c]!)[j]!).2

@[expose] def fi24CaseOK (L : Array Table) (tP R : Table) (c n : Nat) : Bool :=
  let F := fun j => fi24LeafT L tP R c j
  let W := (fi24Term c).evalT nPts F
  (List.range 6).all (fun j => invOK nPts (fi24LeafG L tP j) (invT nPts (fi24LeafG L tP j)) &&
    compT nPts (F j) R == compT nPts R (F j)) &&
    (fi24Term c).invsOK nPts F &&
    (List.range nPts).countP (fun i => ap R i == i && ap W i == i) == n

@[expose] def fi24WitChecks (O : Enum) : Bool :=
  let L := chainLetters O
  let tA := wordT nPts (letterJ L) normWords[0]!
  let tB := wordT nPts (letterJ L) normWords[1]!
  let tP := tPTable O tA tB
  let M0 := wordT nPts (letterJ L) localWords[0]!
  let M1 := wordT nPts (letterJ L) localWords[1]!
  let gT := fi24GenT M0 (invT nPts M0) M1 (invT nPts M1)
  let D := powT nPts 7 (wordT nPts gT CFSG.Sporadic.Fi23.Native.dLetters)
  let W := wordT nPts gT fi23WordW
  let U2 := compT nPts D (compT nPts M0 (compT nPts D (invT nPts M0)))
  let U3 := compT nPts U2 (compT nPts W (compT nPts D (invT nPts W)))
  tPOK O tA tB tP && invOK nPts M0 (invT nPts M0) && invOK nPts M1 (invT nPts M1) &&
    invOK nPts W (invT nPts W) &&
    fi24Fix D == 3512 && fi24Fix U2 == 3512 && fi24Fix U3 == 504 && fi24Fix tP == 31672 &&
    fi24Fix (compT nPts D tP) == 31672 && fi24Fix (compT nPts U2 tP) == 696 &&
    fi24Fix (compT nPts U3 tP) == 696 &&
    fi24CaseOK L tP U3 0 1 && fi24CaseOK L tP (compT nPts U2 tP) 1 4 &&
    fi24CaseOK L tP (compT nPts U3 tP) 2 4

end CFSG.Sporadic.FischerOddCore
