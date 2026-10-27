module

public import CFSG.Sporadic.Schreier.LyCheckR3E

public section

namespace CFSG.Sporadic.LySchreier.Native

open CFSG.Sporadic.Ly.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.He.Native

set_option compiler.extract_closed false

@[expose] def bsTWordsN : List (List Int) :=
  [[2, 2, 12, 12, -12, -2, -2], [-1, 8, 2, 12, -2, -8, 1], [1, 7, 2, 12, -2, -7, -1],
    [3, 7, -1, 12, 1, -7, -3], [-1, 3, 11, 12, -11, -3, 1], [-2, 1, 3, 12, -3, -1, 2],
    [6, -3, -1, 12, 1, 3, -6], [-3, -1, 12, 1, 3], [1, 3, 7, 12, -7, -3, -1]]

@[expose] def bsWfN : List Int := [1, 1, 2, -1, 4, -3, 5, -4, 5, -4, 6, -5]

@[expose] def bsWmN : List Int := [3, -1, 6, -3, 4, -2, 5, -4, 8, -7, 9, -8]

@[expose] def bsVN : List Int := [1, -7, 2, -8, 3, 3, 5, -3, 6, -4, 9, -6]

@[expose] def bsUN : List Int := [1, -7, 2, -8, 3, 3, 5, -3, 10]

@[expose] def bsSwI (i : Nat) : Nat := if i = 6 then 7 else if i = 7 then 6 else i

@[expose] def bsCzM (cs : Array (Mat × Mat)) (j : Nat) : Mat :=
  if j < 12 then (pairAt cs j).1 else matA

@[expose] def bsCzMi (cs : Array (Mat × Mat)) (j : Nat) : Mat :=
  if j < 12 then (pairAt cs j).2 else matA

@[expose] def bsTM (cs : Array (Mat × Mat)) (i : Nat) : Mat :=
  if i < 9 then evalWordM (bsCzM cs) (bsCzMi cs) (bsTWordsN.getD i []) else
    if i = 9 then matA else idM 111

@[expose] def bsTMi (cs : Array (Mat × Mat)) (i : Nat) : Mat :=
  if i < 9 then mulM 5 111 (bsTM cs i) (bsTM cs i) else if i = 9 then matA else idM 111

@[noinline, expose] def bsWordChecks (Ts Tis : Nat → Mat) (mf mg : Mat) : Bool :=
  (List.range 9).all (fun i => mulM 5 111 (mulM 5 111 (Ts i) (Ts i)) (Ts i) == idM 111) &&
    evalWordM Ts Tis bsWfN == mf && mulM 5 111 mg matA == mulM 5 111 mf mg &&
    mulM 5 111 (evalWordM Ts Tis bsWmN) mg == mulM 5 111 mg (evalWordM Ts Tis bsVN) &&
    mulM 5 111 (evalWordM (fun i => Ts (bsSwI i)) (fun i => Tis (bsSwI i)) bsWmN) mg ==
      mulM 5 111 mg (evalWordM Ts Tis bsUN)

@[noinline, expose] def bsChecks (b4 : Mat) (cs : Array (Mat × Mat)) (us : Array Mat) : Bool :=
  let Ta := Array.ofFn (n := 10) fun i => bsTM cs i.val
  let Tia := Array.ofFn (n := 10) fun i => bsTMi cs i.val
  let mf := mulM 5 111 (mulM 5 111 (mulM 5 111 us[2]! us[1]!) us[2]!) us[1]!
  bsWordChecks (fun i => Ta.getD i (idM 111)) (fun i => Tia.getD i (idM 111)) mf
    (r3eGM (r3eHM b4) mf)

@[expose] def bsCertificate (_ : Unit) : Bool :=
  let b4 := powM 5 111 matB 4
  let cs := cStarArr b4
  bsChecks b4 cs (sylowGens cs)

end CFSG.Sporadic.LySchreier.Native
