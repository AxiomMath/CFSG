module

public import CFSG.Sporadic.HNSchreier.ThreeCheck
public meta import CFSG.Sporadic.HNSchreier.ThreeCheck

public section

namespace CFSG.Sporadic.HNOddCore.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.F5.Native

@[noinline, expose] def bfsPar (n : Nat) (a0 a1 : Array Nat) : Array Nat := Id.run do
  let mut par : Array Nat := Array.replicate n 0
  let mut seen : Array Bool := Array.replicate n false
  seen := seen.set! 0 true
  for i in [0:n] do
    let j := a0[i]!
    if !seen[j]! then
      seen := seen.set! j true
      par := par.set! j (2 * i)
    let k := a1[i]!
    if !seen[k]! then
      seen := seen.set! k true
      par := par.set! k (2 * i + 1)
  return par

@[noinline, expose] def cRecArr (n : Nat) (par cA cB : Array Nat) : Array Nat := Id.run do
  let mut c : Array Nat := Array.replicate n 0
  for j in [1:n] do
    let p := par[j]!
    c := c.set! j ((if p % 2 == 0 then cA else cB)[c[p / 2]!]!)
  return c

@[expose] def cRecStep (a0 a1 par cA cB c : Array Nat) (j : Nat) : Bool :=
  let p := par[j]!
  decide (p / 2 < j) &&
    if p % 2 == 0 then a0[p / 2]! == j && c[j]! == cA[c[p / 2]!]!
    else a1[p / 2]! == j && c[j]! == cB[c[p / 2]!]!

@[noinline, expose] def cRecOK (n : Nat) (a0 a1 par cA cB c : Array Nat) : Bool :=
  c.size == n && c[0]! == 0 && allBelowN n fun j => j == 0 || cRecStep a0 a1 par cA cB c j

@[expose] def conjTabs (n : Nat) (a0 a1 k ki W Wi : Array Nat) : Array Nat × Array Nat :=
  (pcomp n k (pcomp n a0 ki), pcomp n k (pcomp n Wi (pcomp n a1 (pcomp n W ki))))

@[noinline, expose] def cChecksK (n : Nat) (a0 a1 k ki W Wi : Array Nat) : Bool :=
  let cAB := conjTabs n a0 a1 k ki W Wi
  let par := bfsPar n a0 a1
  pisInv n k ki && pisInv n W Wi &&
    cRecOK n a0 a1 par cAB.1 cAB.2 (cRecArr n par cAB.1 cAB.2)

@[noinline, expose] def cChecksDU (n : Nat) (a0 a1 D U : Array Nat) : Bool :=
  let k := pcomp n D (pinvCand n U)
  let W := ppow n (pcomp n a0 (pcomp n a1 a1)) 8
  pisInv n U (pinvCand n U) && cChecksK n a0 a1 k (pinvCand n k) W (pinvCand n W)

@[noinline, expose] def cChecksH (n : Nat) (a0 a1 : Array Nat) (hS : Array (Array Nat)) : Bool :=
  plettersOK 17 LocalData.innerWord &&
    cChecksDU n a0 a1 (pword n hS (pinvs n hS) LocalData.innerWord)
      (seedWordArr n a0 a1 LocalData.outerWord)

@[noinline, expose] def cChecksR (n : Nat) (a0 a1 : Array Nat) (regs : Array (Array Nat)) : Bool :=
  cChecksH n a0 a1 (extendStrong n #[regs[1]!, regs[2]!] LocalData.strongWords)

@[noinline, expose] def cChecks (n : Nat) (a0 a1 : Array Nat) : Bool :=
  cChecksR n a0 a1 (progRegs n (initRegs n a0 a1) Data.subgroupProgram)

@[noinline, expose] def cChecksO (O : VOrbit) : Bool :=
  cChecks hnsData.n (natTab O.alpha) (natTab O.beta)

end CFSG.Sporadic.HNOddCore.Native
