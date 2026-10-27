module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenInputs

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenPerfect

open CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative

set_option compiler.extract_closed false

@[expose] def sWords : Array (List Nat) := #[
  [40, 31, 31, 40, 39, 39, 39, 39, 39, 40, 31, 34, 39, 34],
  [31, 34, 39, 39, 34, 39, 39, 39, 39, 40, 31],
  [39, 39, 39, 39, 40, 31, 34, 31, 40, 39],
  [31, 34, 39, 39, 34, 31, 31, 31, 31, 34, 34, 39, 34, 39],
  [39, 40, 40, 40, 39],
  [31, 34, 39, 39, 34, 31, 31, 31, 34, 31, 40, 40]]

@[expose] def sIdx : Array (Nat × Nat) := #[(2, 3), (4, 5), (0, 5), (0, 4), (1, 3), (1, 2)]

@[expose] def invReg (r : Nat) : Nat :=
  if r = 31 then 39 else if r = 39 then 31 else if r = 34 then 40 else if r = 40 then 34 else r

@[expose] def invW (w : List Nat) : List Nat := (w.map invReg).reverse

@[expose] def okReg (r : Nat) : Bool := r == 31 || r == 39 || r == 34 || r == 40

@[expose] def perfAt (regs : Array (Array V4)) (Z : Array V4) (i : Nat) : Bool :=
  let w := sWords[i]!
  let j := (sIdx[i]!).1
  let k := (sIdx[i]!).2
  w.all okReg && sWords[j]!.all okReg && sWords[k]!.all okReg &&
    eqRows (mulRows (wordRowsL regs w) Z) (mulRows Z (wordRowsL regs w)) &&
    eqRows (wordRowsL regs w)
      (wordRowsL regs (sWords[j]! ++ sWords[k]! ++ invW sWords[j]! ++ invW sWords[k]!))

@[expose] def thPerfOK : Bool :=
  let regs := slpRows (rowsOf seedA) (rowsOf seedB) 43 prog7
  let Z := mulRows regs[24]! (powRowsN regs[25]! 6)
  eqRows (mulRows regs[39]! regs[31]!) idRows && eqRows (mulRows regs[40]! regs[34]!) idRows &&
    rowsDiffer (wordRowsL regs sWords[0]!) idRows &&
    (List.range 6).all fun i => decide ((sIdx[i]!).1 < 6) && decide ((sIdx[i]!).2 < 6) &&
      perfAt regs Z i

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenPerfect
