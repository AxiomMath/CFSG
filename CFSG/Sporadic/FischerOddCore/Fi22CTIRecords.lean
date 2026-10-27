module

public import CFSG.Sporadic.FischerOddCore.Fi24R2Data

public section

namespace CFSG.Sporadic.FischerOddCore

@[expose] def ctiParText : String := include_str "Fi22CtiPar.txt"
@[expose] def ctiLabText : String := include_str "Fi22CtiLab.txt"
@[expose] def ctiNxtText : String := include_str "Fi22CtiNxt.txt"
@[expose] def ctiCidsText : String := include_str "Fi22CtiCid.txt"
@[expose] def ctiRepsText : String := include_str "Fi22CtiReps.txt"
@[expose] def ctiZiText : String := include_str "Fi22CtiZi.txt"
@[expose] def ctiS5Text : String := include_str "Fi22CtiS5.txt"

@[expose] def ctiPar : Array Nat := hexNums 3 ctiParText
@[expose] def ctiLab : Array Nat := hexNums 1 ctiLabText
@[expose] def ctiNxt : Array Nat := hexNums 3 ctiNxtText
@[expose] def ctiCids : Array Nat := hexNums 3 ctiCidsText
@[expose] def ctiReps : Array Nat := hexNums 3 ctiRepsText
@[expose] def ctiZi : Array Nat := hexNums 3 ctiZiText

@[expose] def ctiS5 : Array (Array Nat) := rowsOf 512 (hexNums 3 ctiS5Text)

@[expose] def ctiB5 : Array Nat := #[18, 32, 2]

@[expose] def ctiW5 : Array (List Int) :=
  #[[], [], [], [], [], [], [], [], [], [-9, 7, 2], [-2, -3, 10, 2], [-5, 11, -10, -5, -3, 9, 5, 6]]

end CFSG.Sporadic.FischerOddCore

end
