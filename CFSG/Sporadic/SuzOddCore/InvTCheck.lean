module

public import CFSG.Sporadic.SuzOddCore.InvGraphCheck
public import CFSG.Sporadic.SuzOddCore.SmallChainCheck
public meta import CFSG.Sporadic.SuzOddCore.InvGraphCheck
public meta import CFSG.Sporadic.SuzOddCore.SmallChainCheck
public import CFSG.Sporadic.SuzOddCore.InvTCheckInputs
public import Certificates.Certificate2302

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem invT_check :
    (∀ i < 4, eqA 1782 (compA 1782 (tArr i) (tArr i)) (idA 1782) = true ∧
      eqA 1782 (tArr i) (idA 1782) = false ∧ fixedCount (tArr i) = invFixedCounts.getD i 0) ∧
    inM (tArr 0) = true ∧ inM (tArr 1) = true ∧ inM (tArr 2) = false ∧ inM (tArr 3) = false ∧
    (∀ i < 4, ∀ k < invFullGenCounts.getD i 0,
      (inM (invFullGenArrs i)[k]! = true ∨ inM (compA 1782 vArr (invFullGenArrs i)[k]!) = true) ∧
      commutesA (invFullGenArrs i)[k]! (tArr i) = true) ∧
    (∀ i < 4, ∃ k < invFullGenCounts.getD i 0, inM (invFullGenArrs i)[k]! = false) ∧
    (∀ i < 4, ∀ k < invInnerGenCounts.getD i 0,
      inM (invInnerGenArrs i)[k]! = true ∧ commutesA (invInnerGenArrs i)[k]! (tArr i) = true) :=
  Certificates.certificate2302

end CFSG.Sporadic.SuzOddCore
