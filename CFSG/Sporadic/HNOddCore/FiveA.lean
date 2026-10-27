module

public import CFSG.Sporadic.HNOddCore.FiveCheck
public import CFSG.Sporadic.HNOddCore.OrbitX
public import CFSG.Sporadic.HNOddCore.InvFix
public import CFSG.Sporadic.HNSchreier.FALocal
public import Certificates.Certificate2085

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

theorem fFixed_length : FAData.fFixed.length = 50 := by
  decide +kernel

theorem iSmall_size : FAData.iSmall.size = 6 := by
  decide +kernel

theorem a6Small_size : FAData.a6Small.size = 4 := by
  decide +kernel

theorem iSmall_lt : ∀ s < 6, ∀ t < 50, (FAData.iSmall[s]!).getD t 0 < 50 := by
  decide +kernel

theorem a6Small_lt : ∀ s < 4, ∀ t < 50, (FAData.a6Small[s]!).getD t 0 < 50 := by
  decide +kernel

theorem fFixed_lt : ∀ t < 50, FAData.fFixed.getD t 0 < nPts := by
  decide +kernel

theorem fFixed_inj : ∀ s < 50, ∀ t < 50, FAData.fFixed.getD s 0 = FAData.fFixed.getD t 0 → s = t := by
  decide +kernel

theorem toArray_getElem! (l : List ℕ) (i : ℕ) : l.toArray[i]! = l.getD i 0 := by
  rw [List.getElem!_toArray, List.getD_eq_getElem?_getD, getElem!_def]
  cases l[i]? <;> rfl

end CFSG.Sporadic.HNOddCore
