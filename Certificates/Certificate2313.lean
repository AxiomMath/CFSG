
module

public import Certificates.Certificate2313Base
public meta import CFSG.Sporadic.ThSchreier.WordsBase
public meta import CFSG.Sporadic.ThSchreier.LocalDataBase
public import CFSG.Certificates.Kernel.Th.SoundnessTsBase

public import CFSG.Sporadic.ThSchreier.LocalOrbitInputs
public meta import CFSG.Sporadic.ThSchreier.WordsBase1
public meta import CFSG.Sporadic.ThSchreier.LocalData
public import CFSG.Certificates.Kernel.Th.SoundnessTs
import Certificates.Kernel.Th.Ts

public section

namespace Certificates

open CertificateChecks.KernelTh

open CFSG CFSG.Sporadic CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Th.Max3 Pointwise

open CertificateChecks.KernelTh

theorem certificate2313 : ((∀ i < 2457, ∀ j < 2457, i < j → localRowNats.getD i 0 ≠ localRowNats.getD j 0) ∧
      localRowNats.getD 0 0 = 0x6accc40834b0cc5bb7315609695cfa8d6f195e2ac39c3b4260e97d31187fa2 ∧
      (∀ i < 2457, localPermX[i]! < 2457 ∧ localPermY[i]! < 2457 ∧
        (frApply (frTable rowsLX) (localRowV4 i)).beq (localRowV4 localPermX[i]!) = true ∧
        (frApply (frTable (mulRows rowsLY rowsLY)) (localRowV4 i)).beq
          (localRowV4 localPermY[i]!) = true)
    )
    ∧ (localTreePts[0]! = 0 ∧ (∀ k < 2457, localTreePts[k]! < 2457) ∧
      (∀ i < 2457, ∃ k < 2457, localTreePts[k]! = i) ∧
      (∀ k < 2457, 1 ≤ k → localTreePar[k]! < k ∧
        ((localTreeLab[k]! = 1 ∧ localPermX[localTreePts[localTreePar[k]!]!]! = localTreePts[k]!) ∨
         (localTreeLab[k]! = 2 ∧ localPermY[localTreePts[localTreePar[k]!]!]! = localTreePts[k]!)))
    )
    ∧ (eqRows (mulRows rowsLX rowsLX) idRows = true ∧ eqRows rowsLX idRows = false ∧
      eqRows (mulRows (mulRows rowsLY rowsLY) rowsLY) idRows = true ∧
      eqRows rowsLY idRows = false ∧
      eqRows (powRows (mulRows rowsLX rowsLY) 21) idRows = true ∧
      eqRows (powRows (mulRows rowsLX rowsLY) 3) idRows = false ∧
      eqRows (powRows (mulRows rowsLX rowsLY) 7) idRows = false ∧
      imageKey (frTable rowsLX) wKeyRow = wKeyRow ∧
      imageKey (frTable (mulRows rowsLY rowsLY)) wKeyRow = wKeyRow
    ) :=
  CFSG.KC.Th.Soundness.ts_sound2313 tsData ts_hA ts_hB ts_hThTs_Lrows ts_hThTs_Lpx ts_hThTs_Lpy
    ts_hThTs_Ltp ts_hThTs_Ltpa ts_hThTs_Ltla ts_ok

end Certificates
