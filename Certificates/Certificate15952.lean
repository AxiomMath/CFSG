module

public import CFSG.Timmesfeld.Exceptional.SigmaFarCertificate15952Inputs
public import CFSG.Timmesfeld.Exceptional.SigmaFarDataTriv
public import CFSG.Timmesfeld.Exceptional.SigmaFarDataK24
public import CFSG.Timmesfeld.Exceptional.SigmaFarData7560

public section

namespace CFSG.Timmesfeld.Moufang

open CFSG.Certificates CFSG.Certificates.CosetEnumeration

namespace SigmaFar

open TwoLines

private theorem cert15952_0 :
    derivedOK (2 * 3) (invLetter 3) (codes relsF4) DataTriv.words = true := by
  decide +kernel

private theorem cert15952_1 :
    Exc.coverWalk (2 * 3) DataTriv.fx DataTriv.fy DataTriv.ffi 0
      (([(0, true)] : List (Fin 3 × Bool)).map letterCode) = 0 := by
  decide +kernel

private theorem cert15952_2 :
    derivedOK (2 * 3) (invLetter 3) (codes relsK) DataK24.words = true := by
  decide +kernel

private theorem cert15952_3 :
    codes subK = Data7560.subs := by
  decide +kernel

private theorem cert15952_4 :
    derivedOK (2 * 3) (invLetter 3) (codes relsF3) Data7560.words = true := by
  decide +kernel

private theorem cert15952_5 :
    Exc.coverWalk (2 * 3) Data7560.fx Data7560.fy Data7560.ffi 0 (wU.map letterCode) = 0 := by
  decide +kernel

private theorem cert15952_6 :
    ∀ w ∈ relsF3, signedProd σ w = 1 := by
  decide +kernel

private theorem cert15952_7 :
    signedProd σ wU = 1 := by
  decide +kernel

private theorem cert15952_8 :
    ∀ i j : Fin 24, signedProd τ (w24 i) = signedProd τ (w24 j) → i = j := by
  decide +kernel

private theorem cert15952_9 :
    ∀ i : Fin 24, signedProd τ (w24 i) = 1 → i = 0 := by
  decide +kernel

end SigmaFar

end CFSG.Timmesfeld.Moufang

namespace Certificates

open CFSG.Certificates CFSG.Certificates.CosetEnumeration in
open CFSG.Timmesfeld.Moufang CFSG.Timmesfeld.Moufang.SigmaFar in
theorem certificate15952 : (
    derivedOK (2 * 3) (invLetter 3) (codes relsF4) DataTriv.words = true
  ) ∧ (
    Exc.coverWalk (2 * 3) DataTriv.fx DataTriv.fy DataTriv.ffi 0
      (([(0, true)] : List (Fin 3 × Bool)).map letterCode) = 0
  ) ∧ (
    derivedOK (2 * 3) (invLetter 3) (codes relsK) DataK24.words = true
  ) ∧ (
    codes subK = Data7560.subs
  ) ∧ (
    derivedOK (2 * 3) (invLetter 3) (codes relsF3) Data7560.words = true
  ) ∧ (
    Exc.coverWalk (2 * 3) Data7560.fx Data7560.fy Data7560.ffi 0 (wU.map letterCode) = 0
  ) ∧ (
    ∀ w ∈ relsF3, signedProd σ w = 1
  ) ∧ (
    signedProd σ wU = 1
  ) ∧ (
    ∀ i j : Fin 24, signedProd τ (w24 i) = signedProd τ (w24 j) → i = j
  ) ∧ (
    ∀ i : Fin 24, signedProd τ (w24 i) = 1 → i = 0
  ) := by
  exact ⟨CFSG.Timmesfeld.Moufang.SigmaFar.cert15952_0,
    CFSG.Timmesfeld.Moufang.SigmaFar.cert15952_1, CFSG.Timmesfeld.Moufang.SigmaFar.cert15952_2,
    CFSG.Timmesfeld.Moufang.SigmaFar.cert15952_3, CFSG.Timmesfeld.Moufang.SigmaFar.cert15952_4,
    CFSG.Timmesfeld.Moufang.SigmaFar.cert15952_5, CFSG.Timmesfeld.Moufang.SigmaFar.cert15952_6,
    CFSG.Timmesfeld.Moufang.SigmaFar.cert15952_7, CFSG.Timmesfeld.Moufang.SigmaFar.cert15952_8,
    CFSG.Timmesfeld.Moufang.SigmaFar.cert15952_9⟩

end Certificates
