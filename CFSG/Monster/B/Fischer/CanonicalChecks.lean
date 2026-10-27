module

public import CFSG.Monster.B.Fischer.InducedOrbitChecks
public meta import CFSG.Monster.B.Fischer.InducedOrbitChecks
public import Certificates.Certificate3036

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.Code CFSG.Monster.B.TwoA.Census

theorem central_check :
    (∀ n < 22, 22 ≤ indCentral[n]! ∧ indCentral[n]! < 1046 ∧
      red 12 pivK rowK (spreadW (indCentral[n]! - 22) ^^^ 2 ^ n) = 0) ∧
    (∀ u ∈ (wCert 1).pts.toList, indCentral[22 + u]! < 22 ∧
      red 12 pivK rowK (spreadW u ^^^ 2 ^ indCentral[22 + u]!) = 0) ∧
    (∀ u ∈ (wCert 0).pts.toList, indCentral[22 + u]! = 22 + u) ∧
    (∀ u ∈ (wCert 3).pts.toList, indCentral[22 + u]! = 22 + u) ∧
    (∀ u ∈ (wCert 7).pts.toList, indCentral[22 + u]! = 1046 + sigmaFun u) ∧
    (∀ n ∈ (zCert 0).pts.toList, indCentral[1046 + n]! = 1046 + n) ∧
    (∀ n ∈ (zCert 24).pts.toList, 22 ≤ indCentral[1046 + n]! ∧
      indCentral[1046 + n]! - 22 ∈ (wCert 7).pts.toList ∧
      sigmaFun (indCentral[1046 + n]! - 22) = n) ∧
    (∀ n ∈ (zCert 1).pts.toList, indCentral[1046 + n]! = 1046 + tauFun n) :=
  Certificates.certificate3036

theorem red_coord : ∀ x : Fin 22, red 12 pivK rowK (2 ^ (x : ℕ)) ≠ 0 := by decide +kernel

theorem red_coord_pair : ∀ x y : Fin 22, x ≠ y →
    red 12 pivK rowK (2 ^ (x : ℕ) ^^^ 2 ^ (y : ℕ)) ≠ 0 := by
  decide +kernel

theorem popc_coord : ∀ x : Fin 22, popc 22 (2 ^ (x : ℕ)) = 1 := by decide +kernel

end CFSG.Monster.B.Fischer
