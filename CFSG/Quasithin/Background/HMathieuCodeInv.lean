
module

public import CFSG.Quasithin.Background.HMathieuCodeInvBase

public import CFSG.Quasithin.Background.HMathieuCodeMask
public import CFSG.Quasithin.Background.HMathieuSyl22
public import CFSG.Quasithin.Background.HMathieuSyl23
public import CFSG.Quasithin.Background.HMathieuSyl24
public import CFSG.Quasithin.Background.HMathieuFacts24
public meta import CFSG.Quasithin.Background.HMathieuCodeMask
public meta import CFSG.Quasithin.Background.HMathieuSyl22
public meta import CFSG.Quasithin.Background.HMathieuSyl23
public meta import CFSG.Quasithin.Background.HMathieuSyl24
public meta import CFSG.Quasithin.Background.HMathieuFacts24
public meta import CFSG.Monster.Code.Basis
public import CFSG.Quasithin.Background.HMathieuCodeInvInputs
public import Certificates.Certificate7062
public import CFSG.Quasithin.Background.HMathieuSyl22Inputs
public import CFSG.Quasithin.Background.HMathieuPT24
public import CFSG.Quasithin.Background.HMathieuPred
public import CFSG.Quasithin.Background.HMathieuSyl23Inputs
public import CFSG.Quasithin.Background.HMathieuSyl24Inputs
public import CFSG.Quasithin.Background.HMathieuAvoid
public import CFSG.Quasithin.Background.HMathieuEnumAll

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code

theorem invC22_ok :
    ∀ s : T22s2.Elem, s ≠ 1 → s * s = 1 →
    (fixMasks 10 (fun q m => actM (matsC22[q.idx]!) m) [s]).length ≤ 2 ^ 7 :=
  fun s => Certificates.certificate7062.1 s

theorem invC23_ok :
    ∀ s : T23s2.Elem, s ≠ 1 → s * s = 1 →
    (fixMasks 11 (fun q m => actM (matsC23[q.idx]!) m) [s]).length = 2 ^ 7 :=
  fun s => Certificates.certificate7062.2.1 s

theorem invC24_ok :
    ∀ s : T24s2.Elem, s ≠ 1 → s * s = 1 →
    (fixMasks 11 (fun q m => actM (matsC24[q.idx]!) m) [s]).length ≤ 2 ^ 7 :=
  fun s => Certificates.certificate7062.2.2.1 s

theorem invArr_ok :
    inAutOK inv23Arr = true ∧ (∀ i < 24, inv23Arr[inv23Arr[i]!]! = i) ∧
    inv23Arr[0]! = 0 ∧ inv23Arr[1]! ≠ 1 ∧
    ((List.range (2 ^ 11)).filter fun m => act11 inv23Arr m == m).length = 2 ^ 7 ∧
    ((List.range (2 ^ 11)).filter fun m => actC11 inv23Arr m == m).length = 2 ^ 7 ∧
    ((List.range (2 ^ 11)).filter fun m => actC11 inv24Arr m == m).length = 2 ^ 7 :=
  Certificates.certificate7062.2.2.2

end CFSG.Quasithin.H.Mathieu
