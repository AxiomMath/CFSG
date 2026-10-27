module

public import CFSG.Sporadic.SuzOddCore.ArraysCheck
public import Certificates.Data.CFSGNative.Schreier.Refine
public import Certificates.Data.CFSGNative.Perm.Chain
public meta import CFSG.Sporadic.SuzOddCore.ArraysCheck
public meta import Certificates.Data.CFSGNative.Schreier.Refine
public meta import Certificates.Data.CFSGNative.Perm.Chain
public import CFSG.Sporadic.SuzOddCore.FamilyCheckInputs
public import Certificates.Certificate2293

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Th.Native

theorem family_check :
    famOK 1782 22880 #[b0Arr, b1Arr] #[certArr 0, certArr 1] suzFam = true ∧
      smallTreeOK = true ∧ (b0Arr.map UInt32.ofNat).size = 1782 ∧
      (∀ i < 1782, (b0Arr[i]!) < 2 ^ 32) ∧ (∀ i < 1782, (b1Arr[i]!) < 2 ^ 32) ∧
      (∀ i < 1782, (invCand 1782 b0Arr)[i]! < 2 ^ 32) ∧
      (∀ i < 1782, (invCand 1782 b1Arr)[i]! < 2 ^ 32) ∧ b0Arr[0]! ≠ 0 ∧
      (invCand 1782 b0Arr).size = 1782 ∧ (invCand 1782 b1Arr).size = 1782 :=
  Certificates.certificate2293

end CFSG.Sporadic.SuzOddCore
