module

public import CFSG.Sporadic.SuzOddCore.GraphArrays
public import CFSG.Sporadic.SuzOddCore.ArraysCheck
public import Certificates.Data.CFSGNative.Schreier.Refine
public meta import CFSG.Sporadic.SuzOddCore.GraphArrays
public meta import CFSG.Sporadic.SuzOddCore.ArraysCheck
public meta import Certificates.Data.CFSGNative.Schreier.Refine
public import CFSG.Sporadic.SuzOddCore.GraphArraysCheckInputs
public import Certificates.Certificate2295

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem graphArrays_check :
    permOK 22880 outerArr = true ∧ (∀ k < 22, permOK 280 (localRun k) = true) ∧
    (∀ r < 9, permOK 22880 (centerFull r) = true ∧ permOK 280 (centerCompact r) = true) ∧
    localDomain.length = 280 ∧ strictIncr localDomain = true ∧ (∀ x ∈ localDomain, x < 22880) ∧
    derivsOK 8 localDerivs = true ∧ localDerivs.size = 14 ∧ lettersOK 10 zWord = true ∧
    (∀ w ∈ sylowQuotWords, lettersOK 14 w = true) ∧
    (∀ w ∈ normalizingSiftWords, ∀ v ∈ w, lettersOK 10 v = true) ∧
    (∀ w ∈ normWords, lettersOK 8 w = true) ∧
    matHeader suzd2F3r64aM1Text = [1, 3, 64, 64] ∧ (matDigits suzd2F3r64aM1Text).length = 4096 ∧
    (∀ c ∈ matDigits suzd2F3r64aM1Text, c = '0' ∨ c = '1' ∨ c = '2') :=
  Certificates.certificate2295

end CFSG.Sporadic.SuzOddCore
