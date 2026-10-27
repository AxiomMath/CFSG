module

public import CFSG.Sporadic.SuzOddCore.Arrays
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.Sporadic.SuzOddCore.Arrays
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.SuzOddCore.ArraysCheckInputs
public import Certificates.Certificate2289

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native

theorem arrays_check :
    (∀ k < 12, permOK 22880 (certArr k) = true) ∧ (∀ k < 14, permOK 1782 (smallArr k) = true) ∧
    mtxHeader suzP1782M1Text = [12, 1, 1782, 1] ∧ (mtxImages suzP1782M1Text).length = 1782 ∧
    mtxHeader suzP1782M2Text = [12, 1, 1782, 1] ∧ (mtxImages suzP1782M2Text).length = 1782 ∧
    mtxHeader suzd2P1782M1Text = [12, 1, 1782, 1] ∧ (mtxImages suzd2P1782M1Text).length = 1782 ∧
    permOK 1782 b0Arr = true ∧ permOK 1782 b1Arr = true ∧ permOK 1782 vArr = true ∧
    permOK 22880 relabelArr = true ∧
    derivsOK 2 certDerivs = true ∧ derivsOK 2 smallDerivs = true ∧
    smallArr 0 = b0Arr ∧ smallArr 1 = b1Arr :=
  Certificates.certificate2289.1

theorem decoders_check :
    b0Arr = mtxArr suzP1782M1Text ∧ b1Arr = mtxArr suzP1782M2Text ∧
    vArr = mtxArr suzd2P1782M1Text ∧
    (∀ k < 12, certArr k = hexTable 4 22880 (22880 * k) certChainText) ∧
    (∀ k < 14, smallArr k = hexTable 3 1782 (1782 * k) smallChainText) :=
  Certificates.certificate2289.2

end CFSG.Sporadic.SuzOddCore
