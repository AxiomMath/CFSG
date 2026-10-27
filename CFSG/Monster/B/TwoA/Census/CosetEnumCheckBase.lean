
module

public import CFSG.Monster.B.TwoA.Census.CosetEnumBits
public meta import CFSG.Monster.B.TwoA.Census.CosetEnumBits
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Census.CosetCertData
public meta import CFSG.Monster.B.TwoA.Census.MonoCert
public meta import CFSG.Monster.B.Rep4371.GlueDefs
public meta import Certificates.Data.CFSGNative.MonsterB.CosetEnum
public import CFSG.Monster.B.TwoA.Census.CosetEnumCheckInputs

@[expose] public section

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster.B.Rep4371

theorem cosetOrbits_one_length : (cosetOrbits 1).length = 137 := by decide +kernel

theorem classSize_eq : ∀ k < 137, classSize k = if k = 0 ∨ k = 4 then 256 else 512 := by
  decide +kernel

theorem sum_classSize : ∑ k ∈ Finset.range 137, classSize k = 69632 := by decide +kernel

theorem classEnc_succ : ∀ k < 136, classEnc k < classEnc (k + 1) := by decide +kernel

theorem classEnc_zero : classEnc 0 = 0 := by decide +kernel

theorem classEnc_four : classEnc 4 = 63 := by decide +kernel

theorem cosetOrbits_two : (cosetOrbits 2).map OrbitRecord.rep = [734] ∧
    (cosetOrbits 2).map OrbitRecord.size = [8192] := by decide +kernel

end CFSG.Monster.B.TwoA.Census
