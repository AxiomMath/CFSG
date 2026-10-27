module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24ClassData
public import CFSG.Monster.B.Co2.PermArr
public import Mathlib.Data.Set.Card
import Certificates.Kernel.G24Cls.C27203
import CFSG.Sporadic.Co1Block.TwoBCheckInputs
meta import CFSG.Sporadic.Co1Block.TwoBData
meta import CFSG.Sporadic.Co1Block.TwoBCheckDefs
meta import CFSG.Sporadic.Co1Block.CentCheck
meta import CFSG.Sporadic.Schreier.TitsBasic
meta import CFSG.Sporadic.Co2Schreier.ThirdCheck
meta import CFSG.Sporadic.Schreier.Co1ChainCheck
meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
meta import Certificates.Data.CFSGNative.Co1Schreier.Base
meta import Certificates.Data.CFSGNative.Co1.Data
meta import Certificates.Data.CFSGNative.Co1.Involutions
meta import Certificates.Data.CFSGNative.Co1.TwoB
meta import Certificates.Data.CFSGNative.HS.SmallF2
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
meta import Certificates.Data.CFSGNative.Schreier.Check
meta import Certificates.Data.CFSGNative.Schreier.Merge
meta import Certificates.Data.CFSGNative.ONSchreier.Compact
import CFSG.Sporadic.Co1Block.TwoBExtraCheckInputs
meta import CFSG.Sporadic.Co1Block.ConjBData
meta import CFSG.Sporadic.Co1.Module.InvData
meta import CFSG.Sporadic.Co1.Module.Forms
meta import CFSG.Sporadic.Co1.Module.Orbits
import CFSG.Sporadic.Schreier.Co1ThreeLocalInputs
import Certificates.Data.CFSGNative.Co1.Data
import Certificates.Certificate10070
import CFSG.Sporadic.Co1.Module.TwoBFrameInputs
import CFSG.Sporadic.Co1Block.TwoBComp

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.G24Aut CFSG.Monster.B.Co2 in
theorem certificate27203 : ∃ tA : Equiv.Perm (Fin 1365), Rep 1365 tAa tA ∧
    tA ∈ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya} ∧ tA * tA = 1 ∧ tA ≠ 1 ∧
    (∀ i < laList.size, ∃ d ∈ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya},
      Rep 1365 laList[i]! (d * tA * d⁻¹)) ∧
    (∀ z, (∃ d ∈ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya}, z = d * tA * d⁻¹) →
      ∃ i < laList.size, Rep 1365 laList[i]! z) ∧
    laList.size = 4095 ∧
    4096 ≤ {z | ∃ d ∈ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya},
      z = d * permOfArr 1365 xa * d⁻¹}.ncard ∧
    (∀ z ∈ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya}, z * z = 1 → z ≠ 1 →
      (∃ d ∈ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya}, d * z * d⁻¹ = tA) ∨
        ∃ d ∈ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya},
          d * z * d⁻¹ = permOfArr 1365 xa) ∧
    rdGens.size = 8 ∧ (∀ j < 8, Rep 1365 rdGens[j]! (permOfArr 1365 rdGens[j]!)) ∧
    Subgroup.closure ((fun j => permOfArr 1365 rdGens[j]!) '' {j | j < 8}) ≤
      Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya} ∧
    Nat.card (Subgroup.closure ((fun j => permOfArr 1365 rdGens[j]!) '' {j | j < 8})) = 4096 ∧
    ∀ i < rdList.size, ∃ w ∈ Subgroup.closure ((fun j => permOfArr 1365 rdGens[j]!) '' {j | j < 8}),
      Rep 1365 rdList[i]! w :=
  KernelG24.Cls27203.classes_ok

end Certificates
