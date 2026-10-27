module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24AutBase
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutBoundWord
public import CFSG.Monster.B.Co2.PermArr
public import Mathlib.Data.Set.Card
import Certificates.Kernel.G24Cls.C27205
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

open CFSG.EvenSporadicStandard.G24Aut CFSG.Monster.B.Co2 CFSG.EvenSporadicStandard.Induction.AutBound in
theorem certificate27205 : ∃ b : ℕ → Equiv.Perm (Fin 1365), ∃ tests : ℕ → List (List ℕ × ℕ),
    Rep 1365 tAa (b 0) ∧
    (∀ j, ∃ d ∈ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya}, b j = d * b 0 * d⁻¹) ∧
    Subgroup.closure (b '' {j | j < 4}) =
      Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya} ∧
    ∀ i, 1 ≤ i → i < 4 →
      (∀ t ∈ tests i, (∀ l ∈ t.1, l ≤ i) ∧ 0 < t.2 ∧ orderOf (tupleWord b (b i) t.1) = t.2) ∧
      {z | (∃ d ∈ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya}, z = d * b 0 * d⁻¹) ∧
        ∀ t ∈ tests i, orderOf (tupleWord b z t.1) = t.2}.ncard ≤
        if i = 1 then 1024 else if i = 2 then 60 else 2 :=
  KernelG24.Rigid27205.rigid_ok

end Certificates
