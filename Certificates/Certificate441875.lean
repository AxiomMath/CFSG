module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.Basic
import Certificates.Kernel.HN1408.W441875Glue
import Certificates.Kernel.HN1408.W441875Defs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Iso
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts
import Certificates.Kernel.HN1408.ClsAZFacts

public section

namespace Certificates

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.CompatModel in
theorem certificate441875 : Nat.card ↥P1408 = 177408000 → ∀ a x : ↥P1408, In2A a → a * pZ₁ = pZ₁ * a →
    x * pZ₁ = pZ₁ * x →
      x ∈ closure {y : ↥P1408 | y * pZ₁ = pZ₁ * y ∧ In2A y ∧ orderOf (a * y) ≠ 5} :=
  CFSG.KD.HN1408.W441875.wit5e_modelK

end Certificates
