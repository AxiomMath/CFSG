module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.WitCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.Basic
import Certificates.Kernel.HN1408.W441872Glue
import Certificates.Kernel.HN1408.W441872Data
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.BlockCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Iso
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts
import CFSG.Certificates.Kernel.Misc.PermClosSound
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.Enum

public section

namespace Certificates

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.CompatModel in
theorem certificate441872 :
    Nat.card ↥(closure (elemW '' {w | w ∈ witSylow})) = 256 ∧
      closure (elemW '' {w | w ∈ witSylow}) ≤
        P1408 ⊓ centralizer ({elemB} : Set (Equiv.Perm (Fin 1408))) ∧
      ∀ s ∈ closure (elemW '' {w | w ∈ witSylow}), orderOf s = 2 →
        s = elemA ∨ s = elemB ∨ s = elemA * elemB ∨
          ∃ w : ↥P1408, ModelVertex w ∧ (w : Equiv.Perm (Fin 1408)) * s = s * w :=
  CFSG.KD.HN1408.W441872.facts441872

end Certificates
