module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34InvolutionGenCheckInputs
public import CFSG.LieType.SeitzGeneration.HeisSmallOfMat
import Certificates.Kernel.U34Orb.Glue
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace Certificates

open CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.KGroups CFSG.LieType.SeitzGeneration.HeisSmall
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 in
theorem certificate745101 :
    (∀ H : Subgroup (unitarySU 2 2 GF16 3),
      (∃ g ∈ H, ofMat ((g : GL (Fin 3) GF16) : Matrix (Fin 3) (Fin 3) GF16) = d1Mat) →
      (∃ g ∈ H, ofMat ((g : GL (Fin 3) GF16) : Matrix (Fin 3) (Fin 3) GF16) = d2Mat) → H = ⊤) ∧
    (∀ H : Subgroup (unitarySU 2 2 GF16 3),
      (∃ g ∈ H, ofMat ((g : GL (Fin 3) GF16) : Matrix (Fin 3) (Fin 3) GF16) = e1Mat) →
      (∃ g ∈ H, ofMat ((g : GL (Fin 3) GF16) : Matrix (Fin 3) (Fin 3) GF16) = e2Mat) → H = ⊤) := CFSG.KD.U34Orb.gen_holds

end Certificates
