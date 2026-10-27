module

import CFSG.LieType.Simplicity.TitsBits
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.Ree.Duality
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG.LieType.Simplicity.TitsBits CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree

section SoundI

variable {K : Type} [Field K] [CharP K 2]

theorem finite_adjF [Finite K] : Finite (adjointGroup ReeTag.F4.tag K) := by
  have : Finite (Module.End K (RootModule Tag.F4 K)) := Module.finite_of_finite K
  infer_instance

end SoundI

end CFSG.RankThree.PartTwo.Sec21.FF81.F4
