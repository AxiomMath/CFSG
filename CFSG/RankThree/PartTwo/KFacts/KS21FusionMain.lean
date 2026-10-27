module

public import CFSG.RankThree.PartTwo.KFacts.KS21FusionL44
public import CFSG.RankThree.PartTwo.KFacts.KS21FusionSp64
public import CFSG.RankThree.PartTwo.KFacts.KS21FusionU58

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS21

theorem terminalFusion : TerminalFusion := by
  intro X _ hX
  rcases hX with he | he | he <;> obtain ⟨e⟩ := he
  · have : Finite X := Finite.of_equiv _ e.symm.toEquiv
    exact elemAbelianFusedIntoJ_of_hasFusionTarget
      (U58.hasFusionTarget_projSU.of_mulEquiv e.symm)
  · have : Finite X := Finite.of_equiv _ e.symm.toEquiv
    exact elemAbelianFusedIntoJ_of_hasFusionTarget
      (L44.hasFusionTarget_projSL.of_mulEquiv e.symm)
  · have : Finite X := Finite.of_equiv _ e.symm.toEquiv
    exact elemAbelianFusedIntoJ_of_hasFusionTarget
      (Sp64.hasFusionTarget_projSp.of_mulEquiv e.symm)

end CFSG.RankThree.PartTwo.KFacts.KS21
