module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs
public import CFSG.LocalAnalysis.StandardType.GGR4PumpDefs
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLOrderKnownAux
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLOrderKnownAux2

public section

namespace CFSG.StandardType.HdRo7C

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggCorank2CDict_of_known (hKG : GGPumpCLabelKnown) (hRig : GGLabelRigidInput) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
      GGResRowAt ggRowCorank2C p J K →
      ∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ →
        GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) → (labJ.tag = .B ∨ labJ.tag = .C) → labJ.n = 1 →
        ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) →
          ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ labJ.rank < lab.rank) ∨
            (lab.tag = .F4 ∧ lab.n = 1 ∧ labJ.rank = 3) := by
  intro G _ _ p B Bs x L D J y K hH _ hrow labJ hlabJ hlabJ_has hlabJ_tag hlabJ_n lab hlab hlab_has
  exact hdRo7CLOKnownAux_assembly hKG hRig G p B Bs x L D J y K hH hrow labJ hlabJ hlabJ_has
    hlabJ_tag hlabJ_n lab hlab hlab_has

end CFSG.StandardType.HdRo7C

end
