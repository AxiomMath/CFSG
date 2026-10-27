module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Main5
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] [Finite G]

theorem uc22m6_j1Nontrivial : uc22p22d_J1Nontrivial := by
  intro X _ hX
  obtain ⟨e⟩ := hX
  have hJ : Nontrivial CFSG.Blueprint.NativeSporadic.J1 :=
    CFSG.Sporadic.J1.isSimpleGroup_J1.toNontrivial
  have hC : Nontrivial (CFSG.Blueprint.NativeSporadic.Carrier TauCeti.SporadicName.J1) := hJ
  exact e.toEquiv.nontrivial

structure Global22b : Prop extends Global22 where
  k147 : K147

end CFSG.LocalAnalysis.UniquenessCase.UC22
