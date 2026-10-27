module

public import CFSG.Quasithin.Background.P4InspSpBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyEvenSymplectic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace G11

namespace P4InspSp

theorem p4inspsp_isSQT_of_injective {G G' : Type} [Group G] [Group G'] [Finite G'] (f : G →* G')
    (hf : Function.Injective f) (h : CFSG.IsStronglyQuasithin G') :
    CFSG.IsStronglyQuasithin G := by
  have : Finite G := Finite.of_injective f hf
  rw [CFSG.SectionRank.isStronglyQuasithin_iff] at h ⊢
  intro q hq hq2
  exact (CFSG.SectionRank.pRank_top_le_of_injective hq.one_lt f hf).trans (h q hq hq2)

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

theorem p4inspsp_not_sqt_spSub [Finite U] {f : LinearMap.BilinForm (ZMod 2) U}
    (h : IsSymplectic f) (hd : 6 ≤ Module.finrank (ZMod 2) U) :
    ¬ CFSG.IsStronglyQuasithin ↥(spSub f) := by
  intro hsqt
  have : FiniteDimensional (ZMod 2) U := Module.Finite.of_finite
  have : Finite (GLV U) := p4inspsp_finite_glv
  obtain ⟨m, b, hm, hb⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_symplectic_basis
      f h.1 (p4inspsp_nondeg h)
  have hP := p4inspsp_isSQT_of_injective (p4inspsp_projEquiv b hb).symm.toMonoidHom
    (p4inspsp_projEquiv b hb).symm.injective hsqt
  have := CFSG.QuasithinUnique.Setup.Family.even_symplectic_sqt_le_two (K := ZMod 2) m hP
  omega

end P4InspSp

end G11

end CFSG.Quasithin
