module

public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Defs

public section

namespace CFSG.StandardType.GGFinModel.G5

open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.Assembly CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank

section WeylDict

theorem ggG5_weyl_dict
    {t : StatedLieTag} (ht : GGExcFive t) (f : ℕ) :
    ∃ e : GGWeyl (ggU (absTag t) 6 f).D →* WeylGroup (langTag t),
      ∀ (u : GGWeyl (ggU (absTag t) 6 f).D) (v : Fin (ggU (absTag t) 6 f).D.rank → ℤ),
        ggLangReidx (rank_eq_langTag f ht)
            (weylAction (ggU (absTag t) 6 f).D.isFiniteType u v) =
          e u • ggLangReidx (rank_eq_langTag f ht) v := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact ⟨MonoidHom.id _, fun u v => rfl⟩
  · have hIF : (ggU .E6 6 f).D.isFiniteType = isFiniteType_cartan .E6 :=
      Subsingleton.elim _ _
    cases hIF
    exact ⟨MonoidHom.id _, fun u v => rfl⟩
  · have hIF : (ggU .E7 6 f).D.isFiniteType = isFiniteType_cartan .E7 :=
      Subsingleton.elim _ _
    cases hIF
    exact ⟨MonoidHom.id _, fun u v => rfl⟩
  · exact ⟨MonoidHom.id _, fun u v => rfl⟩
  · have hIF : (ggU .E6 6 f).D.isFiniteType = isFiniteType_cartan .E6 :=
      Subsingleton.elim _ _
    cases hIF
    exact ⟨MonoidHom.id _, fun u v => rfl⟩

end WeylDict

end CFSG.StandardType.GGFinModel.G5
