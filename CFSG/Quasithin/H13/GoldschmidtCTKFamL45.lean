module

public import CFSG.Quasithin.H13.GoldschmidtCTKFamAlt
public import CFSG.Quasithin.H13.GoldschmidtCTKFamL5
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo

public section

namespace CFSG.Quasithin.H13.CTK

theorem not_core_psl_four {S : Type} [Group S]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSL 4 2 1) : ¬ A5Core S := by
  obtain ⟨e⟩ := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff S).1
    (Or.inl ⟨by decide, h⟩)
  exact not_core_alternatingGroup_eight e

theorem exclA5BlockFor_l45 : ExclA5BlockFor fun S _ => SQTKL45Fam S := by
  refine ExclA5BlockFor.of_not_core fun S _ _ hS => ?_
  obtain ⟨n, hn, hm⟩ := hS
  rcases hn with rfl | rfl
  · exact not_core_psl_four hm
  · exact not_core_psl_five hm

end CFSG.Quasithin.H13.CTK
