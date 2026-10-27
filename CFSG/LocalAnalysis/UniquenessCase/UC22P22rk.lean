module

public import CFSG.Adapters.LieModelSimple
public import CFSG.LieType.Simplicity.ReeLargeModel
public import CFSG.LieType.Simplicity.TrialityD4
import CFSG.Blueprint.LieModelAPI
import CFSG.LieType.Simplicity.Suzuki

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Assembly.LowTwoRank

section Uncertified

theorem uc22p22r_lieModel_isSimple_classical {X : Type} [Group X] {t : StatedLieTag} {m n : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaMinus) (h : CFSG.Blueprint.LieModel X t m 2 n) :
    IsSimpleGroup X := by
  refine CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags ?_ h
  rcases ht with rfl | rfl | rfl | rfl <;> decide

theorem uc22p22r_lieModel_isSimple_twistedB2 {X : Type} [Group X] {m n : ℕ}
    (h : CFSG.Blueprint.LieModel X .twistedB2 m 2 n) : IsSimpleGroup X :=
  (CFSG.LieType.Simplicity.fam_2b2_simplicity X 2 n (CFSG.Blueprint.LieModel.suzukiModel h).2).2

end Uncertified

section G2


theorem uc22p22r_lieModel_isSimple_G2 {X : Type} [Group X] {m n : ℕ}
    (h : CFSG.Blueprint.LieModel X .G2 m 2 n) : IsSimpleGroup X :=
  (CFSG.LieType.Simplicity.fam_g2_simplicity X 2 n (h.chevalleyExceptionalModel (by decide))).2

end G2

section TrialityD4


theorem uc22p22r_lieModel_isSimple_trialityD4 {X : Type} [Group X] {m n : ℕ}
    (h : CFSG.Blueprint.LieModel X .trialityD4 m 2 n) : IsSimpleGroup X :=
  (CFSG.LieType.Simplicity.fam_3d4_simplicity X 2 n (h.chevalleyExceptionalModel (by decide))).2

end TrialityD4

section TwistedF4


theorem uc22p22r_lieModel_isSimple_twistedF4 {X : Type} [Group X] {m n : ℕ}
    (h : CFSG.Blueprint.LieModel X .twistedF4 m 2 n) : IsSimpleGroup X :=
  (CFSG.LieType.Simplicity.fam_2f4_simplicity X 2 n (h.reeTitsModel (by decide)).2).2

end TwistedF4

section Combined


theorem uc22p22r_lieModel_isSimple {X : Type} [Group X] {t : StatedLieTag} {m n : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaMinus ∨ t = .twistedB2 ∨ t = .G2 ∨
      t = .trialityD4 ∨ t = .twistedF4)
    (h : CFSG.Blueprint.LieModel X t m 2 n) : IsSimpleGroup X := by
  rcases ht with ht | ht | ht | ht | rfl | rfl | rfl | rfl
  · exact uc22p22r_lieModel_isSimple_classical (Or.inl ht) h
  · exact uc22p22r_lieModel_isSimple_classical (Or.inr (Or.inl ht)) h
  · exact uc22p22r_lieModel_isSimple_classical (Or.inr (Or.inr (Or.inl ht))) h
  · exact uc22p22r_lieModel_isSimple_classical (Or.inr (Or.inr (Or.inr ht))) h
  · exact uc22p22r_lieModel_isSimple_twistedB2 h
  · exact uc22p22r_lieModel_isSimple_G2 h
  · exact uc22p22r_lieModel_isSimple_trialityD4 h
  · exact uc22p22r_lieModel_isSimple_twistedF4 h

end Combined

end CFSG.LocalAnalysis.UniquenessCase.UC22
