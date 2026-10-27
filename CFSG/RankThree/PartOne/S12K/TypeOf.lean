module

public import CFSG.RankThree.PartOne.S12K.RigidDef
public import CFSG.RankThree.PartOne.S12K.FixedLayer
import CFSG.RankThree.PartOne.S11d.FixedRes

public section

namespace CFSG.RankThree.PartOne.S12K

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem statedClassicalModel_of_lieModel_of_tag {X : Type} [Group X] {t : StatedLieTag}
    {n p f : ℕ} (ht : t = .PSU ∨ t = .PSp ∨ t = .PSL) (h : LieModel X t n p f) :
    StatedClassicalModel X t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by rcases ht with rfl | rfl | rfl <;> decide)


theorem kf1213Type_of_rigidity (hRig : LieRigidity3) : KF1213Type := by
  intro G _ _ p A c L E ctx b K I X P Q hL hC hI
  have hRq := fixedRes_isQuasisimple hI
  have hKR := kLayer_eq_fixedResidual ctx hL hRq
  obtain ⟨-, -, -, t, n, f, -, hmodI, hmodR⟩ := hI
  subst hKR
  refine ⟨fun g hg hd hm => ?_, fun g hg hd hm => ?_, fun hr => ?_⟩
  · have hK := hL.K_model.1 g hg hd hm
    obtain ⟨rfl, rfl, hf⟩ := (hRig _ t n f hmodR).1 (1 * g) hK
    rw [one_mul] at hf
    subst hf
    exact statedClassicalModel_of_lieModel_of_tag (Or.inl rfl) hmodI
  · have hK := hL.K_model.2.1 g hg hd hm
    obtain ⟨rfl, rfl, hf⟩ := (hRig _ t n f hmodR).2.1 (1 * g) hK
    rw [one_mul] at hf
    subst hf
    exact statedClassicalModel_of_lieModel_of_tag (Or.inr (Or.inl rfl)) hmodI
  · obtain ⟨g, hg, hd, hK⟩ := hL.K_model.2.2 hr
    obtain ⟨rfl, rfl, hf⟩ := (hRig _ t n f hmodR).2.2 (1 * g) hK
    rw [one_mul] at hf
    subst hf
    exact ⟨_, hg, hd, statedClassicalModel_of_lieModel_of_tag (Or.inr (Or.inr rfl)) hmodI⟩

end CFSG.RankThree.PartOne.S12K
