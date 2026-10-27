module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.DetDescent
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.DetAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.DetSpor
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.DetOdd
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.DetTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.DetExc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (K33)
open CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route (K33Models K34Models)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (K34odd)

theorem k328det_famPSL :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ n p f : ℕ,
      (n ≤ 4 ∨ ((n = 5 ∨ n = 6 ∨ n = 7) ∧ p ^ f % 3 = 2)) → LieModel S .PSL n p f → K328DetPosIn S →
        LieModel S .PSL 4 2 2 ∨ LieModel S .PSL 6 2 1 ∨ LieModel S .PSL 7 2 1 := by
  intro S _ _ hS n p f hn h hP
  by_cases hp : p = 2
  · subst hp; exact k328det_famPSLTwo S hS n f hn h hP
  · exact (k328det_famPSLOdd S hS n p f hp hn h hP).elim

theorem k328det_famPSU :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ n p f : ℕ,
      (n ≤ 4 ∨ ((n = 5 ∨ n = 6 ∨ n = 7) ∧ p ^ f % 3 = 1)) → LieModel S .PSU n p f → K328DetPosIn S →
        LieModel S .PSU 4 2 3 := by
  intro S _ _ hS n p f hn h hP
  by_cases hp : p = 2
  · subst hp; exact k328det_famPSUTwo S hS n f hn h hP
  · exact (k328det_famPSUOdd S hS n p f hp hn h hP).elim

theorem k328det_famPSp :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ n p f : ℕ,
      (n = 2 ∨ (n = 3 ∧ p ≠ 3)) → LieModel S .PSp n p f → K328DetPosIn S →
        LieModel S .PSp 3 2 2 ∨ LieModel S .PSp 3 2 3 := by
  intro S _ _ hS n p f hn h hP
  by_cases hp : p = 2
  · subst hp; exact k328det_famPSpTwo S hS n f (hn.imp id fun h => h.1) h hP
  · exact (k328det_famPSpOdd S hS n p f hp hn h hP).elim

theorem k328det_famPOmegaMinus :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ p f : ℕ, p ≠ 3 →
      LieModel S .POmegaMinus 4 p f → K328DetPosIn S →
        LieModel S .POmegaMinus 4 2 2 ∨ LieModel S .POmegaMinus 4 2 3 := by
  intro S _ _ hS p f hp3 h hP
  by_cases hp : p = 2
  · subst hp; exact k328det_famPOmegaMinusTwo S hS f h hP
  · exact (k328det_famPOmegaMinusOdd S hS p f hp hp3 h hP).elim

private abbrev K328DetList (S : Type) [Group S] : Prop :=
  LieModel S .PSL 4 2 2 ∨
  LieModel S .PSp 3 2 2 ∨
  LieModel S .POmegaMinus 4 2 2 ∨
  LieModel S .PSL 6 2 1 ∨
  LieModel S .PSL 7 2 1 ∨
  LieModel S .G2 0 2 2 ∨
  LieModel S .trialityD4 0 2 2 ∨
  LieModel S .PSU 4 2 3 ∨
  LieModel S .PSp 3 2 3 ∨
  LieModel S .POmegaMinus 4 2 3 ∨
  LieModel S .G2 0 2 3 ∨
  LieModel S .trialityD4 0 2 3 ∨
  LieModel S .twistedF4 0 2 3

private theorem k328det_goal_of_psl {S : Type} [Group S]
    (h : LieModel S .PSL 4 2 2 ∨ LieModel S .PSL 6 2 1 ∨ LieModel S .PSL 7 2 1) :
    K328DetList S := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

private theorem k328det_goal_of_psu {S : Type} [Group S] (h : LieModel S .PSU 4 2 3) :
    K328DetList S :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))

private theorem k328det_goal_of_psp {S : Type} [Group S]
    (h : LieModel S .PSp 3 2 2 ∨ LieModel S .PSp 3 2 3) : K328DetList S := by
  rcases h with h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))

private theorem k328det_goal_of_omega {S : Type} [Group S]
    (h : LieModel S .POmegaMinus 4 2 2 ∨ LieModel S .POmegaMinus 4 2 3) : K328DetList S := by
  rcases h with h | h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h)))))))))

private theorem k328det_goal_of_g2 {S : Type} [Group S]
    (h : LieModel S .G2 0 2 2 ∨ LieModel S .G2 0 2 3) : K328DetList S := by
  rcases h with h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h))))))))))

private theorem k328det_goal_of_d4 {S : Type} [Group S]
    (h : LieModel S .trialityD4 0 2 2 ∨ LieModel S .trialityD4 0 2 3) : K328DetList S := by
  rcases h with h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl h)))))))))))

private theorem k328det_goal_of_f4 {S : Type} [Group S] (h : LieModel S .twistedF4 0 2 3) :
    K328DetList S :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr h)))))))))))

private theorem k328det_of_k33Models
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 3) (hP : K328DetPosIn S) (h : K33Models S) :
    K328DetList S := by
  rcases h with (h | h) | (h | h) |
      (⟨p, f, -, h⟩ | ⟨p, f, -, h⟩ | ⟨p, f, h⟩ | ⟨p, f, h⟩ | ⟨p, f, h⟩ | ⟨f, h⟩ | h |
        ⟨p, f, -, h⟩ | ⟨p, f, -, h⟩ | ⟨p, f, hm, h⟩ | ⟨p, f, hm, h⟩) | ⟨s, hs, h⟩
  · exact (k328det_altExcluded S hS 7 (by norm_num) h hP).elim
  · exact (k328det_altExcluded S hS 6 (by norm_num) h hP).elim
  · exact k328det_goal_of_psl (k328det_famPSL S hS 3 3 1 (Or.inl (by norm_num)) h hP)
  · exact k328det_goal_of_psu (k328det_famPSU S hS 3 3 1 (Or.inl (by norm_num)) h hP)
  · exact k328det_goal_of_psl (k328det_famPSL S hS 3 p f (Or.inl (by norm_num)) h hP)
  · exact k328det_goal_of_psu (k328det_famPSU S hS 3 p f (Or.inl (by norm_num)) h hP)
  · exact k328det_goal_of_psp (k328det_famPSp S hS 2 p f (Or.inl rfl) h hP)
  · exact k328det_goal_of_g2 (k328det_famG2 S hS h3 p f h hP)
  · exact k328det_goal_of_d4 (k328det_famTriD4 S hS h3 p f h hP)
  · exact k328det_goal_of_f4 (k328det_famTwF4 S hS f h hP)
  · exact (k328det_tits_excluded h hP).elim
  · exact k328det_goal_of_psl (k328det_famPSL S hS 4 p f (Or.inl le_rfl) h hP)
  · exact k328det_goal_of_psu (k328det_famPSU S hS 4 p f (Or.inl le_rfl) h hP)
  · exact k328det_goal_of_psl (k328det_famPSL S hS 5 p f (Or.inr ⟨Or.inl rfl, hm⟩) h hP)
  · exact k328det_goal_of_psu (k328det_famPSU S hS 5 p f (Or.inr ⟨Or.inl rfl, hm⟩) h hP)
  · exact (k328det_spor_excluded hS hs h hP).elim

private theorem k328det_of_k34Models
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hP : K328DetPosIn S) (h : K34Models S) : K328DetList S := by
  rcases h with (h | h | h) | (h | h) |
      (⟨p, f, hp, h⟩ | ⟨p, f, hp, h⟩ | ⟨p, f, -, h⟩ | ⟨p, f, -, -, h⟩ | ⟨p, f, hm, h⟩ |
        ⟨p, f, hm, h⟩ | ⟨p, f, hm, h⟩ | ⟨p, f, hm, h⟩ | ⟨p, f, hp, h⟩) | h
  · exact (k328det_altExcluded S hS 9 (by norm_num) h hP).elim
  · exact (k328det_altExcluded S hS 10 (by norm_num) h hP).elim
  · exact (k328det_altExcluded S hS 11 le_rfl h hP).elim
  · exact k328det_goal_of_psl (k328det_famPSL S hS 2 3 3 (Or.inl (by norm_num)) h hP)
  · exact k328det_goal_of_psp (k328det_famPSp S hS 2 3 1 (Or.inl rfl) h hP)
  · exact k328det_goal_of_psp (k328det_famPSp S hS 3 p f (Or.inr ⟨rfl, hp⟩) h hP)
  · exact k328det_goal_of_omega (k328det_famPOmegaMinus S hS p f hp h hP)
  · exact k328det_goal_of_psl (k328det_famPSL S hS 4 p f (Or.inl le_rfl) h hP)
  · exact k328det_goal_of_psu (k328det_famPSU S hS 4 p f (Or.inl le_rfl) h hP)
  · exact k328det_goal_of_psl
      (k328det_famPSL S hS 6 p f (Or.inr ⟨Or.inr (Or.inl rfl), hm⟩) h hP)
  · exact k328det_goal_of_psu
      (k328det_famPSU S hS 6 p f (Or.inr ⟨Or.inr (Or.inl rfl), hm⟩) h hP)
  · exact k328det_goal_of_psl
      (k328det_famPSL S hS 7 p f (Or.inr ⟨Or.inr (Or.inr rfl), hm⟩) h hP)
  · exact k328det_goal_of_psu
      (k328det_famPSU S hS 7 p f (Or.inr ⟨Or.inr (Or.inr rfl), hm⟩) h hP)
  · exact (k328det_famPOmegaOdd S hS p f hp h hP).elim
  · exact (k328det_spor_order_excluded (by simp) h hP).elim

theorem k328det_detection_of_lists
    (hK33 : K33) (hK34 : K34odd) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hc : IsPGroup 3 (Subgroup.center K))
    (hK : CFSG.Open.IsKGroup (K ⧸ Subgroup.center K))
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 3) {Z X : Subgroup K} (hpos : Pos K Z X)
    (hX : X ≠ ⊤) :
    LieModel (K ⧸ Subgroup.center K) .PSL 4 2 2 ∨
    LieModel (K ⧸ Subgroup.center K) .PSp 3 2 2 ∨
    LieModel (K ⧸ Subgroup.center K) .POmegaMinus 4 2 2 ∨
    LieModel (K ⧸ Subgroup.center K) .PSL 6 2 1 ∨
    LieModel (K ⧸ Subgroup.center K) .PSL 7 2 1 ∨
    LieModel (K ⧸ Subgroup.center K) .G2 0 2 2 ∨
    LieModel (K ⧸ Subgroup.center K) .trialityD4 0 2 2 ∨
    LieModel (K ⧸ Subgroup.center K) .PSU 4 2 3 ∨
    LieModel (K ⧸ Subgroup.center K) .PSp 3 2 3 ∨
    LieModel (K ⧸ Subgroup.center K) .POmegaMinus 4 2 3 ∨
    LieModel (K ⧸ Subgroup.center K) .G2 0 2 3 ∨
    LieModel (K ⧸ Subgroup.center K) .trialityD4 0 2 3 ∨
    LieModel (K ⧸ Subgroup.center K) .twistedF4 0 2 3 := by
  obtain ⟨-, hP⟩ := k328det_descend K hq Z X hpos hX
  have hS : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  rcases k328det_centerCases hK34 K hq hc hK h3 Z X hpos hX with hcen | hON
  · obtain ⟨h3S, h33 | h34⟩ := k328det_simpleLists hK33 hK34 K hq hcen hK h3 Z X hpos
    · exact k328det_of_k33Models hS h3S hP h33
    · exact k328det_of_k34Models hS hP h34
  · exact (k328det_not_posIn_of_cent (k328det_sporCentData _ .ONan (by simp) hON.2.2) hP).elim

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
