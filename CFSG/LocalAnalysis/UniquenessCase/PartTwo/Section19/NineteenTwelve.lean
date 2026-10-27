module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NotThinShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NOfUniqueShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NOfUniqueShapesSzSp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.ComponentClassification.CatLeafProof CFSG.Blueprint
open CFSG.Blueprint (LieModel)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem nineteen_twelve_of_le_conjClosure (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (hmore : P17_42_more D (conjClosure D.M L) (S17.nOf L))
    {E : Subgroup G} (hEA : E ≤ A) (hEX : E ≤ conjClosure D.M L)
    (hEel : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2) (hr5 : 5 < r) :
    E ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M := by
  have hrprime : r.Prime := h.hr.1
  have hcardA : Nat.card A = (2 ^ S17.nOf L - 1) * (2 ^ S17.nOf L - 1) :=
    card_eq_of_isZModSq h.hAcard
  have hdvd : r ^ 2 ∣ Nat.card A := by
    rw [← hEcard]
    exact Subgroup.card_dvd_of_le hEA
  have hrm : r ∣ 2 ^ S17.nOf L - 1 := by
    have h2 : r ∣ (2 ^ S17.nOf L - 1) ^ 2 := by
      rw [pow_two, ← hcardA]
      exact dvd_trans (by rw [pow_two]; exact dvd_mul_right r r) hdvd
    exact hrprime.dvd_of_dvd_pow h2
  exact (hmore.2 r hrprime hr5 hrm).2 E hEX hEel hEcard

section Certificates


theorem nineteen_twelve_of_X_ne (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (h42 : R17_42At D V₀ V) (hI : IOf D p L = conjClosure D.M L)
    (hne : conjClosure D.M L ≠ L) (hr5 : 5 < r) :
    Concl19_12 D A r := by
  have hnotthin : ¬ F08.Thin8 (conjClosure D.M L) :=
    not_thin8_of_conjClosure_ne h.hyp.hL.1 rfl hne
  have hnotsimple : ¬ IsSimpleGroup (Bar2 (conjClosure D.M L)) := by
    intro hs
    exact hne (conjClosure_eq_self_of_isSimpleGroup_bar2 h.hyp.hL.1 hs)
  have hconcl : Concl17_42 D L (conjClosure D.M L) p := h42 L p h.hyp.hL.1 h.hyp.hp
  have hnot1 : ¬ P17_42_1 D (conjClosure D.M L) := by
    rintro (hthin | ⟨m, hU3⟩ | hL3)
    · exact hnotthin hthin
    · exact hnotsimple (LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU3)
    · exact hnotsimple (LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL3)
  have hnot3 : ¬ P17_42_3 D (conjClosure D.M L) p := by
    rintro ⟨m, hU5, -, -, -, -⟩
    exact hnotsimple (LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU5)
  have hnot4 : ¬ P17_42_4 D (conjClosure D.M L) p := by
    rintro ⟨m, hshape, -, -, -, -, -⟩
    rcases hshape with hSp4 | hG2
    · exact hnotsimple (LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hSp4)
    · exact hnotsimple
        ((CFSG.LieType.Simplicity.fam_g2_simplicity (Bar2 (conjClosure D.M L)) 2 m
          (LieModel.chevalleyExceptionalModel hG2 (by decide))).2)
  have hnot5 : ¬ P17_42_5 D (conjClosure D.M L) p := by
    rintro ⟨m, hU4, -, -, -⟩
    exact hnotsimple (LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU4)
  obtain ⟨m, hmore, hm⟩ : ∃ m : ℕ, P17_42_more D (conjClosure D.M L) m ∧ m = S17.nOf L := by
    rcases hconcl with h1 | h2 | h3 | h4 | h5
    · exact absurd h1 hnot1
    · obtain ⟨m, x, -, -, -, hshape, hmore⟩ := h2
      refine ⟨m, hmore, ?_⟩
      rcases hshape with ⟨hL2, -⟩ | ⟨hSz, -⟩
      · exact (S17.nOf_eq_of_isL2 hL2).symm
      · exact (S17.nOf_eq_of_isSz hSz).symm
    · exact absurd h3 hnot3
    · exact absurd h4 hnot4
    · exact absurd h5 hnot5
  rw [hm] at hmore
  intro E hEA hEel hEcard
  have hEX : E ≤ conjClosure D.M L := hEA.trans (h.hA.trans (le_of_eq hI))
  exact nineteen_twelve_of_le_conjClosure D h hmore hEA hEX hEel hEcard hr5

theorem nineteen_twelve_sp4 (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (h1742 : R17_42At D V₀ V) (hI : IOf D p L = conjClosure D.M L)
    (hSp : IsSp4 (Bar2 (IOf D p L)) (S17.nOf L)) (hr5 : 5 < r) :
    Concl19_12 D A r := by
  have hSp' : IsSp4 (Bar2 (conjClosure D.M L)) (S17.nOf L) := by
    rw [← hI]
    exact hSp
  have hSpL : IsSp4 (Bar2 L) (S17.nOf L) := by
    have hXL : conjClosure D.M L = L :=
      conjClosure_eq_self_of_isSimpleGroup_bar2 h.hyp.hL.1
        (LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hSp')
    rw [hXL] at hSp'
    exact hSp'
  have hnotthin : ¬ F08.Thin8 (conjClosure D.M L) := not_thin8_of_isSp4_bar2 hSp'
  have hconcl : Concl17_42 D L (conjClosure D.M L) p := h1742 L p h.hyp.hL.1 h.hyp.hp
  have hnot1 : ¬ P17_42_1 D (conjClosure D.M L) := by
    rintro (hthin | ⟨m, hU3⟩ | hL3)
    · exact hnotthin hthin
    · exact absurd (lieModel_eq_of_isChar2LieShape hSp' isChar2LieShape_PSp hU3).1
        (by decide)
    · exact absurd (lieModel_eq_of_isChar2LieShape hSp' isChar2LieShape_PSp hL3).1
        (by decide)
  have hnot3 : ¬ P17_42_3 D (conjClosure D.M L) p := by
    rintro ⟨m, hU5, -, -, -, -⟩
    exact absurd (lieModel_eq_of_isChar2LieShape hSp' isChar2LieShape_PSp hU5).1 (by decide)
  have hnot5 : ¬ P17_42_5 D (conjClosure D.M L) p := by
    rintro ⟨m, hU4, -, -, -⟩
    exact absurd (lieModel_eq_of_isChar2LieShape hSp' isChar2LieShape_PSp hU4).1 (by decide)
  obtain ⟨m, hmore, hm⟩ : ∃ m : ℕ, P17_42_more D (conjClosure D.M L) m ∧ m = S17.nOf L := by
    rcases hconcl with h1 | h2 | h3 | h4 | h5
    · exact absurd h1 hnot1
    · obtain ⟨m, x, -, -, -, hshape, hmore⟩ := h2
      rcases hshape with ⟨hL2, -⟩ | ⟨hSz, -⟩
      · exact absurd (lieModel_eq_of_isChar2LieShape hSpL isChar2LieShape_PSp hL2).1
          (by decide)
      · exact absurd (lieModel_eq_of_isChar2LieShape hSpL isChar2LieShape_PSp hSz).1
          (by decide)
    · exact absurd h3 hnot3
    · obtain ⟨m, hshape, -, -, -, -, hmore⟩ := h4
      rcases hshape with hSp4 | hG2
      · exact ⟨m, hmore,
          (lieModel_eq_of_isChar2LieShape hSp4 isChar2LieShape_PSp hSp').2.2.symm⟩
      · exact absurd (lieModel_eq_of_isChar2LieShape hSp' isChar2LieShape_PSp hG2).1
          (by decide)
    · exact absurd h5 hnot5
  rw [hm] at hmore
  intro E hEA hEel hEcard
  have hEX : E ≤ conjClosure D.M L := hEA.trans (h.hA.trans (le_of_eq hI))
  exact nineteen_twelve_of_le_conjClosure D h hmore hEA hEX hEel hEcard hr5

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
