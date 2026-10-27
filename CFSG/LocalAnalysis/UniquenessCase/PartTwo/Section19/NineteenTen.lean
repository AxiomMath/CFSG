module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.MSubBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.JMEqualFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NOfUniqueShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NOfUniqueShapesSzSp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NotThinShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Bar2Transfer
public import CFSG.Quasithin.H13.A5S1327j
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.ComponentClassification.CatLeafProof CFSG.Blueprint
open CFSG.Assembly.LowTwoRank
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isL2U3Product_of_mulEquiv {X Y : Type} [Group X] [Group Y] {n : ℕ} (e : X ≃* Y)
    (h : IsL2U3Product X n) : IsL2U3Product Y n := by
  obtain ⟨A, B, gA, gB, ⟨f⟩, hA, hB⟩ := h
  exact ⟨A, B, gA, gB, ⟨e.symm.trans f⟩, hA, hB⟩

theorem isL2U3Product_or_isL2Square_of_bar2_equiv {D : Data G} {p n : ℕ} {L : Subgroup G}
    (h : P17_64_2 D p n)
    (he : Nonempty (Bar2 (IOf D p L) ≃* Bar2 (Lp D p))) :
    IsL2U3Product (Bar2 (IOf D p L)) n ∨ IsL2Square (Bar2 (IOf D p L)) n := by
  rcases h with ⟨hsq, -⟩ | ⟨hu3, -⟩
  · obtain ⟨e⟩ := he
    exact Or.inr (IsL2Square.of_mulEquiv e.symm hsq)
  · obtain ⟨e⟩ := he
    exact Or.inl (isL2U3Product_of_mulEquiv e.symm hu3)

section Certificates


private theorem odd_and_cong_of_isSp4_branch {D : Data G} {p : ℕ} {L : Subgroup G}
    (h42 : Concl17_42 D L (conjClosure D.M L) p)
    {m : ℕ} (hXL : conjClosure D.M L = L) (hSp : IsSp4 (Bar2 (conjClosure D.M L)) m) :
    Odd m ∧ (2 : ℤ) ^ m ≡ -1 [ZMOD (p : ℤ)] ∧ evenRank G = 3 := by
  rcases h42 with h1 | h2 | h3 | h4 | h5
  · rcases h1 with hthin | ⟨m', hU3⟩ | hL3
    · exact absurd hthin (not_thin8_of_isSp4_bar2 hSp)
    · exact absurd (lieModel_eq_of_isChar2LieShape hSp isChar2LieShape_PSp hU3).1 (by decide)
    · exact absurd (lieModel_eq_of_isChar2LieShape hSp isChar2LieShape_PSp hL3).1 (by decide)
  · obtain ⟨m', x, -, -, hne, -, -⟩ := h2
    exact absurd hXL hne
  · obtain ⟨m', hU5, -, -, -, -⟩ := h3
    exact absurd (lieModel_eq_of_isChar2LieShape hSp isChar2LieShape_PSp hU5).1 (by decide)
  · obtain ⟨m', hshape, -, hodd, hcong, -, hmore⟩ := h4
    rcases hshape with hSp' | hG2
    · have hm : m' = m :=
        (lieModel_eq_of_isChar2LieShape hSp isChar2LieShape_PSp hSp').2.2
      exact ⟨by rwa [← hm], by rwa [← hm], hmore.1⟩
    · exact absurd (lieModel_eq_of_isChar2LieShape hSp isChar2LieShape_PSp hG2).1 (by decide)
  · obtain ⟨m', hU4, -, -, -⟩ := h5
    exact absurd (lieModel_eq_of_isChar2LieShape hSp isChar2LieShape_PSp hU4).1 (by decide)

private theorem setting1910_alt_two {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h1 : Concl19_1 L)
    {m : ℕ} (hmore : P17_42_more D (conjClosure D.M L) m)
    (hj : jM D p ≠ 4) (hXne : conjClosure D.M L ≠ L)
    (hshape : (IsL2 (Bar2 L) m ∧ (2 : ℤ) ^ m ≡ -1 [ZMOD (p : ℤ)]) ∨
      (IsSz (Bar2 L) m ∧ (2 : ℤ) ^ (2 * m) ≡ -1 [ZMOD (p : ℤ)])) :
    Setting1910 D V₀ V p L := by
  have hI : IOf D p L = conjClosure D.M L := by simp [IOf, hj]
  have hnm : S17.nOf L = m := by
    rcases hshape with ⟨hL2, -⟩ | ⟨hSz, -⟩
    · exact S17.nOf_eq_of_isL2 hL2
    · exact S17.nOf_eq_of_isSz hSz
  have hn2 : 2 < S17.nOf L := by
    rw [hnm]
    rcases hshape with ⟨hL2, -⟩ | ⟨hSz, -⟩
    · have h1m : 1 ≤ m := hL2.admissible.2.1
      have hm1 : m ≠ 1 := by
        intro hm1
        have hadm := hL2.admissible
        simp only [CFSG.Open.StatedLieAdmissible] at hadm
        exact hadm.2.2.2.1 (by norm_num [hm1])
      have hm2 : m ≠ 2 := by
        intro hm2
        exact h1.1 (by rwa [hm2] at hL2)
      omega
    · have h3 : 3 ≤ m := by
        have hadm := hSz.admissible
        simp only [CFSG.Open.StatedLieAdmissible] at hadm
        exact hadm.2.2.2.2.2
      omega
  simp only [Setting1910]
  refine ⟨hmore.1, Or.inr (Or.inl ⟨hI, hXne, hn2, ?_⟩)⟩
  rcases hshape with ⟨hL2, hcong⟩ | ⟨hSz, hcong⟩
  · exact Or.inl ⟨by rwa [hnm], by rwa [hnm]⟩
  · exact Or.inr ⟨by rwa [hnm], by rw [hnm]; exact hcong⟩

private theorem setting1910_alt_one {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp19 D V₀ V p L) (h42 : Concl17_42 D L (conjClosure D.M L) p)
    (hj : jM D p ≠ 4) {m : ℕ} (hSp : IsSp4 (Bar2 (conjClosure D.M L)) m)
    (hswap : SwapsParabolics D.T (conjClosure D.M L)) : Setting1910 D V₀ V p L := by
  have hsX : IsSimpleGroup (Bar2 (conjClosure D.M L)) :=
    LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hSp
  have hXL : conjClosure D.M L = L :=
    conjClosure_eq_self_of_isSimpleGroup_bar2 h.hL.1 hsX
  obtain ⟨hodd, hcong, he⟩ := odd_and_cong_of_isSp4_branch h42 hXL hSp
  have hnm : S17.nOf L = m :=
    S17.nOf_eq_of_isSp4 (hXL ▸ hSp)
  have hI : IOf D p L = conjClosure D.M L := by simp [IOf, hj]
  simp only [Setting1910]
  refine ⟨he, Or.inl ⟨?_, ?_, ?_, ?_⟩⟩
  · have h' := LieModel.of_mulEquiv (QuotientGroup.congr
      (CFSG.pCore 2 ↥(IOf D p L)) (CFSG.pCore 2 ↥(conjClosure D.M L))
      (MulEquiv.subgroupCongr hI) (CFSG.pCore_map_iso 2 (MulEquiv.subgroupCongr hI))).symm hSp
    rw [hnm]
    exact h'
  · simpa only [hnm] using hodd
  · rw [hI]; exact hswap
  · rw [hnm]; exact hcong

theorem setting1910_of_jM_ne_four (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp19 D V₀ V p L) (h1 : R19_1At D V₀ V p L h) (h9 : R19_9At D V₀ V p L h)
    (h67 : R17_67At D V₀ V) (h42 : R17_42At D V₀ V) (hj : jM D p ≠ 4) :
    Setting1910 D V₀ V p L := by
  have hV0 : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.big
  have hXstar : conjClosure D.M L ∈ calL0Star D p := h.hX
  have h67' := h67 hV0 p h.hp L h.hL (conjClosure D.M L) rfl hXstar
  have h42' : Concl17_42 D L (conjClosure D.M L) p := h42 L p h.hL.1 h.hp
  rcases h67' with hU5 | ⟨m, -, hU4⟩ | ⟨m, hSp4, hswap⟩ | ⟨hXne, m, hshape⟩ |
    ⟨m, hpow, hLU⟩
  ·
    have hsX : IsSimpleGroup (Bar2 (conjClosure D.M L)) :=
      LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU5
    have hXL : conjClosure D.M L = L :=
      conjClosure_eq_self_of_isSimpleGroup_bar2 h.hL.1 hsX
    exact absurd (hXL ▸ hU5) h9.1
  ·
    have hsX : IsSimpleGroup (Bar2 (conjClosure D.M L)) :=
      LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU4
    have hXL : conjClosure D.M L = L :=
      conjClosure_eq_self_of_isSimpleGroup_bar2 h.hL.1 hsX
    have hU4L : IsU4 (Bar2 L) m := hXL ▸ hU4
    have hnm : S17.nOf L = m := S17.nOf_eq_of_isU4 hU4L
    exact False.elim (h9.2 (by rwa [hnm]))
  · exact setting1910_alt_one h h42' hj hSp4 hswap
  ·
    have hnotthin : ¬ F08.Thin8 (conjClosure D.M L) :=
      not_thin8_of_conjClosure_ne h.hL.1 rfl hXne
    have hnotsimple : ¬ IsSimpleGroup (Bar2 (conjClosure D.M L)) := by
      intro hs
      exact hXne (conjClosure_eq_self_of_isSimpleGroup_bar2 h.hL.1 hs)
    have hnot1 : ¬ P17_42_1 D (conjClosure D.M L) := by
      rintro (hthin | ⟨m', hU3⟩ | hL3)
      · exact hnotthin hthin
      · exact absurd (LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU3) hnotsimple
      · exact absurd (LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL3) hnotsimple
    have hnot3 : ¬ P17_42_3 D (conjClosure D.M L) p := by
      rintro ⟨m', hU5, -, -, -, -⟩
      exact absurd (LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU5) hnotsimple
    have hnot4 : ¬ P17_42_4 D (conjClosure D.M L) p := by
      rintro ⟨m', hshape', -, -, -, -, -⟩
      rcases hshape' with hSp | hG2
      · exact absurd (LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hSp) hnotsimple
      · exact absurd
          ((CFSG.LieType.Simplicity.fam_g2_simplicity (Bar2 (conjClosure D.M L)) 2 m'
            (LieModel.chevalleyExceptionalModel hG2 (by decide))).2) hnotsimple
    have hnot5 : ¬ P17_42_5 D (conjClosure D.M L) p := by
      rintro ⟨m', hU4', -, -, -⟩
      exact absurd (LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU4') hnotsimple
    rcases h42' with h1' | h2' | h3' | h4' | h5'
    · exact absurd h1' hnot1
    · obtain ⟨m', x, -, -, -, hshape', hmore⟩ := h2'
      exact setting1910_alt_two h1 hmore hj hXne hshape'
    · exact absurd h3' hnot3
    · exact absurd h4' hnot4
    · exact absurd h5' hnot5
  ·
    have hsX : IsSimpleGroup (Bar2 (conjClosure D.M L)) := by
      rcases hLU with hL2 | hU3
      · exact LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
      · exact LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU3
    have hXL : conjClosure D.M L = L :=
      conjClosure_eq_self_of_isSimpleGroup_bar2 h.hL.1 hsX
    have hnotalt : ¬ IsAlt (Bar2 L) 5 := by
      intro halt
      have h2 : IsL2 (Bar2 L) 2 := CFSG.Quasithin.H13.A5.lieModel_of_alternating_five halt.some
      exact h1.1 h2
    have hj4 : jM D p = 4 :=
      jM_eq_four_of_mem_calL0Star (X := L) (hXL ▸ h.hX) h.hL
        (hXL ▸ hsX) hnotalt
        ⟨m, by
          rcases hLU with h | h
          · exact Or.inl (hXL ▸ h)
          · exact Or.inr (hXL ▸ h)⟩
    exact absurd hj4 hj

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
