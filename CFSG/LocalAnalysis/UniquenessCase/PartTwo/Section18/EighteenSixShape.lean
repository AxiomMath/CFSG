module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Statements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.XBarShapeCong
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySixShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixHyp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeafProof
  (IsChar2LieShape lieModel_eq_of_isChar2LieShape fieldExponent_eq_of_isChar2LieShape)

variable {G : Type} [Group G] [Finite G]

section Certified


private theorem isU4_bar2_cong {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h1742 : S17.R17_42At D V₀ V) {f : ℕ}
    (hU : IsU4 (Bar2 (conjClosure D.M L)) f) :
    conjClosure D.M L = L ∧ S17.nOf L = f ∧ IsU4 (Bar2 L) (S17.nOf L) ∧ 1 < f ∧
      (2 : ℤ) ^ f ≡ -1 [ZMOD (p : ℤ)] := by
  have hs : IsSimpleGroup (Bar2 (conjClosure D.M L)) :=
    LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU
  have hXL : conjClosure D.M L = L :=
    conjClosure_eq_self_of_isSimpleGroup_bar2 h.hL.1 hs
  have hUX : IsU4 (Bar2 (conjClosure D.M L)) f := hU
  have hUL : IsU4 (Bar2 L) f := hXL ▸ hU
  have hconcl : S17.Concl17_42 D L (conjClosure D.M L) p := h1742 L p h.hL.1 h.hp
  rcases hconcl with h1 | ⟨n, x, -, -, hXne, -, -⟩ | ⟨n, hU5, -, -, -, -⟩ |
    ⟨n, hshape4, -, -, -, -⟩ | ⟨n, hU4, hn1, hcong, -⟩
  · rcases h1 with hthin | ⟨n, hU3⟩ | hL3
    · exact absurd hthin (S17.not_thin8_of_isU4_bar2 hUX)
    · exact absurd (lieModel_eq_of_isChar2LieShape hUX S17.isChar2LieShape_PSU_four hU3).2.1
        (by norm_num)
    · exact absurd (lieModel_eq_of_isChar2LieShape hUX S17.isChar2LieShape_PSU_four hL3).1
        (by decide)
  · exact absurd hXL hXne
  · exact absurd (lieModel_eq_of_isChar2LieShape hUX S17.isChar2LieShape_PSU_four hU5).2.1
      (by norm_num)
  · rcases hshape4 with hsp | hg2
    · exact absurd (lieModel_eq_of_isChar2LieShape hUX S17.isChar2LieShape_PSU_four hsp).1
        (by decide)
    · exact absurd (lieModel_eq_of_isChar2LieShape hUX S17.isChar2LieShape_PSU_four hg2).1
        (by decide)
  · have hnf : n = f :=
      fieldExponent_eq_of_isChar2LieShape hUX S17.isChar2LieShape_PSU_four hU4
    have hnof : S17.nOf L = f := S17.nOf_eq_of_isU4 hUL
    exact ⟨hXL, hnof, hnof.symm ▸ hUL, hnf ▸ hn1, hnf ▸ hcong⟩

theorem shape18_6 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h1742 : S17.R17_42At D V₀ V) (h1733 : S17.R17_33_3At D V₀ V)
    (h18_4 : R18_4At D V₀ V p L) :
    Shape18_6 D L := by
  by_cases hXL : conjClosure D.M L = L
  ·
    right
    refine ⟨hXL, ?_⟩
    have hXc : L ∈ S17.calLjStar D p (S17.jM D p) := by
      have h0 := (S17.mem_calL0Star (D := D) (p := p)).1 h.hX
      rwa [hXL] at h0
    simp only [S17.calLjStar] at hXc
    split_ifs at hXc with hj1 hj2 hj3 hj4 hj5
    ·
      rw [S17.mem_calL1Star] at hXc
      rcases hXc.2 with ⟨f, hg2 | hsp | hu4⟩ | hu5
      · obtain ⟨-, hnof, hf1, hodd, -⟩ :=
          isSp4_or_isG2_bar2_cong_more h h1742 (Or.inr (hXL.symm ▸ hg2))
        rw [← hnof] at hf1 hodd
        exact Or.inr (Or.inr (Or.inl ⟨hodd, by omega, Or.inr (hnof.symm ▸ hg2)⟩))
      · obtain ⟨-, hnof, hf1, hodd, -⟩ :=
          isSp4_or_isG2_bar2_cong_more h h1742 (Or.inl (hXL.symm ▸ hsp))
        rw [← hnof] at hf1 hodd
        exact Or.inr (Or.inr (Or.inl ⟨hodd, by omega, Or.inl (hnof.symm ▸ hsp)⟩))
      · obtain ⟨-, hnof, hu4, hf1, -⟩ :=
          isU4_bar2_cong h h1742 (hXL.symm ▸ hu4)
        exact Or.inr (Or.inr (Or.inr ⟨by rw [← hnof] at hf1; omega, hu4⟩))
      · have hshape : IsChar2LieShape .PSU 5 := by
          unfold IsChar2LieShape; simp
        exact Or.inr (Or.inl ⟨hu5, S17.nOf_eq_of_isChar2LieShape hu5 hshape⟩)
    ·
      rw [S17.mem_calL2Star] at hXc
      exact absurd h.hL hXc.2.1
    ·
      rw [S17.mem_calL3Star] at hXc
      exact absurd h.hL.1.2.2 (S17.not_isQuasisimple_of_isA5xA5 hXc.2)
    ·
      rw [S17.mem_calL4Star] at hXc
      obtain ⟨k, hL2 | hU3⟩ := hXc.2.1
      · have hnof : S17.nOf L = 2 ^ k := S17.nOf_eq_of_isL2 hL2
        refine Or.inl ⟨hnof.symm ▸ hL2, ?_, ⟨k, hnof⟩⟩
        rw [hnof]
        have hk2 : 2 ≤ k := by
          by_contra hk
          have hk1 : k ≤ 1 := by omega
          interval_cases k
          · have hadm := CFSG.Blueprint.LieModel.admissible hL2
            simpa [CFSG.Open.StatedLieAdmissible] using hadm
          · have hSC : CFSG.Open.StatedClassicalModel (Bar2 L) .PSL 2 2 2 :=
              LieModel.statedClassicalModel hL2 (by decide)
            have hsimple : IsSimpleGroup (Bar2 L) :=
              (CFSG.LieType.Simplicity.fam_PSL_simplicity (Bar2 L) 2 2 2 hSC).2
            have hcard : Nat.card (Bar2 L) = 60 :=
              CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_four hSC
            exact hXc.2.2
              (CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
                hcard)
        calc 2 < 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      · have hSU3 : IsSU3 (Bar2 L) (2 ^ k) :=
          uc22p22d_isSU3_of_isU3 h.hL.1.2.2 hU3
        have hsmall := h.small
        exact absurd (h1733 L (2 ^ k) h.hL.1 hSU3) (by omega)
    ·
      rw [S17.mem_calL5Star] at hXc
      exact absurd hXc.2 h18_4
    · exact absurd hXc (by simp)
  ·
    left
    obtain ⟨n, x, hxM, hXsup, -, hshape, -⟩ :=
      S17.p42_alt2_of_ne (D := D) (V₀ := V₀) (V := V) h1742 (p := p) h.hp
        (L := L) h.hL.1 hXL
    have hncard : (conjSetOf D.M L).ncard = 2 :=
      S17.ncard_eq_two_of_p42 h.hL.1 hxM hXsup hXL
    refine ⟨hXL, ?_, ?_, hncard⟩
    · rcases hshape with ⟨hL2, -⟩ | ⟨hSz, -⟩
      · have hnof : S17.nOf L = n := S17.nOf_eq_of_isL2 hL2
        refine Or.inl (hnof.symm ▸ hL2)
      · have hnof : S17.nOf L = n := S17.nOf_eq_of_isSz hSz
        refine Or.inr (hnof.symm ▸ hSz)
    · rcases hshape with ⟨hL2, -⟩ | ⟨hSz, -⟩
      · have hnof : S17.nOf L = n := S17.nOf_eq_of_isL2 hL2
        rw [hnof]
        have hadm := CFSG.Blueprint.LieModel.admissible hL2
        simp only [CFSG.Open.StatedLieAdmissible] at hadm
        obtain ⟨-, hnpos, -, hne2, -⟩ := hadm
        have hn1 : n ≠ 1 := by
          intro hn
          subst hn
          exact hne2 (by norm_num)
        have hn2 : n ≠ 2 := by
          intro hn
          subst hn
          have hSC : CFSG.Open.StatedClassicalModel (Bar2 L) .PSL 2 2 2 :=
            LieModel.statedClassicalModel hL2 (by decide)
          have hsimple : IsSimpleGroup (Bar2 L) :=
            (CFSG.LieType.Simplicity.fam_PSL_simplicity (Bar2 L) 2 2 2 hSC).2
          have hcard : Nat.card (Bar2 L) = 60 :=
            CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_four hSC
          exact h18_4
            (CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty hcard)
        omega
      · have hnof : S17.nOf L = n := S17.nOf_eq_of_isSz hSz
        rw [hnof]
        have hadm := CFSG.Blueprint.LieModel.admissible hSz
        simp only [CFSG.Open.StatedLieAdmissible] at hadm
        obtain ⟨-, -, -, -, hodd, hge3⟩ := hadm
        omega

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
