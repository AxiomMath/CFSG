module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NOfUniqueShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySixShape
public import CFSG.Quasithin.H13.A5S1327j
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofRead
public import CFSG.GroupTheory.QuasisimpleProduct

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem commutator_V0_eq_bot_of_uniqueMax {D : Data G} (h127 : R127 D) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hKN : D.M ≤ normalizer (K : Set G)) (hU : UniqueMax D.M K) : ⁅K, V₀⁆ = ⊥ := by
  have hU' : UniqueMax D.M (K ⊔ D.T) :=
    uc22p22u_uniqueMax_mono D le_sup_left (sup_le hK.1.le D.sylowM.le) hU
  by_contra hKV0ne
  have hV0ne : V₀ ≠ ⊥ := by
    intro h0
    apply hKV0ne
    rw [h0, Subgroup.commutator_bot_right]
  have hV0 : InCalV D.M V₀ := by
    rcases h.1 with ⟨-, hbot⟩ | ⟨h0, -, -⟩
    · exact absurd hbot hV0ne
    · exact h0.1
  have h8 : 8 ≤ Nat.card V₀ := by
    by_contra hlt
    have hV04 : Nat.card V₀ ≤ 4 := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp
        (CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hV0.2.2.2)
      rw [hn] at hlt ⊢
      have h2 : n ≤ 2 := by
        by_contra h
        have h3 : 3 ≤ n := by omega
        have h4 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
        omega
      exact Nat.pow_le_pow_right (by norm_num) h2
    have hcent : K ≤ Subgroup.centralizer (V₀ : Set G) :=
      CFSG.SeitzReduction.LinearPilot.le_centralizer_of_perfect_of_card_le_four
        hK.2.1 (hK.1.le.trans hV0.2.2.1) hV04
    exact hKV0ne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent)
  have hnotV1 : ¬ InCalV1 D.M D.T V₀ := (twelve_nine D h127 h).2 h8 |>.1
  exact hnotV1 (inCalV1_of_commutator_ne_bot hV0 hK hKN hU' hKV0ne)

theorem isL2_or_isU3_of_mem_calC_of_product {I K : Subgroup G} {n : ℕ} (hK : K ∈ calC I)
    (hshape : S17.IsL2U3Product (Bar2 I) n ∨ IsL2Square (Bar2 I) n) :
    IsL2 (Bar2 K) n ∨ IsU3 (Bar2 K) n := by
  obtain ⟨K', -, ⟨e, -⟩, -, -, hsub⟩ := uc22p22r_bar2_quasisimple_iso hK
  have hP : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
  rcases hshape with ⟨A, B, gA, gB, ⟨f⟩, hA, hB⟩ | ⟨A, B, gA, gB, ⟨f⟩, hA, hB⟩
  · have : IsSimpleGroup A :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hA
    have : IsSimpleGroup B :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hB
    rcases CFSG.GroupTheory.nonempty_mulEquiv_factor_of_isSubnormal_quasisimple f e hP
      hsub with hgA | hgB
    · obtain ⟨g⟩ := hgA
      exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv g.symm hA)
    · obtain ⟨g⟩ := hgB
      exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv g.symm hB)
  · have : IsSimpleGroup A :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hA
    have : IsSimpleGroup B :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hB
    rcases CFSG.GroupTheory.nonempty_mulEquiv_factor_of_isSubnormal_quasisimple f e hP
      hsub with hgA | hgB
    · obtain ⟨g⟩ := hgA
      exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv g.symm hA)
    · obtain ⟨g⟩ := hgB
      exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv g.symm hB)

theorem le_IOf_of_mem_calLp {D : Data G} {p : ℕ} {L K : Subgroup G} (hj : S17.jM D p = 4)
    (hK : K ∈ S17.calLp D p) : K ≤ IOf D p L := by
  rw [IOf, if_pos hj]
  exact le_iSup₂_of_le K hK le_rfl

theorem mem_calC_IOf_of_mem_calLp {D : Data G} {p : ℕ} {L K : Subgroup G}
    (hj : S17.jM D p = 4) (hK : K ∈ S17.calLp D p) (hIM : IOf D p L ≤ D.M) :
    K ∈ calC (IOf D p L) := by
  have hKI : K ≤ IOf D p L := le_IOf_of_mem_calLp hj hK
  have h := hK.1.1.inf (IOf D p L)
  rw [inf_eq_left.2 hKI, inf_eq_right.2 hIM] at h
  exact ⟨h, hK.1.2.1, hK.1.2.2⟩

section Cert


theorem hyp1754_of_jM_eq_four (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp19 D V₀ V p L) (h42 : S17.R17_42At D V₀ V) (hj : S17.jM D p = 4) :
    S17.Hyp1754 D p := by
  have hjm := S17.jM_mem_of_nonempty ⟨_, h.hX⟩
  have hX1 : conjClosure D.M L ∉ S17.calL1Star D p := by
    have he : S17.calL1Star D p = ∅ := by
      simpa [S17.calLjStar] using hjm.2.2.2 1 (by norm_num) (by omega)
    simp [he]
  have hX2 : conjClosure D.M L ∉ S17.calL2Star D p := by
    have he : S17.calL2Star D p = ∅ := by
      simpa [S17.calLjStar] using hjm.2.2.2 2 (by norm_num) (by omega)
    simp [he]
  have hX3 : conjClosure D.M L ∉ S17.calL3Star D p := by
    have he : S17.calL3Star D p = ∅ := by
      simpa [S17.calLjStar] using hjm.2.2.2 3 (by norm_num) (by omega)
    simp [he]
  exact S17.hyp1754_of_mem_calL0Star D h42 h.hp h.hX hX1 hX2 hX3

theorem uniqueMax_of_mem_calLp_of_jM_four {D : Data G} {V₀ V : Subgroup G} {p n : ℕ}
    {K : Subgroup G} (hp : p ∈ D.sig) (hj : S17.jM D p = 4) (h54 : S17.Hyp1754 D p)
    (h661 : S17.R17_66_1At D V₀ V) (hK : K ∈ S17.calLp D p)
    (hshapeK : IsL2 (Bar2 K) n ∨ IsU3 (Bar2 K) n) (hpow : IsPowTwo n) (hn : 2 < n) :
    UniqueMax D.M K := by
  have hKM : K ≤ D.M := hK.1.1.le
  have hcc : conjClosure D.M K = K := uc22p2214_conjClosure_eq_of_normal hKM (h54.2 K hK.1).1
  have hnotA5 : ¬ IsAlt (Bar2 K) 5 := by
    rintro ⟨e⟩
    have h2 : IsL2 (Bar2 K) 2 := CFSG.Quasithin.H13.A5.lieModel_of_alternating_five e
    rcases hshapeK with hL2 | hU3
    · have := (CFSG.ComponentClassification.CatLeafProof.lieModel_eq_of_isChar2LieShape h2
        S17.isChar2LieShape_PSL hL2).2.2
      omega
    · exact absurd (CFSG.ComponentClassification.CatLeafProof.lieModel_eq_of_isChar2LieShape h2
        S17.isChar2LieShape_PSL hU3).1 (by decide)
  have h0 : S17.calL0Star D p = S17.calL4Star D p := by
    simp [S17.calL0Star, S17.calLjStar, hj]
  have hmem : conjClosure D.M K ∈ S17.calL0Star D p := by
    rw [h0]
    obtain ⟨k, rfl⟩ := hpow
    refine ⟨⟨K, hK, rfl⟩, ⟨k, ?_⟩, ?_⟩
    · rw [hcc]
      exact hshapeK
    · rw [hcc]
      exact hnotA5
  rcases h661 p hp K hK (conjClosure D.M K) rfl hmem with hU | hA5
  · exact hU
  · exact absurd hA5 hnotA5

theorem IOf_le_centralizer_V0_of_jM_four (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp19 D V₀ V p L) (h127 : R127 D) (hj : S17.jM D p = 4)
    (h54 : S17.Hyp1754 D p) (h661 : S17.R17_66_1At D V₀ V)
    (hshape : S17.IsL2U3Product (Bar2 (IOf D p L)) (S17.nOf L) ∨
      IsL2Square (Bar2 (IOf D p L)) (S17.nOf L))
    (hpow : IsPowTwo (S17.nOf L)) (hn : 2 < S17.nOf L) :
    IOf D p L ≤ centralizer (V₀ : Set G) := by
  have hIM : IOf D p L ≤ D.M := IOf_le_M D p h.hL.1.1.le
  have hgen : ∀ K ∈ S17.calLp D p, K ≤ centralizer (V₀ : Set G) := by
    intro K hK
    have hKcalC : K ∈ calC (IOf D p L) := mem_calC_IOf_of_mem_calLp hj hK hIM
    have hshapeK := isL2_or_isU3_of_mem_calC_of_product hKcalC hshape
    have hU : UniqueMax D.M K :=
      uniqueMax_of_mem_calLp_of_jM_four h.hp hj h54 h661 hK hshapeK hpow hn
    have hKN : D.M ≤ normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hK.1.1.le).mp (h54.2 K hK.1).1
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (commutator_V0_eq_bot_of_uniqueMax h127 h.hyp125 hK.1 hKN hU)
  rw [IOf, if_pos hj]
  exact iSup₂_le hgen

theorem alt3_A_le_centralizer (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h42 : S17.R17_42At D V₀ V)
    (h661 : S17.R17_66_1At D V₀ V)
    (hshape : S17.IsL2U3Product (Bar2 (IOf D p L)) (S17.nOf L) ∨
      IsL2Square (Bar2 (IOf D p L)) (S17.nOf L))
    (hpow : IsPowTwo (S17.nOf L)) (hn : 2 < S17.nOf L) :
    A ≤ centralizer (V₀ : Set G) := by
  by_cases hj : S17.jM D p = 4
  · exact h.hA.trans (IOf_le_centralizer_V0_of_jM_four D h.hyp h127 hj
      (hyp1754_of_jM_eq_four D h.hyp h42 hj) h661 hshape hpow hn)
  · have hI : IOf D p L = conjClosure D.M L := by simp [IOf, hj]
    have hXne : conjClosure D.M L ≠ L := by
      intro hXL
      have hq : CFSG.Open.IsQuasisimple (Bar2 (IOf D p L)) := by
        rw [hI, hXL]
        exact h.hyp.hL.1.2.2
      rcases hshape with ⟨A', B', gA, gB, ⟨f⟩, hA, hB⟩ | ⟨A', B', gA, gB, ⟨f⟩, hA, hB⟩
      · have : IsSimpleGroup A' :=
          CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hA
        have : IsSimpleGroup B' :=
          CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hB
        exact (CFSG.RankThree.PartTwo.Sec15.Proof1515.isEmpty_mulEquiv_prod_of_isQuasisimple
          (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq)).false f
      · have : IsSimpleGroup A' :=
          CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hA
        have : IsSimpleGroup B' :=
          CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hB
        exact (CFSG.RankThree.PartTwo.Sec15.Proof1515.isEmpty_mulEquiv_prod_of_isQuasisimple
          (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq)).false f
    obtain ⟨m, x, -, -, -, hshL, -⟩ := S17.p42_alt2_of_ne h42 h.hyp.hp h.hyp.hL.1 hXne
    have hnm : S17.nOf L = m := by
      rcases hshL with ⟨hL2, -⟩ | ⟨hSz, -⟩
      · exact S17.nOf_eq_of_isL2 hL2
      · exact S17.nOf_eq_of_isChar2LieShape hSz (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    exact alt2_A_le_centralizer D h h61 h127 hI hXne (by rw [hnm]; exact hshL)

theorem A_le_centralizer_V0 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h42 : S17.R17_42At D V₀ V)
    (h661 : S17.R17_66_1At D V₀ V) :
    A ≤ centralizer (V₀ : Set G) := by
  have h1910 := h.h1910
  simp only [Setting1910] at h1910
  obtain ⟨-, h1 | h2 | h3⟩ := h1910
  · exact alt1_A_le_centralizer D h h61 h127 h1.1 h1.2.2.2
  · exact alt2_A_le_centralizer D h h61 h127 h2.1 h2.2.1 h2.2.2.2
  · exact alt3_A_le_centralizer D h h61 h127 h42 h661 h3.1 h3.2.2.1 h3.2.1

theorem gap19_22_holds (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h42 : S17.R17_42At D V₀ V)
    (h661 : S17.R17_66_1At D V₀ V) :
    Gap19_22 D V₀ V p L A t B r h := by
  intro _ A₀ hA₀ _ _ _
  exact Subgroup.le_centralizer_iff.mp (hA₀.trans (A_le_centralizer_V0 D h h61 h127 h42 h661))

end Cert

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
