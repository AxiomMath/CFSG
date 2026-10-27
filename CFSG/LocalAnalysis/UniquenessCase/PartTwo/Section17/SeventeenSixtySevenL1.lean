module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySevenBorel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4G2TwoAutInnerHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U4TwoAutPowerMapHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U4RootLineHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4RootLineHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.G2RootLineHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NOfUniqueShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NOfUniqueShapesSzSp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeafProof
  (lieModel_eq_of_isChar2LieShape fieldExponent_eq_of_isChar2LieShape)

variable {G : Type} [Group G] [Finite G]

section CertD


theorem p42_4_of_isSp4_or_isG2_bar2 {D : Data G} {V₀ V : Subgroup G}
    (h42 : R17_42At D V₀ V) {p : ℕ} (hp : p ∈ D.sig) {L : Subgroup G} (hL : L ∈ calC D.M)
    {f : ℕ} (hS : IsSp4 (Bar2 (conjClosure D.M L)) f ∨ IsG2 (Bar2 (conjClosure D.M L)) f) :
    conjClosure D.M L = L ∧ 1 < f ∧ Odd f ∧ (2 : ℤ) ^ f ≡ -1 [ZMOD (p : ℤ)] ∧
      P17_42_more D (conjClosure D.M L) f := by
  have hsimple : IsSimpleGroup (Bar2 (conjClosure D.M L)) := by
    rcases hS with hsp | hg2
    · exact LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hsp
    · exact (CFSG.LieType.Simplicity.fam_g2_simplicity (Bar2 (conjClosure D.M L)) 2 f
        (LieModel.chevalleyExceptionalModel hg2 (by decide))).2
  have hXL : conjClosure D.M L = L := conjClosure_eq_self_of_isSimpleGroup_bar2 hL hsimple
  rcases h42 L p hL hp with h1 | ⟨n, x, -, -, hXne, -, -⟩ | ⟨n, hU5, -, -, -, -⟩ |
    ⟨n, hshape4, hn1, hodd, hcong, -, hmore⟩ | ⟨n, hU4, -, -, -⟩
  · rcases h1 with hthin | ⟨n, hU3⟩ | hL3
    · rcases hS with hsp | hg2
      · exact absurd hthin (not_thin8_of_isSp4_bar2 hsp)
      · exact absurd hthin (not_thin8_of_isG2_bar2 hg2)
    · rcases hS with hsp | hg2
      · exact absurd (lieModel_eq_of_isChar2LieShape hsp isChar2LieShape_PSp hU3).1 (by decide)
      · exact absurd (lieModel_eq_of_isChar2LieShape hg2 isChar2LieShape_G2 hU3).1 (by decide)
    · rcases hS with hsp | hg2
      · exact absurd (lieModel_eq_of_isChar2LieShape hsp isChar2LieShape_PSp hL3).1 (by decide)
      · exact absurd (lieModel_eq_of_isChar2LieShape hg2 isChar2LieShape_G2 hL3).1 (by decide)
  · exact absurd hXL hXne
  · rcases hS with hsp | hg2
    · exact absurd (lieModel_eq_of_isChar2LieShape hsp isChar2LieShape_PSp hU5).1 (by decide)
    · exact absurd (lieModel_eq_of_isChar2LieShape hg2 isChar2LieShape_G2 hU5).1 (by decide)
  · have hnf : n = f := by
      rcases hS with hsp | hg2
      · rcases hshape4 with hspn | hg2n
        · exact fieldExponent_eq_of_isChar2LieShape hsp isChar2LieShape_PSp hspn
        · exact absurd (lieModel_eq_of_isChar2LieShape hsp isChar2LieShape_PSp hg2n).1
            (by decide)
      · rcases hshape4 with hspn | hg2n
        · exact absurd (lieModel_eq_of_isChar2LieShape hg2 isChar2LieShape_G2 hspn).1
            (by decide)
        · exact fieldExponent_eq_of_isChar2LieShape hg2 isChar2LieShape_G2 hg2n
    subst hnf
    exact ⟨hXL, hn1, hodd, hcong, hmore⟩
  · rcases hS with hsp | hg2
    · exact absurd (lieModel_eq_of_isChar2LieShape hsp isChar2LieShape_PSp hU4).1 (by decide)
    · exact absurd (lieModel_eq_of_isChar2LieShape hg2 isChar2LieShape_G2 hU4).1 (by decide)

theorem p42_5_of_isU4_bar2 {D : Data G} {V₀ V : Subgroup G}
    (h42 : R17_42At D V₀ V) {p : ℕ} (hp : p ∈ D.sig) {L : Subgroup G} (hL : L ∈ calC D.M)
    {f : ℕ} (hU : IsU4 (Bar2 (conjClosure D.M L)) f) :
    conjClosure D.M L = L ∧ 1 < f ∧ (2 : ℤ) ^ f ≡ -1 [ZMOD (p : ℤ)] ∧
      P17_42_more D (conjClosure D.M L) f := by
  have hs : IsSimpleGroup (Bar2 (conjClosure D.M L)) :=
    LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU
  have hXL : conjClosure D.M L = L := conjClosure_eq_self_of_isSimpleGroup_bar2 hL hs
  rcases h42 L p hL hp with h1 | ⟨n, x, -, -, hXne, -, -⟩ | ⟨n, hU5, -, -, -, -⟩ |
    ⟨n, hshape4, -, -, -, -, -⟩ | ⟨n, hU4, hn1, hcong, hmore⟩
  · rcases h1 with hthin | ⟨n, hU3⟩ | hL3
    · exact absurd hthin (not_thin8_of_isU4_bar2 hU)
    · exact absurd (lieModel_eq_of_isChar2LieShape hU isChar2LieShape_PSU_four hU3).2.1
        (by norm_num)
    · exact absurd (lieModel_eq_of_isChar2LieShape hU isChar2LieShape_PSU_four hL3).1
        (by decide)
  · exact absurd hXL hXne
  · exact absurd (lieModel_eq_of_isChar2LieShape hU isChar2LieShape_PSU_four hU5).2.1
      (by norm_num)
  · rcases hshape4 with hsp | hg2
    · exact absurd (lieModel_eq_of_isChar2LieShape hU isChar2LieShape_PSU_four hsp).1
        (by decide)
    · exact absurd (lieModel_eq_of_isChar2LieShape hU isChar2LieShape_PSU_four hg2).1
        (by decide)
  · have hnf : n = f := fieldExponent_eq_of_isChar2LieShape hU isChar2LieShape_PSU_four hU4
    subst hnf
    exact ⟨hXL, hn1, hcong, hmore⟩

theorem seventeen_sixtyseven_l1_false_of_shape {D : Data G} {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) (hV0 : V₀ ≠ ⊥) (h109 : Inputs1719.UC2_10_9 D) (h869 : F08.R869 D)
    (hSg : UC6S846.SigmaStd D) (h638 : UC6.R6_38 D) (h72 : F07.R72 D) (hK35 : UCK.K35w)
    (hKU4 : Inputs1719.K_U4RootLine) (hKSp4 : Inputs1719.K_Sp4RootLine)
    (hKG2 : Inputs1719.K_G2RootLine)
    {p : ℕ} (hp : p ∈ D.sig) {L : Subgroup G} (hL : L ∈ calLp D p)
    (hXL : conjClosure D.M L = L)
    {f s : ℕ} (hshape : IsU4 (Bar2 L) f ∨ IsSp4 (Bar2 L) f ∨ IsG2 (Bar2 L) f) (hf1 : 1 < f)
    (hs : Odd s) (hs1 : 1 < s) (hsf : s ∣ f)
    (hcong : (2 : ℤ) ^ f ≡ -1 [ZMOD (p : ℤ)]) (hmore : P17_42_more D L f)
    (hcase : CFSG.Open.pRank p L = 2 ∨ IsU4 (Bar2 L) f)
    (hpow : ∀ t ∈ D.T, ∃ j : ℕ, ∀ b ∈ L ⊓ normalizer ((D.T ⊓ L : Subgroup G) : Set G),
      t * b * t⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ D.T ⊓ L) :
    False := by
  classical
  obtain ⟨r, hr, hrdvd⟩ := s13_exists_prime_dvd hs1
  have hr7 : 7 ≤ r := s13_seven_le_of_dvd hs hr hrdvd
  have hrdvdf : r ∣ 2 ^ f - 1 := hrdvd.trans (Nat.pow_sub_one_dvd_pow_sub_one (x := 2) hsf)
  have hLopp : L = Opp r D.M := (hmore.2 r hr (by omega) hrdvdf).1
  obtain ⟨B, hBB, hBcard, hBU⟩ :=
    exists_rootLine_le_borel_mem_uniqueSet hL.1 hp hSg h638 h72 hK35 hKU4 hKSp4 hKG2 hshape
      hf1 hcong hcase hr (by omega) hrdvdf hLopp
  have hT2 : IsPGroup 2 D.T := (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM).2.1
  have hTL : D.T ≤ normalizer (L : Set G) := by
    have h := TwelveTwentyThree.le_normalizer_conjClosure D.M L
    rw [hXL] at h
    exact D.sylowM.le.trans h
  have hBT : B ≤ normalizer (D.T : Set G) :=
    le_normalizer_of_le_borel hTL hT2 hpow hs hr hrdvd hBB hBcard
  have hnt : ¬ F08.Thin8 L := by
    rcases hshape with h | h | h
    · exact not_thin8_of_isU4_bar2 h
    · exact not_thin8_of_isSp4_bar2 h
    · exact not_thin8_of_isG2_bar2 h
  have hsimple : IsSimpleGroup (Bar2 L) := by
    rcases hshape with h | h | h
    · exact LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
    · exact LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
    · exact (CFSG.LieType.Simplicity.fam_g2_simplicity (Bar2 L) 2 f
        (LieModel.chevalleyExceptionalModel h (by decide))).2
  have hX1 : L ∈ calL1Star D p := by
    rcases hshape with h | h | h
    · exact ⟨⟨L, hL, hXL.symm⟩, Or.inl ⟨f, Or.inr (Or.inr h)⟩⟩
    · exact ⟨⟨L, hL, hXL.symm⟩, Or.inl ⟨f, Or.inr (Or.inl h)⟩⟩
    · exact ⟨⟨L, hL, hXL.symm⟩, Or.inl ⟨f, Or.inl h⟩⟩
  exact seventeen_sixtyseven_l1_false_of_torusElement h109 hV hV0 h869 hL hXL.symm hX1 hsimple
    hnt hs hr hrdvd (hBB.trans inf_le_left) hBT hBcard (inU_iff_mem_uniqueSet.mpr hBU)

private theorem seventeen_sixtyseven_l1_g2_false {D : Data G} {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) (hV0 : V₀ ≠ ⊥) (h109 : Inputs1719.UC2_10_9 D) (h869 : F08.R869 D)
    (hSg : UC6S846.SigmaStd D) (h638 : UC6.R6_38 D) (h72 : F07.R72 D) (hK35 : UCK.K35w)
    (hKU4 : Inputs1719.K_U4RootLine) (hKSp4 : Inputs1719.K_Sp4RootLine)
    (hKG2 : Inputs1719.K_G2RootLine)
    (h42 : R17_42At D V₀ V) {p : ℕ} (hp : p ∈ D.sig) {L : Subgroup G}
    (hL : L ∈ calLp D p) {f : ℕ} (hshape : IsG2 (Bar2 (conjClosure D.M L)) f) : False := by
  have hp' : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  have hT2 : IsPGroup 2 D.T := (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM).2.1
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (D.T ⊓ L) L :=
    isSylowTwoOf_inf_of_mem_calC hL.1
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf (sylowBar2 L (D.T ⊓ L)) ⊤ :=
    isSylowTwoOf_sylowBar2 hL.1
  obtain ⟨hXL, hf1, hodd, hcong, hmore⟩ :=
    p42_4_of_isSp4_or_isG2_bar2 h42 hp hL.1 (Or.inr hshape)
  have hG2L : IsG2 (Bar2 L) f := hXL ▸ hshape
  have hTL : D.T ≤ normalizer (L : Set G) := by
    have h := TwelveTwentyThree.le_normalizer_conjClosure D.M L
    rw [hXL] at h
    exact D.sylowM.le.trans h
  have hq : 2 < 2 ^ f := by
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
    norm_num at this
    omega
  have hZ : Subgroup.center (Bar2 L) = ⊥ :=
    Inputs1719.center_eq_bot_of_rootLineShape hq (Or.inr (Or.inr hG2L))
  have hpow := powerMap_of_rhoL_mem_inner hTL hT2 hSyl hZ fun m hm =>
    Inputs1719.g2_twoAut_inner hodd hf1 hG2L _ (exists_rhoL_pow_two_pow_eq_one hT2 m hm)
  exact seventeen_sixtyseven_l1_false_of_shape hV hV0 h109 h869 hSg h638 h72 hK35 hKU4 hKSp4
    hKG2 hp hL hXL (Or.inr (Or.inr hG2L)) hf1 hodd hf1 dvd_rfl hcong (hXL ▸ hmore)
    (Or.inl (pRank_eq_two_of_isSp4_or_isG2_bar2 (Or.inr hG2L) (by omega) hp' hp2 hcong)) hpow

private theorem seventeen_sixtyseven_l1_sp4_false {D : Data G} {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) (hV0 : V₀ ≠ ⊥) (h109 : Inputs1719.UC2_10_9 D) (h869 : F08.R869 D)
    (hSg : UC6S846.SigmaStd D) (h638 : UC6.R6_38 D) (h72 : F07.R72 D) (hK35 : UCK.K35w)
    (hKU4 : Inputs1719.K_U4RootLine) (hKSp4 : Inputs1719.K_Sp4RootLine)
    (hKG2 : Inputs1719.K_G2RootLine)
    (h42 : R17_42At D V₀ V) {p : ℕ} (hp : p ∈ D.sig) {L : Subgroup G}
    (hL : L ∈ calLp D p) {f : ℕ} (hshape : IsSp4 (Bar2 (conjClosure D.M L)) f)
    (hsw : ¬ SwapsParabolics D.T (conjClosure D.M L)) : False := by
  have hp' : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  have hT2 : IsPGroup 2 D.T := (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM).2.1
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (D.T ⊓ L) L :=
    isSylowTwoOf_inf_of_mem_calC hL.1
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf (sylowBar2 L (D.T ⊓ L)) ⊤ :=
    isSylowTwoOf_sylowBar2 hL.1
  obtain ⟨hXL, hf1, hodd, hcong, hmore⟩ :=
    p42_4_of_isSp4_or_isG2_bar2 h42 hp hL.1 (Or.inl hshape)
  have hSpL : IsSp4 (Bar2 L) f := hXL ▸ hshape
  have hswL : ¬ SwapsParabolics D.T L := hXL ▸ hsw
  have hTL : D.T ≤ normalizer (L : Set G) := by
    have h := TwelveTwentyThree.le_normalizer_conjClosure D.M L
    rw [hXL] at h
    exact D.sylowM.le.trans h
  have hq : 2 < 2 ^ f := by
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
    norm_num at this
    omega
  have hZ : Subgroup.center (Bar2 L) = ⊥ :=
    Inputs1719.center_eq_bot_of_rootLineShape hq (Or.inr (Or.inl hSpL))
  have hpow := powerMap_of_rhoL_mem_inner hTL hT2 hSyl hZ fun m hm =>
    Inputs1719.sp4_twoAut_inner hodd hSpL hS (exists_rhoL_pow_two_pow_eq_one hT2 m hm)
      (rhoL_map_eq_of_not_swaps hswL m hm)
  exact seventeen_sixtyseven_l1_false_of_shape hV hV0 h109 h869 hSg h638 h72 hK35 hKU4 hKSp4
    hKG2 hp hL hXL (Or.inr (Or.inl hSpL)) hf1 hodd hf1 dvd_rfl hcong (hXL ▸ hmore)
    (Or.inl (pRank_eq_two_of_isSp4_or_isG2_bar2 (Or.inl hSpL) (by omega) hp' hp2 hcong)) hpow

private theorem seventeen_sixtyseven_l1_u4_false {D : Data G} {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) (hV0 : V₀ ≠ ⊥) (h109 : Inputs1719.UC2_10_9 D) (h869 : F08.R869 D)
    (hSg : UC6S846.SigmaStd D) (h638 : UC6.R6_38 D) (h72 : F07.R72 D) (hK35 : UCK.K35w)
    (hKU4 : Inputs1719.K_U4RootLine) (hKSp4 : Inputs1719.K_Sp4RootLine)
    (hKG2 : Inputs1719.K_G2RootLine)
    (h42 : R17_42At D V₀ V) {p : ℕ} (hp : p ∈ D.sig) {L : Subgroup G}
    (hL : L ∈ calLp D p) {f : ℕ} (hshape : IsU4 (Bar2 (conjClosure D.M L)) f)
    (hpow2 : ¬ IsPowTwo f) : False := by
  have hT2 : IsPGroup 2 D.T := (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM).2.1
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (D.T ⊓ L) L :=
    isSylowTwoOf_inf_of_mem_calC hL.1
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf (sylowBar2 L (D.T ⊓ L)) ⊤ :=
    isSylowTwoOf_sylowBar2 hL.1
  obtain ⟨hXL, hf1, hcong, hmore⟩ := p42_5_of_isU4_bar2 h42 hp hL.1 hshape
  have hU4L : IsU4 (Bar2 L) f := hXL ▸ hshape
  have hTL : D.T ≤ normalizer (L : Set G) := by
    have h := TwelveTwentyThree.le_normalizer_conjClosure D.M L
    rw [hXL] at h
    exact D.sylowM.le.trans h
  obtain ⟨s, hs, hs1, hsf⟩ := s13_exists_odd_divisor hpow2
  have hpow := powerMap_of_rhoL_powerMap hTL hT2 hSyl
    (Inputs1719.k_U4TwoAutPowerMap_holds (Bar2 L) f hU4L hf1 _ hS)
  exact seventeen_sixtyseven_l1_false_of_shape hV hV0 h109 h869 hSg h638 h72 hK35 hKU4 hKSp4
    hKG2 hp hL hXL (Or.inl hU4L) hf1 hs hs1 hsf hcong (hXL ▸ hmore) (Or.inr hU4L) hpow

theorem seventeen_sixtyseven_of_mem_calL1Star {D : Data G} {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) (h42 : R17_42At D V₀ V) (h109 : Inputs1719.UC2_10_9 D)
    (h869 : F08.R869 D) (hSg : UC6S846.SigmaStd D) (h638 : UC6.R6_38 D) (h72 : F07.R72 D)
    (hK35 : UCK.K35w) (hKU4 : Inputs1719.K_U4RootLine) (hKSp4 : Inputs1719.K_Sp4RootLine)
    (hKG2 : Inputs1719.K_G2RootLine) :
    V₀ ≠ ⊥ → ∀ p : ℕ, p ∈ D.sig → ∀ L ∈ calLp D p, ∀ X : Subgroup G,
      X = conjClosure D.M L → X ∈ calL1Star D p →
        IsU5 (Bar2 X) 2 ∨
        (∃ n : ℕ, IsPowTwo n ∧ IsU4 (Bar2 X) n) ∨
        (∃ n : ℕ, IsSp4 (Bar2 X) n ∧ SwapsParabolics D.T X) ∨
        (X ≠ L ∧ ∃ n : ℕ, IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) ∨
        (∃ n : ℕ, IsPowTwo n ∧ (IsL2 (Bar2 X) n ∨ IsU3 (Bar2 X) n)) := by
  intro hV0 p hp L hL X hXeq hX1
  subst hXeq
  rw [mem_calL1Star] at hX1
  rcases hX1.2 with ⟨f, hg2 | hsp | hu4⟩ | hu5
  · exfalso
    exact seventeen_sixtyseven_l1_g2_false hV hV0 h109 h869 hSg h638 h72 hK35 hKU4 hKSp4 hKG2
      h42 hp hL hg2
  · by_cases hsw : SwapsParabolics D.T (conjClosure D.M L)
    · exact Or.inr (Or.inr (Or.inl ⟨f, hsp, hsw⟩))
    · exfalso
      exact seventeen_sixtyseven_l1_sp4_false hV hV0 h109 h869 hSg h638 h72 hK35 hKU4 hKSp4
        hKG2 h42 hp hL hsp hsw
  · by_cases hpow2 : IsPowTwo f
    · exact Or.inr (Or.inl ⟨f, hpow2, hu4⟩)
    · exfalso
      exact seventeen_sixtyseven_l1_u4_false hV hV0 h109 h869 hSg h638 h72 hK35 hKU4 hKSp4
        hKG2 h42 hp hL hu4 hpow2
  · exact Or.inl hu5

theorem seventeen_sixtyseven_of_mem_calL0Star
    {D : Data G} {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) (h42 : R17_42At D V₀ V) (h109 : Inputs1719.UC2_10_9 D)
    (h869 : F08.R869 D) (hSg : UC6S846.SigmaStd D) (h638 : UC6.R6_38 D) (h72 : F07.R72 D)
    (hK35 : UCK.K35w) (hKU4 : Inputs1719.K_U4RootLine) (hKSp4 : Inputs1719.K_Sp4RootLine)
    (hKG2 : Inputs1719.K_G2RootLine) :
    V₀ ≠ ⊥ → ∀ p : ℕ, p ∈ D.sig → ∀ L ∈ calLp D p, ∀ X : Subgroup G,
      X = conjClosure D.M L → X ∈ calL0Star D p →
        IsU5 (Bar2 X) 2 ∨
        (∃ n : ℕ, IsPowTwo n ∧ IsU4 (Bar2 X) n) ∨
        (∃ n : ℕ, IsSp4 (Bar2 X) n ∧ SwapsParabolics D.T X) ∨
        (X ≠ L ∧ ∃ n : ℕ, IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) ∨
        (∃ n : ℕ, IsPowTwo n ∧ (IsL2 (Bar2 X) n ∨ IsU3 (Bar2 X) n)) := by
  intro hV0 p hp L hL X hXeq hX0
  by_cases hX1 : X ∈ calL1Star D p
  · exact seventeen_sixtyseven_of_mem_calL1Star hV h42 h109 h869 hSg h638 h72 hK35 hKU4 hKSp4
      hKG2 hV0 p hp L hL X hXeq hX1
  · exact seventeen_sixtyseven_of_mem_calL0Star_of_not_calL1Star h42 hV0 p hp L hL X hXeq hX0
      hX1

theorem seventeen_sixtyseven {D : Data G} {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) (h42 : R17_42At D V₀ V) (h109 : Inputs1719.UC2_10_9 D)
    (h869 : F08.R869 D) (hSg : UC6S846.SigmaStd D) (h638 : UC6.R6_38 D) (h72 : F07.R72 D)
    (hK35 : UCK.K35w) : R17_67At D V₀ V :=
  seventeen_sixtyseven_of_mem_calL0Star hV h42 h109 h869 hSg h638 h72 hK35
    Inputs1719.k_U4RootLine_holds Inputs1719.k_Sp4RootLine_holds Inputs1719.k_G2RootLine_holds

end CertD

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
