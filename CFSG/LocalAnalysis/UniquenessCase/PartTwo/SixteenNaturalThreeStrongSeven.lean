module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ComponentCentralizingStrongEmbedding
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeCases
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeK7Residual
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeCentralizerRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3SmallRowsB6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3SmallCount
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Engine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeArithmetic
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K33PartialRanks

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem seven_subgroup_le_s1t3KBar_of_threeNat
    {W : Type} [CommGroup W] [Finite W] {A B T : Subgroup (MulAut W)}
    (hT : ThreeNat A B T)
    (h7 : Nat.card ↥(irrSet B) = 7)
    (h7B : ¬ 7 ∣ Nat.card ↥B)
    {P : Subgroup (MulAut W)} (hP : IsPGroup 7 P) (hPA : P ≤ A) :
    P ≤ s1t3KBar A B := by
  classical
  have hKle : s1t3KBar A B ≤ A := inf_le_left
  have hBnorm : (B.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hT.le).mpr hT.normal
  have hKcenter : (s1t3KBar A B).subgroupOf A =
      Subgroup.centralizer (B.subgroupOf A : Set ↥A) := by
    ext x
    change (x : MulAut W) ∈ A ⊓ Subgroup.centralizer (B : Set (MulAut W)) ↔
      x ∈ Subgroup.centralizer (B.subgroupOf A : Set ↥A)
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨-, hx⟩ y hy
      exact Subtype.ext (hx (y : MulAut W) (Subgroup.mem_subgroupOf.mp hy))
    · intro hx
      refine ⟨x.2, ?_⟩
      intro y hy
      have hyA : y ∈ A := hT.le hy
      exact congrArg Subtype.val (hx ⟨y, hyA⟩ (Subgroup.mem_subgroupOf.mpr hy))
  have hKnormal : ((s1t3KBar A B).subgroupOf A).Normal := by
    rw [hKcenter]
    exact Subgroup.normal_centralizer
  obtain ⟨N, hNA, hBN, hNfix, hcomm, hNKbot, hNKsup, hKcard⟩ := hT.structure_of_seven h7
  have h7K : 7 ∣ Nat.card ↥(s1t3KBar A B) := by
    rcases hKcard with h | h | ⟨h, -⟩ <;> rw [h] <;> norm_num
  let Q := ↥A ⧸ (s1t3KBar A B).subgroupOf A
  have hAcard : Nat.card ↥A = Nat.card ↥(s1t3KBar A B) * Nat.card Q := by
    have h := (Subgroup.card_mul_index ((s1t3KBar A B).subgroupOf A)).symm
    rw [Subgroup.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv] at h
    exact h
  have hAdvd : Nat.card ↥A ∣ 336 * Nat.card ↥B := hT.card_dvd_of_seven h7
  obtain ⟨t, ht⟩ := h7K
  have h7Qdvd : 7 * Nat.card Q ∣ Nat.card ↥A := by
    refine ⟨t, ?_⟩
    rw [hAcard, ht]
    ring
  have hQdvd : Nat.card Q ∣ 48 * Nat.card ↥B := by
    have h336 : 336 * Nat.card ↥B = 7 * (48 * Nat.card ↥B) := by ring
    have h' : 7 * Nat.card Q ∣ 7 * (48 * Nat.card ↥B) := by
      rw [← h336]
      exact h7Qdvd.trans hAdvd
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 7)).mp h'
  have h7notQ : ¬ 7 ∣ Nat.card Q := by
    intro h
    apply h7B
    rcases (Nat.Prime.dvd_mul Nat.prime_seven).1 (h.trans hQdvd) with h48 | hB
    · norm_num at h48
    · exact hB
  let π : ↥A →* Q := QuotientGroup.mk' ((s1t3KBar A B).subgroupOf A)
  have himg : IsPGroup 7 ((P.subgroupOf A).map π) :=
    IsPGroup.map (hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPA).symm) π
  have himgdvd : Nat.card ↥((P.subgroupOf A).map π) ∣ Nat.card Q := by
    simpa using Subgroup.card_dvd_of_le (le_top : (P.subgroupOf A).map π ≤ ⊤)
  have himgbot : (P.subgroupOf A).map π = ⊥ := by
    rcases IsPGroup.card_eq_or_dvd (p := 7) (G := ↥((P.subgroupOf A).map π)) himg with
      h1 | h7dvd
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exact absurd (h7dvd.trans himgdvd) h7notQ
  intro x hx
  have hxK : (⟨x, hPA hx⟩ : ↥A) ∈ (s1t3KBar A B).subgroupOf A := by
    have hxmem : π ⟨x, hPA hx⟩ = 1 := by
      have hmem : π ⟨x, hPA hx⟩ ∈ (P.subgroupOf A).map π :=
        ⟨⟨x, hPA hx⟩, hx, rfl⟩
      rw [himgbot] at hmem
      exact hmem
    have hker : (⟨x, hPA hx⟩ : ↥A) ∈ π.ker := MonoidHom.mem_ker.mpr hxmem
    rwa [QuotientGroup.ker_mk'] at hker
  exact Subgroup.mem_subgroupOf.mp hxK

theorem s168e3_strongly_seven_of_threeNat
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (h869 : F08.R869 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsimple : IsSimpleGroup ↥(lBar V₀ V hV L))
    (hrank : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      2 ≤ CFSG.Open.pRank q (⊤ : Subgroup ↥(lBar V₀ V hV L)))
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L)
      (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (h7B : ¬ 7 ∣ Nat.card ↥(lBar V₀ V hV L)) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 7 D.M := by
  classical
  have h125 : Hyp125 D V₀ V := c.setting.hyp16.hyp125
  have hms : D.M ≤ stabTil V₀ V := c.m_le_stabTil
  have hdvdA : Nat.card ↥(Mbar D.M V₀ V hV) ∣ Nat.card ↥D.M := by
    let φ : ↥D.M →* MulAut (Vtil V₀ V hV) := barHom V₀ V hV hms
    have hrange : φ.range = Mbar D.M V₀ V hV := by
      simpa only [φ, Mbar] using range_barHom V₀ V hV hms
    let f : ↥D.M →* ↥(Mbar D.M V₀ V hV) :=
      φ.codRestrict _ fun m => hrange ▸ MonoidHom.mem_range.2 ⟨m, rfl⟩
    have hf : Function.Surjective f := by
      intro y
      have hy : (y : MulAut (Vtil V₀ V hV)) ∈ φ.range := by
        rw [hrange]
        exact y.2
      obtain ⟨m, hm⟩ := MonoidHom.mem_range.1 hy
      exact ⟨m, Subtype.ext hm⟩
    exact Subgroup.card_dvd_of_surjective hf
  have h7A : 7 ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
    obtain ⟨-, -, -, -, -, -, -, hKcard⟩ := hT.structure_of_seven h7
    have h7K : 7 ∣ Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) := by
      rcases hKcard with h | h | ⟨h, -⟩ <;> rw [h] <;> norm_num
    exact h7K.trans (Subgroup.card_dvd_of_le
      (inf_le_left : s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) ≤
        Mbar D.M V₀ V hV))
  have hpM : 7 ∣ Nat.card ↥D.M := h7A.trans hdvdA
  refine isStronglyPEmbedded_of_component_action_centralization h125 c.std.h127 c.std.h119 h869
    hcomp hsimple hrank Nat.prime_seven (by norm_num) hpM ?_
  intro P hP hPM
  have hPA : barSub V₀ V hV P ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hPM
  have hP7 : IsPGroup 7 (barSub V₀ V hV P) := by
    have hPsub : IsPGroup 7 (P.subgroupOf (stabTil V₀ V)) :=
      hP.of_equiv (Subgroup.subgroupOfEquivOfLe (hPM.trans hms)).symm
    exact hPsub.map (actTil V₀ V hV)
  exact (seven_subgroup_le_s1t3KBar_of_threeNat hT h7 h7B hP7 hPA).trans inf_le_right

theorem s168e3_strongly_seven_of_threeNat_alt_six
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (h869 : F08.R869 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L)
      (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hAlt6 : UC22.IsAlt ↥(lBar V₀ V hV L) 6) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 7 D.M := by
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) :=
    s16c167_cfg2_simple_alt (by norm_num) hAlt6
  have hcard : Nat.card ↥(lBar V₀ V hV L) = 360 := by
    rw [s15k_six_alt_card hAlt6 (by norm_num)]
    norm_num
  have h7B : ¬ 7 ∣ Nat.card ↥(lBar V₀ V hV L) := by
    rw [hcard]
    norm_num
  have hrank : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      2 ≤ CFSG.Open.pRank q (⊤ : Subgroup ↥(lBar V₀ V hV L)) := by
    refine ⟨3, Nat.prime_three, by norm_num, ?_⟩
    have h := CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.pRank_three_eq_two_of_isAlt_six
      hAlt6
    omega
  exact s168e3_strongly_seven_of_threeNat c h869 hcomp hsimple hrank hT h7 h7B

theorem s168e3_false_of_sum_three_alt_six
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (h869 : F08.R869 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsum : SumOfNatShape (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L),
      ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓ Subgroup.normalizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))),
        I₂ = I₁.map g.toMonoidHom)
    (hs : s15 D.M V₀ V hV L = 1)
    (hA6 : UC22.IsAlt ↥(lBar V₀ V hV L) 6) : False := by
  have hT := s168e3_threeNat_of_s15_eq_one c hcomp hsum htrans hs
  have h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7 :=
    s168e3_irrSet_seven_of_bounded c hcomp hsum htrans hs
      ⟨6, Or.inr (Or.inr (Or.inr (Or.inr ⟨hA6, by norm_num⟩)))⟩
  have hm : MBarGT D.M V₀ V 2 := mBarGT_two_of_threeNat c.setting hT
  have hcard : Nat.card ↥(lBar V₀ V hV L) = 360 := by
    rw [s15k_six_alt_card hA6 (by norm_num : 2 ≤ 6)]
    norm_num [Nat.factorial]
  have harith : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 →
      ¬ p ^ 2 ∣ 336 * Nat.card ↥(lBar V₀ V hV L) := by
    intro p hp hp2 hp3
    rw [hcard]
    exact s168e3_not_sq_dvd_336_mul hp hp2 hp3 (by norm_num)
  have hsig : D.sig = {3} := s168e3_sig_eq_three_of_threeNat_card c hT h7 harith
  have h3 : 3 ∈ D.sig := by
    rw [hsig]
    exact Set.mem_singleton 3
  obtain ⟨-, -, -, -, -, -, -, hKcard⟩ := hT.structure_of_seven h7
  rcases hKcard with hK7 | hK21 | ⟨hK168, -⟩
  · exact (s168e3_not_strongly_seven_of_kBar_card_seven c hT h7 hK7)
      (s168e3_strongly_seven_of_threeNat_alt_six c h869 hcomp hT h7 hA6)
  · exact c.setting.false_of_kBar_order_21 c.std.h638 h3 hT h7 hK21
  · obtain ⟨Y, hYM, hY3, hYexp, hYnc, hperm, -⟩ :=
      s168e3_exists_permuting_three_alt_six_k168 c hT h7 hA6 hK168
    refine false_of_permuting_three_of_weakClosure D c.std.hx c.std.hSg c.std.h61 c.std.h63
      c.std.h126 c.std.h1211 c.std.h111 c.std.h6161ii
      (c.std.h1219 V₀ V c.setting.hyp16.hyp125)
      c.setting h3 hm hYM hY3 hYexp hYnc hperm ?_
    by_cases hV₀ : V₀ = ⊥
    · exact Or.inr (Or.inr
        (c.setting.exists_good_vector_alt6 c.std.h61 h3 hV₀ hT h7 hA6 hK168))
    · exact Or.inl hV₀

theorem s168e3_concl163F_of_sum_three_alt_six
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (h869 : F08.R869 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsum : SumOfNatShape (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L),
      ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓ Subgroup.normalizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))),
        I₂ = I₁.map g.toMonoidHom)
    (hs : s15 D.M V₀ V hV L = 1)
    (hA6 : UC22.IsAlt ↥(lBar V₀ V hV L) 6) :
    Concl163F D V₀ V hV L :=
  False.elim (s168e3_false_of_sum_three_alt_six c h869 hcomp hsum htrans hs hA6)

theorem s168e3_false_of_sum_three_omega_minus_six
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (h869 : F08.R869 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsum : SumOfNatShape (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L),
      ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓ Subgroup.normalizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))),
        I₂ = I₁.map g.toMonoidHom)
    (hs : s15 D.M V₀ V hV L = 1)
    (hOm : IsOmegaMinus ↥(lBar V₀ V hV L) 6 1) : False := by
  have hT := s168e3_threeNat_of_s15_eq_one c hcomp hsum htrans hs
  have h7 := s168e3_irrSet_seven_of_sum_three c hcomp hsum htrans hs
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) :=
    s16c1_isSimpleGroup_of_isOmegaMinus_six hOm
  have hcard : Nat.card ↥(lBar V₀ V hV L) = 25920 :=
    s16c1_card_isOmegaMinus_six hOm
  have h7B : ¬ 7 ∣ Nat.card ↥(lBar V₀ V hV L) := by
    rw [hcard]
    norm_num
  have hrank : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      2 ≤ CFSG.Open.pRank q (⊤ : Subgroup ↥(lBar V₀ V hV L)) := by
    obtain ⟨E, hE, hEcard⟩ := s15k_om6_exists_e27 hOm
    have h3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(lBar V₀ V hV L)) :=
      CFSG.SectionRank.le_pRank (p := 3) (k := 3) (by norm_num) (H := ⊤) (E := E)
        le_top hE (by rw [hEcard]; norm_num)
    exact ⟨3, Nat.prime_three, by norm_num, by omega⟩
  have hstr := s168e3_strongly_seven_of_threeNat c h869 hcomp hsimple hrank hT h7 h7B
  have h3K := s168e3_three_not_dvd_kBar_of_omega_minus_six c hcomp hOm
  obtain ⟨-, -, -, -, -, -, -, hKcard⟩ := hT.structure_of_seven h7
  have hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 7 := by
    rcases hKcard with h | h | ⟨h, -⟩
    · exact h
    · exact absurd (by rw [h]; norm_num :
        3 ∣ Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L))) h3K
    · exact absurd (by rw [h]; norm_num :
        3 ∣ Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L))) h3K
  exact (s168e3_not_strongly_seven_of_kBar_card_seven c hT h7 hK) hstr

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
