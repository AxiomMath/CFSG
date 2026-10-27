module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftySeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySixShape
public import CFSG.Quasithin.Vol2.Ch10SecEE3Prod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySixAlt3
public import CFSG.LocalAnalysis.UniquenessCase.UC22BarLemmas
public import CFSG.Quasithin.Background.B682Ambient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclCard
public import CFSG.Quasithin.H13.A5S1327j
public import CFSG.RankThree.ThinCatalog.FiveModels
public import CFSG.GroupTheory.StronglyPEmbeddedRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InP11OfStrongly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Opp
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevProd
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHAut3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem thin8_of_isAlt_five {L : Subgroup G}
    (h : IsAlt (Bar2 L) 5) : F08.Thin8 L := by
  obtain ⟨e⟩ := h
  exact thin8_of_isL2 (CFSG.Quasithin.H13.A5.lieModel_of_alternating_five e)

theorem isL2_PSL2_two_of_isAlt_five {X : Type} [Group X]
    (h : IsAlt X 5) : IsL2 X 2 := by
  obtain ⟨e⟩ := h
  exact CFSG.Quasithin.H13.A5.lieModel_of_alternating_five e

theorem not_isA5xA5_of_isAlt_five {X : Type} [Group X] (h : IsAlt X 5) :
    ¬ IsA5xA5 X := by
  obtain ⟨e⟩ := h
  intro hA
  exact not_isSimpleGroup_of_isA5xA5 (e.isSimpleGroup_congr.mpr
    alternatingGroup.isSimpleGroup_five) hA

theorem jM_eq_five_of_mem_calL5Star
    {D : Data G} {p : ℕ}
    {X : Subgroup G} (hL : X ∈ calLp D p) (hX0 : X ∈ calL0Star D p)
    (hX5 : X ∈ calL5Star D p) : jM D p = 5 := by
  have hj := jM_mem_of_nonempty (D := D) (p := p) ⟨X, hX0⟩
  have hle5 : jM D p ≤ 5 := hj.2.1
  have hAlt : IsAlt (Bar2 X) 5 := hX5.2
  have hthin : F08.Thin8 X := thin8_of_isAlt_five hAlt
  have h1 : X ∉ calL1Star D p := by
    intro hmem
    rw [mem_calL1Star] at hmem
    rcases hmem.2 with ⟨f, hG2 | hSp4 | hU4⟩ | hU5
    · exact not_thin8_of_isG2_bar2 hG2 hthin
    · exact not_thin8_of_isSp4_bar2 hSp4 hthin
    · exact not_thin8_of_isU4_bar2 hU4 hthin
    · exact not_thin8_of_isU5_bar2 hU5 hthin
  have h2 : X ∉ calL2Star D p := by
    intro hmem
    rw [mem_calL2Star] at hmem
    exact hmem.2.1 hL
  have h3 : X ∉ calL3Star D p := by
    intro hmem
    rw [mem_calL3Star] at hmem
    exact not_isA5xA5_of_isAlt_five hAlt hmem.2
  have h4 : X ∉ calL4Star D p := by
    intro hmem
    rw [mem_calL4Star] at hmem
    exact hmem.2.2 hAlt
  rcases Nat.lt_or_ge (jM D p) 5 with hlt | hge
  · have hcases : jM D p = 1 ∨ jM D p = 2 ∨ jM D p = 3 ∨ jM D p = 4 := by omega
    rcases hcases with h | h | h | h
    · exact absurd (by simpa [calL0Star, calLjStar, h] using hX0) h1
    · exact absurd (by simpa [calL0Star, calLjStar, h] using hX0) h2
    · exact absurd (by simpa [calL0Star, calLjStar, h] using hX0) h3
    · exact absurd (by simpa [calL0Star, calLjStar, h] using hX0) h4
  · omega

theorem calL4Star_eq_empty_of_jM_eq_five {D : Data G} {p : ℕ}
    (hX0 : (calL0Star D p).Nonempty) (h5 : jM D p = 5) : calL4Star D p = ∅ := by
  have hj := jM_mem_of_nonempty (D := D) (p := p) hX0
  have := hj.2.2.2 4 (by norm_num) (by omega)
  simpa [calLjStar] using this


theorem eq_five_of_modEq_four {p : ℕ} (hp : p.Prime)
    (h : (2 : ℤ) ^ 2 ≡ -1 [ZMOD (p : ℤ)]) : p = 5 := by
  have hdvd : (p : ℤ) ∣ (5 : ℤ) := by
    have h1 : (p : ℤ) ∣ (-1 : ℤ) - 2 ^ 2 := Int.modEq_iff_dvd.mp h
    simpa using h1
  have hdvd' : p ∣ 5 := by exact_mod_cast hdvd
  rcases (Nat.dvd_prime Nat.prime_five).mp hdvd' with h1 | h1
  · exact absurd h1 hp.ne_one
  · exact h1

theorem card_of_isU3_two {X : Type} [Group X] [Finite X] (h : IsU3 X 2) :
    Nat.card X = 62400 := by
  have h := card_mul_gcd_of_isU3 h
  norm_num at h
  exact h

theorem five_dvd_card_of_isU3_two {X : Type} [Group X] [Finite X] (h : IsU3 X 2) :
    5 ∣ Nat.card X := by
  rw [card_of_isU3_two h]
  norm_num

theorem not_isAlt_five_of_isU3_two {X : Type} [Group X] [Finite X] (h : IsU3 X 2) :
    ¬ IsAlt X 5 := by
  intro hA
  have h1 := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Om8Excl.card_isAlt_five hA
  have h2 := card_of_isU3_two h
  omega

theorem p_eq_five_of_eq_self
    {D : Data G} {V₀ V : Subgroup G} (h42 : R17_42At D V₀ V)
    (h641 : R17_64_1At D V₀ V) (h642 : R17_64_2At D V₀ V) (h643 : R17_64_3At D V₀ V)
    {p : ℕ} (hp : p ∈ D.sig) {L : Subgroup G} (hL : L ∈ calLp D p)
    (hL0 : L ∈ calL0Star D p) (hAlt : IsAlt (Bar2 L) 5) :
    p = 5 ∧ Hinf D.M = Lp D p ∧ P17_64_2 D p 2 := by
  have hthin : F08.Thin8 L := thin8_of_isAlt_five hAlt
  obtain ⟨m, hHinf, hm, -, hL2m⟩ :=
    exists_p1642_isL2_of_self h42 h641 h642 h643 hp hL hL0 hthin
  have hm2 : m = 2 := isL2_field_unique hL2m (isL2_PSL2_two_of_isAlt_five hAlt)
  have h54 : Hyp1754 D p := hyp1754_of_thin_mem_calL0Star D h42 hp hL hL0 hthin
  have hmod := (h643 p h54 m hm).2
  rw [hm2] at hmod
  exact ⟨eq_five_of_modEq_four (D.sig_prime p hp).1 hmod, hHinf,
    hm2 ▸ hm⟩


theorem eq_bot_of_isPGroup_two_of_eq_pElementSubgroup {H : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h2 : IsPGroup 2 ↥H) (hH : H = Opp p H) : H = ⊥ := by
  rw [hH, Opp, eq_bot_iff]
  show Subgroup.closure {x : G | x ∈ H ∧ ∃ k : ℕ, orderOf x = p ^ k} ≤ ⊥
  refine (Subgroup.closure_le (⊥ : Subgroup G)).2 ?_
  rintro x ⟨hxH, k, hk⟩
  obtain ⟨m, hm⟩ := h2 ⟨x, hxH⟩
  have hdvd : orderOf x ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hm)
  have hdvd' : orderOf x ∣ p ^ k := hk ▸ dvd_rfl
  have hcop : Nat.Coprime (2 ^ m) (p ^ k) :=
    (Nat.Coprime.pow _ _) ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have h1 : orderOf x = 1 := by
    have hd : orderOf x ∣ Nat.gcd (2 ^ m) (p ^ k) := Nat.dvd_gcd hdvd hdvd'
    rw [hcop.gcd_eq_one] at hd
    exact Nat.dvd_one.mp hd
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)

theorem exists_cyclic_barImage_Sp (D : Data G) {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h54 : Hyp1754 D 5) (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (h638 : UC6.R6_38 D)
    (h33 : R17_33_2At D V₀ V) (h22 : R17_2_2At D V₀ V hV)
    (h23 : R17_2_3At D V₀ V hV) (h57 : R17_57At D V₀ V) (hspne : Sp D 5 ≠ ⊥) :
    ∃ e : ℕ, 1 ≤ e ∧ Nat.card ↥(barImage D.M (Sp D 5)) = 5 ^ e ∧
      IsCyclic ↥(barImage D.M (Sp D 5)) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hle : barImage D.M (Sp D 5) ≤ CFSG.pCore 5 (Bar2 D.M) :=
    barImage_Sp_le_pCore D hV h54 hThin hCyc h638 h33 h22 h23
  have hP : IsPGroup 5 ↥(barImage D.M (Sp D 5)) := by
    intro x
    obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 5) (G := Bar2 D.M) ⟨x, hle x.2⟩
    exact ⟨n, Subtype.ext (by simpa using congrArg Subtype.val hn)⟩
  have hrank : CFSG.Open.pRank 5 (barImage D.M (Sp D 5)) ≤ 1 := by
    rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pRank_barImage Nat.prime_five
      (by norm_num) (Sp_le D 5)]
    exact h57 5 h54
  have hcyc : IsCyclic ↥(barImage D.M (Sp D 5)) :=
    CFSG.Quasithin.isCyclic_of_pRank_le_one (p := 5) (by norm_num) le_rfl hP hrank
  obtain ⟨e, he⟩ := hP.exists_card_eq
  have hne : barImage D.M (Sp D 5) ≠ ⊥ := by
    intro hbot
    have hleO2 : Sp D 5 ≤ CFSG.Open.pCoreOf 2 D.M :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.le_pCoreOf_of_barImage_eq_bot (Sp_le D 5) hbot
    have h2 : IsPGroup 2 ↥(Sp D 5) := by
      intro x
      obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M ⟨x, hleO2 x.2⟩
      exact ⟨n, Subtype.ext (by simpa using congrArg Subtype.val hn)⟩
    have hidem : Sp D 5 = Opp 5 (Sp D 5) := by
      rw [Sp]
      exact (close16_opp_idem 5
        (centSection D.M (Lp D 5) (CFSG.Open.pCoreOf 2 (Lp D 5)))).symm
    exact hspne (eq_bot_of_isPGroup_two_of_eq_pElementSubgroup Nat.prime_five (by norm_num) h2
      hidem)
  have he1 : 1 ≤ e := by
    by_contra h
    have h0 : e = 0 := by omega
    rw [h0] at he
    simp only [pow_zero] at he
    have hsub : Subsingleton ↥(barImage D.M (Sp D 5)) :=
      (Finite.card_le_one_iff_subsingleton).mp (le_of_eq he)
    exact hne (Subgroup.eq_bot_of_subsingleton _)
  exact ⟨e, he1, he, hcyc⟩


theorem false_of_isL2U3Product_two {D : Data G} (h54 : Hyp1754 D 5)
    (hHinf : Hinf D.M = Lp D 5) (hEmpty : calL4Star D 5 = ∅)
    (hu3 : IsL2U3Product (Bar2 (Lp D 5)) 2) : False := by
  obtain ⟨A, B, gA, gB, ⟨eAB⟩, hA2, hB2⟩ := hu3
  letI := gA
  letI := gB
  haveI : IsSimpleGroup A := LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hA2
  haveI : IsSimpleGroup B := LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hB2
  have hAab : ¬ ∀ x y : A, x * y = y * x := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2 (p := 2) (f := 2) hA2
    exact fun h => hab (h a b)
  have hBab : ¬ ∀ x y : B, x * y = y * x :=
    fun h => not_isMulCommutative_of_isU3 hB2 (isMulCommutative_iff.mpr h)
  have hsym : Bar2 (Hinf D.M) ≃* A × B :=
    (MulEquiv.cast (M := fun x : Subgroup G => Bar2 x) (by rw [hHinf])).trans eAB
  obtain ⟨KA, KB, -, hKB, -, ⟨eKB⟩, -⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.exists_two_calC_of_bar2_hinf_prod hAab hBab hsym
  have hKBu3 : IsU3 (Bar2 KB) 2 := LieModel.of_mulEquiv eKB.symm hB2
  have hKBnorm : (KB.subgroupOf D.M).Normal := (h54.2 KB hKB).1
  have hXeq : conjClosure D.M KB = KB := uc22p2214_conjClosure_eq_of_normal hKB.1.le hKBnorm
  have h5KB : 5 ∣ Nat.card KB :=
    (five_dvd_card_of_isU3_two hKBu3).trans (Subgroup.card_quotient_dvd_card _)
  have hKBcalLp : KB ∈ calLp D 5 := ⟨hKB, Nat.prime_five, h5KB⟩
  have hmem : conjClosure D.M KB ∈ calL4Star D 5 := by
    refine ⟨⟨KB, hKBcalLp, rfl⟩, ⟨1, ?_⟩, ?_⟩
    · right
      rw [hXeq]
      simpa using hKBu3
    · rw [hXeq]
      exact not_isAlt_five_of_isU3_two hKBu3
  rw [hEmpty] at hmem
  exact hmem


theorem isAlt_five_of_isL2_two {X : Type} [Group X]
    (h : IsL2 X 2) : IsAlt X 5 := by
  obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := LieModel.statedClassicalModel h (by decide)
  letI := hfield
  letI := hfinite
  have h4 : Nat.card K = 4 := by simpa using hK
  obtain ⟨e5⟩ :=
    CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K (Or.inl h4)
  exact ⟨e.trans e5⟩

theorem center_eq_bot_of_isA5xA5 {X : Type} [Group X] (h : IsA5xA5 X) :
    Subgroup.center X = ⊥ := by
  obtain ⟨e⟩ := h
  exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e
    (by rw [Subgroup.center_prod, alternatingGroup.center_eq_bot (by norm_num),
      Subgroup.bot_prod_bot])


theorem isA5A5Cyclic5_of_eq_self
    {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V) (h54 : Hyp1754 D 5)
    (h56 : R17_56At D V₀ V) (h57 : R17_57At D V₀ V) (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (h638 : UC6.R6_38 D)
    (h33 : R17_33_2At D V₀ V) (h22 : R17_2_2At D V₀ V hV)
    (h23 : R17_2_3At D V₀ V hV) {L : Subgroup G} (hL : L ∈ calLp D 5)
    (hL0 : L ∈ calL0Star D 5) (hXeq : conjClosure D.M L = L) (hAlt : IsAlt (Bar2 L) 5)
    (hHinf : Hinf D.M = Lp D 5) (hP : P17_64_2 D 5 2) :
    IsA5A5Cyclic5
      ↥(CFSG.RankThree.PartOne.pElementSubgroup 5 (⊤ : Subgroup (Bar2 D.M))) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hLstar : L ∈ calLpStar D 5 := (mem_calLpStar).2 ⟨L, hL, hXeq.symm⟩
  have hL5 : L ∈ calL5Star D 5 := ⟨hLstar, hAlt⟩
  have hj5 : jM D 5 = 5 := jM_eq_five_of_mem_calL5Star hL hL0 hL5
  have hEmpty : calL4Star D 5 = ∅ := calL4Star_eq_empty_of_jM_eq_five ⟨L, hL0⟩ hj5
  have hsq : IsL2Square (Bar2 (Lp D 5)) 2 ∧ Sp D 5 ≠ ⊥ := by
    rcases hP with h | h
    · exact h
    · exact (false_of_isL2U3Product_two h54 hHinf hEmpty h.1).elim
  obtain ⟨hL2sq, hspne⟩ := hsq
  have hOpp : Opp 5 D.M = Lp D 5 ⊔ Sp D 5 := by
    rcases h56 5 h54 with h | h
    · exact h
    · exact absurd h.1 (by norm_num)
  obtain ⟨e, he1, hBcard, hBcyc⟩ := exists_cyclic_barImage_Sp D hV h54 hThin hCyc h638 h33
    h22 h23 h57 hspne
  let A : Subgroup (Bar2 D.M) := barImage D.M (Lp D 5)
  let B : Subgroup (Bar2 D.M) := barImage D.M (Sp D 5)
  have hAn : A.Normal := by
    show (barImage D.M (Lp D 5)).Normal
    exact s13_barImage_normal (s13_Lp_normal D.M 5)
  have hBn : B.Normal := by
    show (barImage D.M (Sp D 5)).Normal
    rw [show Sp D 5 = CFSG.LocalAnalysis.UniquenessCase.UC22.F13.Sp D.M 5 from sp_eq_f13Sp D 5]
    exact s13_barImage_normal (s13_Sp_normal D.M 5)
  obtain ⟨e1, -⟩ := uc22p20d_bar2Equiv (s13_Lp_le D.M 5)
    (CFSG.Open.IsSubnormal.step (s13_Lp_le D.M 5) (s13_Lp_normal D.M 5)
      (CFSG.Open.IsSubnormal.refl D.M))
  obtain ⟨A₀, B₀, gA₀, gB₀, ⟨e0⟩, hA₀, hB₀⟩ := hL2sq
  letI := gA₀
  letI := gB₀
  obtain ⟨eA₀⟩ := isAlt_five_of_isL2_two (X := A₀) hA₀
  obtain ⟨eB₀⟩ := isAlt_five_of_isL2_two (X := B₀) hB₀
  have hAiso : ↥A ≃* alternatingGroup (Fin 5) × alternatingGroup (Fin 5) :=
    e1.symm.trans (e0.trans (eA₀.prodCongr eB₀))
  have hA5 : IsA5xA5 ↥A := ⟨hAiso⟩
  have hBiso : ↥B ≃* Multiplicative (ZMod (5 ^ e)) := by
    have h := (zmodCyclicMulEquiv hBcyc).symm
    rw [hBcard] at h
    exact h
  have hBcent : B ≤ Subgroup.centralizer (A : Set (Bar2 D.M)) := by
    change barImage D.M (Sp D 5) ≤
      Subgroup.centralizer (barImage D.M (Lp D 5) : Set (Bar2 D.M))
    have h := s13_barImage_Sp (M := D.M) (p := 5) Nat.prime_five
    have hBA : barImage D.M (Sp D 5) =
        barImage D.M (CFSG.LocalAnalysis.UniquenessCase.UC22.F13.Sp D.M 5) := by
      rw [sp_eq_f13Sp]
    have hAeq : barImage D.M (Lp D 5) =
        CFSG.RankThree.PartOne.pElementSubgroup 5 (CFSG.layer (Bar2 D.M)) :=
      s13_barImage_Lp D.M Nat.prime_five
    rw [hBA, h, hAeq]
    exact s13_Thirteen2_pElementSubgroup_le 5 _
  have hdisj : A ⊓ B = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left A hBcent).trans_eq
      (CFSG.AGLEmbedding.inf_centralizer_eq_bot_of_center (center_eq_bot_of_isA5xA5 hA5)))
  have hjoin : A ⊔ B =
      CFSG.RankThree.PartOne.pElementSubgroup 5 (⊤ : Subgroup (Bar2 D.M)) := by
    have h1 : barImage D.M (Opp 5 D.M) =
        CFSG.RankThree.PartOne.pElementSubgroup 5 (⊤ : Subgroup (Bar2 D.M)) := by
      rw [s13_barImage_opp (p := 5) Nat.prime_five (le_refl D.M),
        CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_barImage_self]
    calc A ⊔ B = barImage D.M (Lp D 5 ⊔ Sp D 5) :=
          (s13_barImage_sup (Lp_le_M D 5) (Sp_le D 5)).symm
      _ = barImage D.M (Opp 5 D.M) := by rw [hOpp]
      _ = _ := h1
  have eprod : ↥A × ↥B ≃* ↥(A ⊔ B) :=
    CFSG.Quasithin.Vol2.Ch10.SecE.prodEquivSup (P₁ := A) (P₂ := B) (fun a ha b hb =>
      Subgroup.commute_of_normal_of_disjoint _ _ hAn hBn (disjoint_iff.2 hdisj)
        a b ha hb) hdisj
  have eprod' : ↥A × ↥B ≃*
      ↥(CFSG.RankThree.PartOne.pElementSubgroup 5 (⊤ : Subgroup (Bar2 D.M))) :=
    eprod.trans (MulEquiv.cast (M := fun x : Subgroup (Bar2 D.M) => ↥x) hjoin)
  refine ⟨e, he1, ⟨eprod'.symm.trans ((hAiso.prodCongr hBiso).trans
    (MulEquiv.prodAssoc (M := alternatingGroup (Fin 5))
      (N := alternatingGroup (Fin 5)) (P := Multiplicative (ZMod (5 ^ e)))))⟩⟩


theorem pRank_five_alternating_five :
    CFSG.Open.pRank 5 (⊤ : Subgroup (alternatingGroup (Fin 5))) = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcardA5 : Nat.card (alternatingGroup (Fin 5)) = 60 :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Om8Excl.card_isAlt_five
      (X := alternatingGroup (Fin 5)) ⟨MulEquiv.refl _⟩
  refine le_antisymm ?_ ?_
  · refine CFSG.SectionRank.pRank_le (by norm_num : 1 < 5) ?_
    intro E _ hE
    obtain ⟨k, hk⟩ : ∃ k, Nat.card ↥E = 5 ^ k :=
      IsPGroup.iff_card.1 fun g => ⟨1, Subtype.ext (by
        rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact hE.2 _ g.2)⟩
    have hdvd : 5 ^ k ∣ 60 := by
      rw [← hk, ← hcardA5]
      exact Subgroup.card_subgroup_dvd_card E
    have hk1 : k ≤ 1 := by
      by_contra h
      have h2 : 2 ≤ k := by omega
      exact absurd ((Nat.pow_dvd_pow 5 h2).trans hdvd) (by norm_num)
    calc Nat.card ↥E = 5 ^ k := hk
      _ ≤ 5 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 5 ^ 1 := rfl
  · have hdvd : 5 ∣ Nat.card (alternatingGroup (Fin 5)) := by rw [hcardA5]; norm_num
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := alternatingGroup (Fin 5)) 5 hdvd
    have hx5 : x ^ 5 = 1 := by
      have h := pow_orderOf_eq_one x
      rwa [hx] at h
    have hE := CFSG.Open.isElemAbelian_zpowers (p := 5) hx5
    have hcardE : Nat.card ↥(Subgroup.zpowers x) = 5 ^ 1 := by
      rw [Nat.card_zpowers, hx]; norm_num
    exact CFSG.SectionRank.le_pRank (by norm_num : 1 < 5) le_top hE hcardE

theorem pRank_five_eq_three {D : Data G}
    (h : IsA5A5Cyclic5
      ↥(CFSG.RankThree.PartOne.pElementSubgroup 5 (⊤ : Subgroup (Bar2 D.M)))) :
    CFSG.Open.pRank 5 D.M = 3 := by
  obtain ⟨e, he1, ⟨m⟩⟩ := h
  have h1 : CFSG.Open.pRank 5 D.M =
      CFSG.Open.pRank 5 (CFSG.RankThree.PartOne.pElementSubgroup 5
        (⊤ : Subgroup (Bar2 D.M))) := by
    rw [← CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pRank_bar_top Nat.prime_five
      (by norm_num) D.M]
    exact (CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pRank_pElementSubgroup
      Nat.prime_five (⊤ : Subgroup (Bar2 D.M))).symm
  rw [h1, CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num) m]
  have hA5 : CFSG.Open.pRank 5 (⊤ : Subgroup (alternatingGroup (Fin 5))) = 1 :=
    pRank_five_alternating_five
  have hZ : CFSG.Open.pRank 5 (⊤ : Subgroup (Multiplicative (ZMod (5 ^ e)))) = 1 := by
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    exact CFSG.LocalAnalysis.RankThreeUC.S15.RankChevProof.pRank_multiplicative_zmod he1
  have h2 : CFSG.Open.pRank 5
      (⊤ : Subgroup (alternatingGroup (Fin 5) × (alternatingGroup (Fin 5) ×
        Multiplicative (ZMod (5 ^ e))))) =
      CFSG.Open.pRank 5 (⊤ : Subgroup (alternatingGroup (Fin 5))) +
        CFSG.Open.pRank 5 (⊤ : Subgroup (alternatingGroup (Fin 5) ×
          Multiplicative (ZMod (5 ^ e)))) := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top,
      CFSG.Quasithin.H13.NQBlock.pRank_prod_eq (p := 5) Nat.prime_five,
      CFSG.SectionRank.pRank_eq_open_pRank_top,
      CFSG.SectionRank.pRank_eq_open_pRank_top]
  have h3 : CFSG.Open.pRank 5 (⊤ : Subgroup (alternatingGroup (Fin 5) ×
      Multiplicative (ZMod (5 ^ e)))) =
      CFSG.Open.pRank 5 (⊤ : Subgroup (alternatingGroup (Fin 5))) +
        CFSG.Open.pRank 5 (⊤ : Subgroup (Multiplicative (ZMod (5 ^ e)))) := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top,
      CFSG.Quasithin.H13.NQBlock.pRank_prod_eq (p := 5) Nat.prime_five,
      CFSG.SectionRank.pRank_eq_open_pRank_top,
      CFSG.SectionRank.pRank_eq_open_pRank_top]
  rw [h2, h3, hA5, hZ]

theorem pRank_le_eM_of_odd_prime {M : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p M ≤ eM M := by
  unfold eM
  refine le_csSup ?_ ?_
  · refine ⟨Nat.card M, ?_⟩
    rintro n ⟨q, hq, hq2, rfl⟩
    exact CFSG.RankThreeEvenClassification.Helpers.pRank_le_card q hq M
  · exact ⟨p, hp, hp2, rfl⟩

theorem eM_eq_three {D : Data G} (hDE : DataExt D) (hp5 : 5 ∈ D.sig)
    (hm5 : CFSG.Open.pRank 5 D.M = 3) : eM D.M = 3 := by
  have hge : 3 ≤ eM D.M := by
    have := pRank_le_eM_of_odd_prime (M := D.M) Nat.prime_five (by norm_num)
    omega
  have hle : eM D.M ≤ 3 := by
    rcases lt_or_eq_of_le D.standing.rank with h4 | h3
    · have h4le : 4 ≤ CFSG.Open.pRank 5 D.M := hDE.four_le h4 5 hp5
      omega
    · exact (CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.eM_le_evenRank D).trans
        (le_of_eq h3.symm)
  omega

theorem Hinf_oTwoEOf_le_Opp_five {D : Data G} {V₀ V : Subgroup G}
    (h641 : R17_64_1At D V₀ V) (h54 : Hyp1754 D 5) :
    Hinf (oTwoEOf D.M) ≤ Opp 5 D.M := by
  have h1 : Hinf (oTwoEOf D.M) ≤ Hinf D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21c_le_Hinf
      (P := Hinf (oTwoEOf D.M)) (K := D.M)
      ((CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21c_Hinf_le
        (oTwoEOf D.M)).trans (Subgroup.map_subtype_le _))
      (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21c_Hinf_perfect _)
  rw [h641 5 h54] at h1
  exact h1.trans (CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_Thirteen2_pElementSubgroup_mono
    (Subgroup.map_subtype_le _))


theorem seventeen_sixtyeight_of_eq_self
    {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h42 : R17_42At D V₀ V) (h56 : R17_56At D V₀ V) (h57 : R17_57At D V₀ V)
    (h641 : R17_64_1At D V₀ V) (h642 : R17_64_2At D V₀ V) (h643 : R17_64_3At D V₀ V)
    (hThin : ThinList13) (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian)
    (h638 : UC6.R6_38 D) (h33 : R17_33_2At D V₀ V) (h22 : R17_2_2At D V₀ V hV)
    (h23 : R17_2_3At D V₀ V hV) (hDE : DataExt D) :
    ∀ p : ℕ, p ∈ D.sig → ∀ L ∈ calLp D p, ∀ X : Subgroup G, X = conjClosure D.M L →
      X ∈ calL0Star D p → IsAlt (Bar2 L) 5 → X = L →
        p = 5 ∧ eM D.M = 3 ∧
          IsA5A5Cyclic5
            ↥(CFSG.RankThree.PartOne.pElementSubgroup 5 (⊤ : Subgroup (Bar2 D.M))) ∧
          Hinf (oTwoEOf D.M) ≤ Opp 5 D.M := by
  intro p hp L hL X hXeq hX0 hAlt hXL
  have hL0 : L ∈ calL0Star D p := hXL ▸ hX0
  obtain ⟨hp5, hHinf, hP2⟩ :=
    p_eq_five_of_eq_self h42 h641 h642 h643 hp hL hL0 hAlt
  subst hp5
  have h54 : Hyp1754 D 5 :=
    hyp1754_of_thin_mem_calL0Star D h42 hp hL hL0 (thin8_of_isAlt_five hAlt)
  have hA5C := isA5A5Cyclic5_of_eq_self hV h54 h56 h57 hThin hCyc h638 h33 h22 h23
    hL hL0 (hXeq.symm.trans hXL) hAlt hHinf hP2
  exact ⟨rfl, eM_eq_three hDE h54.1 (pRank_five_eq_three hA5C), hA5C,
    Hinf_oTwoEOf_le_Opp_five h641 h54⟩


theorem p_eq_five_of_ne
    {D : Data G} {V₀ V : Subgroup G} (h42 : R17_42At D V₀ V) {p : ℕ} (hp : p ∈ D.sig)
    {L : Subgroup G} (hL : L ∈ calLp D p) (hne : conjClosure D.M L ≠ L)
    (hAlt : IsAlt (Bar2 L) 5) :
    p = 5 ∧ CFSG.Open.evenRank G = 3 := by
  obtain ⟨n, x, -, -, -, hshape, hmore⟩ := p42_alt2_of_ne h42 hp hL.1 hne
  have hp5 : p = 5 := by
    rcases hshape with ⟨hL2n, hmod⟩ | ⟨hSzn, -⟩
    · have hn : n = 2 := isL2_field_unique hL2n (isL2_PSL2_two_of_isAlt_five hAlt)
      rw [hn] at hmod
      exact eq_five_of_modEq_four (D.sig_prime p hp).1 hmod
    · exfalso
      have hsz : CFSG.Blueprint.SuzukiModel (Bar2 L) 2 n := by
        have h' := hSzn
        unfold IsSz CFSG.Blueprint.LieModel at h'
        rcases h' with h1 | h2 | h3 | h4
        · exact absurd h1.1 (by decide)
        · exact absurd h2.2.1 (by decide)
        · exact absurd h3.2.1 (by decide)
        · exact h4.2.2
      have h3 : 3 ∣ Nat.card (Bar2 L) := by
        rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.Om8Excl.card_isAlt_five hAlt]
        norm_num
      exact CFSG.RankThree.ThinCatalog.not_three_dvd_card_of_suzukiModel hsz h3
  exact ⟨hp5, hmore.1⟩


theorem not_dvd_card_mulAut_of_isA5xA5 {Q : Type} [Group Q] [Finite Q] (hQ : IsA5xA5 Q)
    {r : ℕ} (hr : r.Prime) (hr5 : 5 < r) : ¬ r ∣ Nat.card (MulAut Q) := by
  intro hdvd
  obtain ⟨e⟩ := hQ
  have hcard : Nat.card (MulAut Q) = 28800 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact CFSG.EvenSporadicStandard.TwoHS.card_mulAut_A5A5
  rw [hcard] at hdvd
  have hfac : r ∣ 2 ^ 7 * 3 ^ 2 * 5 ^ 2 := by
    norm_num
    exact hdvd
  have hcases : r ∣ 2 ∨ r ∣ 3 ∨ r ∣ 5 := by
    rcases (Nat.Prime.dvd_mul hr).mp hfac with h | h
    · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
      · exact Or.inl (hr.dvd_of_dvd_pow h)
      · exact Or.inr (Or.inl (hr.dvd_of_dvd_pow h))
    · exact Or.inr (Or.inr (hr.dvd_of_dvd_pow h))
  rcases hcases with h | h | h
  · have := Nat.le_of_dvd (by norm_num) h
    omega
  · have := Nat.le_of_dvd (by norm_num) h
    omega
  · have := Nat.le_of_dvd (by norm_num) h
    omega

theorem commutator_le_pCoreOf_of_isA5xA5
    {X S : Subgroup G} {r : ℕ} (hr : r.Prime) (hr5 : 5 < r) (hScard : Nat.card S = r)
    (hSX : S ≤ Subgroup.normalizer (X : Set G)) (hXbar : IsA5xA5 (Bar2 X)) :
    ⁅X, S⁆ ≤ pCoreOf 2 X := by
  classical
  rw [Subgroup.commutator_le]
  intro x hx s hs
  by_contra hcon
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact hcon (by simp)
  haveI : Fintype ↥S := Fintype.ofFinite _
  have hspow : s ^ r = 1 := by
    have h := pow_card_eq_one (x := (⟨s, hs⟩ : ↥S))
    rw [show Fintype.card ↥S = r by rw [← Nat.card_eq_fintype_card, hScard]] at h
    exact Subtype.ext_iff.mp h
  let e : MulAut ↥X := X.normalizerMonoidHom ⟨s, hSX hs⟩
  have heN : (CFSG.pCore 2 ↥X).map (e : ↥X →* ↥X) = CFSG.pCore 2 ↥X :=
    (Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (CFSG.pCore 2 ↥X).Characteristic)) e
  let φ : MulAut (Bar2 X) :=
    QuotientGroup.congr (CFSG.pCore 2 ↥X) (CFSG.pCore 2 ↥X) e heN
  have hepow : e ^ r = 1 := by
    have h1 : (⟨s, hSX hs⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ r = 1 := by
      ext
      simpa using hspow
    rw [← map_pow, h1, map_one]
  have hφpow : φ ^ r = 1 := by
    have hpow : ∀ k : ℕ, ∀ y : ↥X, (φ ^ k) (↑y) = ↑((e ^ k) y) := by
      intro k
      induction k with
      | zero => intro y; simp
      | succ k ih =>
          intro y
          rw [pow_succ', MulAut.mul_apply, ih, pow_succ', MulAut.mul_apply]
          exact QuotientGroup.congr_mk _ _ e heN _
    refine MulEquiv.ext fun y => ?_
    induction y using QuotientGroup.induction_on with
    | _ y =>
        rw [hpow r y, hepow]
        rfl
  have hφ1 : φ ≠ 1 := by
    intro hφ
    apply hcon
    have hfix : ∀ y : ↥X, QuotientGroup.mk' (CFSG.pCore 2 ↥X) (e y) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥X) y := by
      intro y
      have := congrArg (fun ψ : MulAut (Bar2 X) => ψ (QuotientGroup.mk' (CFSG.pCore 2 ↥X) y)) hφ
      simpa [φ, QuotientGroup.congr_mk] using this
    have hy : (e ⟨x, hx⟩)⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 ↥X :=
      QuotientGroup.eq.mp (hfix ⟨x, hx⟩)
    have hy2 : ⟨x, hx⟩ * (e ⟨x, hx⟩)⁻¹ ∈ CFSG.pCore 2 ↥X := by
      have hconj := (CFSG.pCore_normal (p := 2) (G := ↥X)).conj_mem
        ((e ⟨x, hx⟩)⁻¹ * ⟨x, hx⟩) hy ⟨x, hx⟩
      have heq : ⟨x, hx⟩ * ((e ⟨x, hx⟩)⁻¹ * ⟨x, hx⟩) * ⟨x, hx⟩⁻¹ =
          ⟨x, hx⟩ * (e ⟨x, hx⟩)⁻¹ := by group
      rwa [heq] at hconj
    have hy3 : e ⟨x, hx⟩ * ⟨x, hx⟩⁻¹ ∈ CFSG.pCore 2 ↥X := by
      simpa using (CFSG.pCore 2 ↥X).inv_mem hy2
    have hval : ((e ⟨x, hx⟩ * ⟨x, hx⟩⁻¹ : ↥X) : G) = s * x * s⁻¹ * x⁻¹ := by
      simp [e, Subgroup.normalizerMonoidHom_apply_apply_coe, mul_assoc]
    have hmem : ((e ⟨x, hx⟩ * ⟨x, hx⟩⁻¹ : ↥X) : G) ∈ pCoreOf 2 X :=
      Subgroup.mem_map.mpr ⟨_, hy3, rfl⟩
    rw [hval] at hmem
    have hmem2 : ⁅s, x⁆ ∈ pCoreOf 2 X := by
      rw [commutatorElement_def]
      exact hmem
    have hinv : ⁅x, s⁆ = ⁅s, x⁆⁻¹ := by
      have h := commutatorElement_inv x s
      rw [← h, inv_inv]
    rw [hinv]
    exact (pCoreOf 2 X).inv_mem hmem2
  have hdvd_ord : orderOf φ ∣ r := orderOf_dvd_iff_pow_eq_one.mpr hφpow
  have hord : orderOf φ = r := by
    rcases Nat.Prime.eq_one_or_self_of_dvd hr _ hdvd_ord with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hφ1
    · exact h1
  haveI : Fintype (Bar2 X) := Fintype.ofFinite _
  have hdvd : r ∣ Nat.card (MulAut (Bar2 X)) := by
    rw [Nat.card_eq_fintype_card, ← hord]
    exact orderOf_dvd_card
  exact not_dvd_card_mulAut_of_isA5xA5 hXbar hr hr5 hdvd


theorem false_of_prime_order_acting_trivially
    {D : Data G}
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 D.M)
    {X S : Subgroup G} {g : G} {r : ℕ}
    (hXM : X ≤ D.M) (hXn : D.M ≤ Subgroup.normalizer (X : Set G))
    (h5X : 5 ∣ Nat.card X)
    (hSM : S ≤ D.M) (hr : r.Prime) (hr5 : 5 < r) (hScard : Nat.card S = r)
    (hcomm : ⁅X, S⁆ ≤ pCoreOf 2 X)
    (hg : g ∉ D.M)
    (hND : Subgroup.normalizer (S : Set G) ≤ CFSG.Quasithin.conjSubgroup D.M g) :
    False := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime r) := ⟨hr⟩
  haveI : Fintype ↥X := Fintype.ofFinite _
  have h5card : 5 ∣ Fintype.card ↥X := by
    rw [← Nat.card_eq_fintype_card]
    exact h5X
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card (G := ↥X) 5 h5card
  set R : Subgroup G := Subgroup.zpowers (z : G) with hR
  have hzX : (z : G) ∈ X := z.2
  have hRX : R ≤ X := by
    rintro _ ⟨k, rfl⟩
    exact X.zpow_mem hzX k
  have hRM : R ≤ D.M := hRX.trans hXM
  have hRcard : Nat.card R = 5 := by
    rw [hR, Nat.card_zpowers, Subgroup.orderOf_coe, hzord]
  have hRp : IsPGroup 5 ↥R := IsPGroup.of_card (n := 1) (by rw [hRcard]; norm_num)
  have hRel : IsElemAbelian 5 R := by
    haveI : IsCyclic ↥R := Subgroup.isCyclic_zpowers (z : G)
    refine ⟨IsCyclic.isMulCommutative, ?_⟩
    intro y hy
    haveI : Fintype ↥R := Fintype.ofFinite _
    have h := pow_card_eq_one (x := (⟨y, hy⟩ : ↥R))
    rw [show Fintype.card ↥R = 5 by rw [← Nat.card_eq_fintype_card, hRcard]] at h
    exact Subtype.ext_iff.mp h
  have hrank : 0 < CFSG.Open.pRank 5 R := by
    have h1 : 1 ≤ CFSG.Open.pRank 5 R :=
      CFSG.SectionRank.le_pRank (p := 5) (by norm_num) (H := R) (E := R) le_rfl hRel
        (k := 1) (by rw [hRcard]; norm_num)
    omega
  have hNp : IsPGroup 2 ↥(pCoreOf 2 X) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  obtain ⟨m, hm⟩ := hNp.exists_card_eq
  have h5N : ¬ 5 ∣ Nat.card ↥(pCoreOf 2 X) := by
    rw [hm]
    intro h
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_five h) (by norm_num)
  have hrN : ¬ r ∣ Nat.card ↥(pCoreOf 2 X) := by
    rw [hm]
    intro h
    have h2 : r ∣ 2 := Nat.Prime.dvd_of_dvd_pow hr h
    have := (Nat.dvd_prime Nat.prime_two).mp h2
    omega
  have hXN : X ≤ Subgroup.normalizer (X : Set G) := fun x hx => Subgroup.le_normalizer hx
  have hRM' : R ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    hRX.trans (hXN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X))
  have hSM' : S ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    hSM.trans (hXn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X))
  have hcommR : ⁅R, S⁆ ≤ pCoreOf 2 X :=
    (Subgroup.commutator_mono hRX le_rfl).trans hcomm
  have hSp : IsPGroup r ↥S := IsPGroup.of_card (n := 1) (by rw [hScard]; norm_num)
  have hrank_le := CFSG.GroupTheory.pRank_le_pRank_inf_centralizer_of_commutator_le
    (M := D.M) (N := pCoreOf 2 X) (R := R) (B := S)
    hRM ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXM) hRM' hSM' hRp hSp h5N hrN hcommR
  have hpos : 0 < CFSG.Open.pRank 5 (D.M ⊓ Subgroup.centralizer (S : Set G)) :=
    lt_of_lt_of_le hrank hrank_le
  have hle : D.M ⊓ Subgroup.centralizer (S : Set G) ≤
      D.M ⊓ CFSG.Quasithin.conjSubgroup D.M g :=
    le_inf inf_le_left (inf_le_right.trans
      ((Subgroup.centralizer_le_normalizer (S : Set G)).trans hND))
  exact hg (CFSG.GroupTheory.mem_of_pRank_pos_of_le_inf_conjSubgroup Nat.prime_five hsp hle hpos)


theorem exists_conj_normalizer_of_sz {D : Data G} {V₀ V : Subgroup G}
    (h55 : R17_55At D V₀ V) (h3 : R17_3At D V₀ V)
    {J B : Subgroup G} {n r : ℕ}
    (hJ : J ∈ calC D.M) (hJn : (J.subgroupOf D.M).Normal)
    (hSz : IsSz (Bar2 J) n) (hnodd : Odd n)
    (hr : r.Prime) (hr7 : 7 ≤ r) (hrdvd : r ∣ 2 ^ n - 1)
    (hBJ : B ≤ J) (hBcard : Nat.card B = r) :
    ∃ (K : Subgroup G) (g : G), K ≤ D.M ∧ Nat.card K = r ∧ g ∉ D.M ∧
      Subgroup.normalizer (K : Set G) ≤ CFSG.Quasithin.conjSubgroup D.M g := by
  classical
  have hJM : J ≤ D.M := hJ.1.le
  have hBM : B ≤ D.M := hBJ.trans hJM
  have hineq := h55 J hJM hJn n (Or.inr hSz) n hnodd (dvd_refl n) r hr hrdvd B hBJ hBcard
  have hsub : conjSetOf D.M B ⊆
      conjSetOf (⊤ : Subgroup G) B ∩ {Y : Subgroup G | Y ≤ D.M} := by
    rintro K ⟨g, hg, rfl⟩
    refine ⟨⟨g, trivial, rfl⟩, ?_⟩
    rintro y ⟨b, hb, rfl⟩
    exact D.M.mul_mem (D.M.mul_mem hg (hBM hb)) (D.M.inv_mem hg)
  have hex : ∃ K, K ∈ conjSetOf (⊤ : Subgroup G) B ∩ {Y : Subgroup G | Y ≤ D.M} ∧
      K ∉ conjSetOf D.M B := by
    by_contra h
    push Not at h
    exact hineq (Set.Subset.antisymm (fun K hK => h K hK) hsub)
  obtain ⟨K, ⟨⟨g, -, hKg⟩, hKM⟩, hKnot⟩ := hex
  have hg : g ∉ D.M := by
    intro hgm
    exact hKnot (hKg ▸ ⟨g, hgm, rfl⟩)
  have hNB : Subgroup.normalizer (B : Set G) ≤ D.M :=
    h3 J hJ (thin8_of_isSz hSz) B ⟨r, hr, by omega, hBcard, hBJ⟩
  refine ⟨K, g⁻¹, hKM, ?_, ?_, ?_⟩
  · rw [hKg, Subgroup.card_map_of_injective (MulAut.conj g).injective, hBcard]
  · intro h
    exact hg (by simpa using D.M.inv_mem h)
  · rw [hKg, ← Subgroup.map_normalizer_eq_of_bijective B (MulAut.conj g).bijective]
    rintro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hEq : CFSG.Quasithin.conjSubgroup D.M g⁻¹ =
        D.M.map (MulAut.conj g).toMonoidHom := by
      rw [CFSG.Quasithin.conjSubgroup, inv_inv]
    rw [hEq]
    exact Subgroup.mem_map.mpr ⟨y, hNB hy, rfl⟩

theorem false_of_sz_component
    {D : Data G} {V₀ V : Subgroup G}
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 D.M)
    (h55 : R17_55At D V₀ V) (h3 : R17_3At D V₀ V)
    {X J B : Subgroup G} {n r : ℕ}
    (hXM : X ≤ D.M) (hXn : D.M ≤ Subgroup.normalizer (X : Set G))
    (h5X : 5 ∣ Nat.card X) (hXbar : IsA5xA5 (Bar2 X))
    (hJ : J ∈ calC D.M) (hJn : (J.subgroupOf D.M).Normal)
    (hSz : IsSz (Bar2 J) n) (hnodd : Odd n)
    (hr : r.Prime) (hr7 : 7 ≤ r) (hrdvd : r ∣ 2 ^ n - 1)
    (hBJ : B ≤ J) (hBcard : Nat.card B = r) :
    False := by
  obtain ⟨K, g, hKM, hKcard, hg, hNK⟩ :=
    exists_conj_normalizer_of_sz h55 h3 hJ hJn hSz hnodd hr hr7 hrdvd hBJ hBcard
  exact false_of_prime_order_acting_trivially hsp hXM hXn h5X hKM hr (by omega) hKcard
    (commutator_le_pCoreOf_of_isA5xA5 hr (by omega) hKcard (hKM.trans hXn) hXbar)
    hg hNK


theorem k_eq_two_of_permuting_e9 {D : Data G} {V₀ V : Subgroup G} {hV : Hyp125 D V₀ V}
    (h1 : R17_1At D V₀ V hV) {E : Subgroup G} (hEM : E ≤ D.M)
    (hEel : IsElemAbelian 3 E) (hperm : Permutes E D.T)
    (hrank : 2 ≤ CFSG.Open.pRank 3 E) : D.k = 2 := by
  have hk12 : D.k = 1 ∨ D.k = 2 := by
    unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
    split <;> simp
  rcases hk12 with hk | hk
  · exfalso
    have hnc : ¬ IsCyclic ↥E := by
      intro hcyc
      have := CFSG.SectionRank.pRank_le_one_of_isCyclic Nat.prime_three hcyc
      omega
    have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
      by_contra h
      have h2 : D.k = 2 := by
        unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
        simp [h]
      omega
    have hin : F11.InP11 D E :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.inP11_of_strongly Nat.prime_three (by norm_num)
        hsp hEM hEel.isPGroup hEel.2 hnc hperm
    have hk2 : D.k = 2 := (h1.2 ⟨E, hin⟩).2.1
    omega
  · exact hk

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
