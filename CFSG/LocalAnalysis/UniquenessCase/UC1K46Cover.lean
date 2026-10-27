module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K32
public import CFSG.LocalAnalysis.UniquenessCase.UC1K462Inputs
public import CFSG.GH74.Generic.BProg.B2.L2Cover
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3M
public import CFSG.GH74.Generic.Context
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.GH74.E2.ComponentsShape
public import CFSG.GH74.Generic.S45.LLift
public import CFSG.LocalAnalysis.SectionRank.CyclicCenter
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.LieType.Steinberg.CentralExt.PSL2Multiplier
public import CFSG.LieType.Steinberg.CentralExt.PSLMultiplier
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr
public import CFSG.LieType.SeitzGeneration.OrthExLift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcTwistedE6
public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs462
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL2Abs
public import CFSG.RankThree.PartOne.CTP.SeitzOrthModel
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.CTP.StrongPFinal
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import Certificates.Certificate5007

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor)
open scoped MatrixGroups

namespace Cover46

theorem not_three_dvd_card_center {G : Type} [Group G] [Finite G]
    (hperf : commutator G = ⊤) (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup G) = 1) :
    ¬ 3 ∣ Nat.card (Subgroup.center G) := by
  haveI : Group.IsPerfect G := Group.isPerfect_def.mpr hperf
  intro h3
  have hpL : 3 ∣ Nat.card G := h3.trans (Subgroup.card_subgroup_dvd_card (Subgroup.center G))
  have h2 := (CFSG.SectionRank.perfect_cyclic_center_odd_elements (L := G) (p := 3)
    (by norm_num) hpL).2 h3
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
  omega

theorem no_odd_center_of_hopf_eq_two_or_six {G : Type} [Group G] [Finite G]
    (hG' : CFSG.IsQuasisimple G) (h3Z : ¬ 3 ∣ Nat.card (Subgroup.center G))
    (hM : Nat.card (CFSG.Open.griessHopfMultiplier (G ⧸ Subgroup.center G)) = 2 ∨
      Nat.card (CFSG.Open.griessHopfMultiplier (G ⧸ Subgroup.center G)) = 6) :
    ¬ ∃ z : G, z ≠ 1 ∧ (∀ g : G, g * z = z * g) ∧ Odd (orderOf z) := by
  have hMdvd : Nat.card (Subgroup.center G) ∣
      Nat.card (CFSG.Open.griessHopfMultiplier (G ⧸ Subgroup.center G)) :=
    CFSG.ClassicalInvolution.Q3.TL4.E3S3M.natCard_center_dvd hG'
      (MulEquiv.refl (G ⧸ Subgroup.center G))
  rintro ⟨z, hz1, hzc, hzodd⟩
  have hzZ : z ∈ Subgroup.center G := Subgroup.mem_center_iff.2 hzc
  have hzdvd : orderOf z ∣ Nat.card (Subgroup.center G) :=
    Subgroup.orderOf_dvd_natCard (Subgroup.center G) hzZ
  have hdvd : orderOf z ∣
      Nat.card (CFSG.Open.griessHopfMultiplier (G ⧸ Subgroup.center G)) :=
    hzdvd.trans hMdvd
  rcases hM with hM | hM
  · rw [hM] at hdvd
    have hone : orderOf z = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact h
      · exact absurd (h ▸ hzodd) (by decide)
    exact hz1 (orderOf_eq_one_iff.1 hone)
  · rw [hM] at hdvd
    rw [show (6 : ℕ) = 3 * 2 by norm_num] at hdvd
    have hdvd3 : orderOf z ∣ 3 :=
      (Nat.coprime_two_right.2 hzodd).dvd_of_dvd_mul_right hdvd
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd3 with h | h
    · exact hz1 (orderOf_eq_one_iff.1 h)
    · exact h3Z (h ▸ hzdvd)

theorem psl2_odd_of_lieModel
    {G : Type} [Group G] [Finite G]
    (hG : CFSG.Open.IsQuasisimple G) (h3Z : ¬ 3 ∣ Nat.card (Subgroup.center G))
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : LieModel (G ⧸ Subgroup.center G) .PSL 2 p f) :
    (∃ p f : ℕ, LieModel G .PSL 2 p f) ∨
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧
        Nonempty (G ≃* SL(2, F))) := by
  obtain ⟨-, hf, F, _, _, hFcard, ⟨e₀⟩⟩ := CFSG.GH74.Generic.lieModel_psl_data hL
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Group.IsPerfect G := Group.isPerfect_def.mpr hG.1
  have hG' : CFSG.IsQuasisimple G :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff G).2.2.1.mpr hG
  let e : (G ⧸ Subgroup.center G) ≃* PSL(2, F) :=
    e₀.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have hoddF : Odd (Fintype.card F) := by
    rw [Fintype.card_eq_nat_card, hFcard]
    exact (hp.odd_of_ne_two hp2).pow
  have hpf3 : p ^ f ≠ 3 := by
    have hadm := CFSG.Blueprint.LieModel.admissible hL
    intro h
    exact hadm.2.2.2.2 (Prod.ext rfl h)
  have h5 : 5 ≤ Fintype.card F := by
    rw [Fintype.card_eq_nat_card, hFcard]
    have h3 : 3 ≤ p ^ f := by
      have hge : 3 ≤ p := by have := hp.two_le; omega
      exact hge.trans (Nat.le_self_pow (by omega) p)
    have hne4 : p ^ f ≠ 4 := by
      intro h4
      have hpdvd : p ∣ p ^ f := dvd_pow_self p (by omega : f ≠ 0)
      rw [h4] at hpdvd
      have hpdvd2 : p ∣ 2 ^ 2 := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num] at hpdvd
        exact hpdvd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hpdvd2))
    omega
  have hM : Nat.card (CFSG.Open.griessHopfMultiplier (G ⧸ Subgroup.center G)) = 2 ∨
      Nat.card (CFSG.Open.griessHopfMultiplier (G ⧸ Subgroup.center G)) = 6 := by
    rw [Nat.card_congr
      (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv]
    exact CFSG.ClassicalInvolution.Q3.TL4.E3S3M.natCard_hopf_psl2 hoddF h5
  have hnoOdd : ¬ ∃ z : G, z ≠ 1 ∧ (∀ g : G, g * z = z * g) ∧ Odd (orderOf z) :=
    no_odd_center_of_hopf_eq_two_or_six hG' h3Z hM
  have h2 : IsPGroup 2 ↥(Subgroup.center G) :=
    CFSG.GH74.Generic.BProg.B2.L2Cover.isPGroup_two_center_of_no_odd hnoOdd
  have hoddFn : Odd (Nat.card F) := Fintype.card_eq_nat_card ▸ hoddF
  have h5n : 5 ≤ Nat.card F := by rw [← Fintype.card_eq_nat_card]; exact h5
  rcases CFSG.GH74.Generic.BProg.B2.L2Cover.l2_cover_two_group hG' h2 hoddFn h5n e with
    hbot | ⟨h2card, ⟨φ⟩⟩
  · left
    obtain ⟨eGX⟩ := CFSG.GH74.Generic.nonempty_mulEquiv_of_center_eq_bot hbot
      (MulEquiv.refl (G ⧸ Subgroup.center G))
    exact ⟨p, f, CFSG.Blueprint.LieModel.of_mulEquiv eGX.symm hL⟩
  · right
    exact ⟨F, inferInstance, inferInstance, hoddFn, ⟨φ⟩⟩

theorem psl2_even_center_eq_bot
    {G : Type} [Group G] [Finite G]
    (hG : CFSG.Open.IsQuasisimple G) {f : ℕ} (hf2 : f ≠ 2)
    (hL : LieModel (G ⧸ Subgroup.center G) .PSL 2 2 f) :
    Subgroup.center G = ⊥ := by
  have hadm := CFSG.Blueprint.LieModel.admissible hL
  have hpf2 : 2 ^ f ≠ 2 := fun h => hadm.2.2.2.1 (Prod.ext rfl h)
  have hf3 : 3 ≤ f := by
    have h1 : 1 ≤ f := hadm.2.1
    have : f ≠ 1 := fun h => hpf2 (by rw [h]; norm_num)
    omega
  obtain ⟨-, hf, F, _, _, hFcard, ⟨e₀⟩⟩ := CFSG.GH74.Generic.lieModel_psl_data hL
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Group.IsPerfect G := Group.isPerfect_def.mpr hG.1
  have hG' : CFSG.IsQuasisimple G :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff G).2.2.1.mpr hG
  let e : (G ⧸ Subgroup.center G) ≃* PSL(2, F) :=
    e₀.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have hk : 5 ≤ Fintype.card F := by
    rw [Fintype.card_eq_nat_card, hFcard]
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
  have hk9 : Fintype.card F ≠ 9 := by
    rw [Fintype.card_eq_nat_card, hFcard]
    intro h
    have h2dvd : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    rw [h] at h2dvd
    norm_num at h2dvd
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SL2Closed.psl_two_hopfMultiplier
    (k := F) hk hk9
  have hg : Nat.gcd 2 (Fintype.card F - 1) = 1 := by
    rw [Fintype.card_eq_nat_card, hFcard]
    have h2even : Even (2 ^ f : ℕ) :=
      (even_two : Even (2 : ℕ)).pow_of_ne_zero (by omega : f ≠ 0)
    have hodd : Odd (2 ^ f - 1) :=
      Nat.Even.sub_odd (Nat.one_le_two_pow) h2even (odd_one : Odd (1 : ℕ))
    exact (Nat.coprime_two_left.2 hodd).gcd_eq_one
  have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (G ⧸ Subgroup.center G)) =
      Nat.gcd 2 (Fintype.card F - 1) := by
    rw [Nat.card_congr
        ((CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).trans eM).toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hdvd := CFSG.ClassicalInvolution.Q3.TL4.E3S3M.natCard_center_dvd hG'
    (MulEquiv.refl (G ⧸ Subgroup.center G))
  rw [hcard, hg] at hdvd
  exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 hdvd)

theorem psl3_center_eq_bot {G : Type} [Group G] [Finite G]
    (hG : CFSG.Open.IsQuasisimple G) (h3Z : ¬ 3 ∣ Nat.card (Subgroup.center G))
    {p f : ℕ} (hmod : p ^ f % 3 = 2) (hq2 : p ^ f ≠ 2)
    (hL : LieModel (G ⧸ Subgroup.center G) .PSL 3 p f) :
    Subgroup.center G = ⊥ := by
  obtain ⟨-, hf, F, _, _, hFcard, ⟨e₀⟩⟩ := CFSG.GH74.Generic.lieModel_psl_data hL
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Group.IsPerfect G := Group.isPerfect_def.mpr hG.1
  have hG' : CFSG.IsQuasisimple G :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff G).2.2.1.mpr hG
  let e : (G ⧸ Subgroup.center G) ≃* PSL(3, F) :=
    e₀.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm
  have hpf3 : 3 ≤ p ^ f := by
    by_contra h
    have hlt : p ^ f < 3 := by omega
    have hmod' : p ^ f % 3 = p ^ f := Nat.mod_eq_of_lt hlt
    rw [hmod'] at hmod
    exact hq2 hmod
  have hpf4 : p ^ f ≠ 4 := by
    intro h; rw [h] at hmod; norm_num at hmod
  have hq3 : 3 ≤ Fintype.card F := by rwa [Fintype.card_eq_nat_card, hFcard]
  have hq4 : Fintype.card F ≠ 4 := by rwa [Fintype.card_eq_nat_card, hFcard]
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_hopfMultiplier_of_three_le
    (k := F) (n := 3) le_rfl hq3 (fun h => hq4 h.2)
  have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (G ⧸ Subgroup.center G)) =
      Nat.gcd 3 (Fintype.card F - 1) := by
    rw [Nat.card_congr
        ((CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).trans eM).toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hdvd := CFSG.ClassicalInvolution.Q3.TL4.E3S3M.natCard_center_dvd hG'
    (MulEquiv.refl (G ⧸ Subgroup.center G))
  rw [hcard] at hdvd
  have hdvd3 : Nat.card (Subgroup.center G) ∣ 3 := hdvd.trans (Nat.gcd_dvd_left 3 _)
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd3 with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    exact h3Z (by simpa [h3])

theorem psu3_center_eq_bot
    {G : Type} [Group G] [Finite G]
    (hG : CFSG.Open.IsQuasisimple G) (h3Z : ¬ 3 ∣ Nat.card (Subgroup.center G))
    {p f : ℕ} (hmod : p ^ f % 3 = 1)
    (hL : LieModel (G ⧸ Subgroup.center G) .PSU 3 p f) :
    Subgroup.center G = ⊥ := by
  obtain ⟨hp, hf, F, _, _, hFcard, ⟨e₀⟩⟩ := CFSG.GH74.Generic.lieModel_psu_data hL
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP F p := CFSG.LieType.Steinberg.charP_of_card_eq_sq_pow hp hFcard
  haveI : Group.IsPerfect G := Group.isPerfect_def.mpr hG.1
  have hG' : CFSG.IsQuasisimple G :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff G).2.2.1.mpr hG
  have hne : ((3 : ℕ), p ^ f) ≠ (3, 2) := by
    intro h2
    have h2' : p ^ f = 2 := (Prod.mk.inj h2).2
    rw [h2'] at hmod
    norm_num at hmod
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SUOdd.psu_odd_hopfMultiplier
    (hF := hFcard) (hf := hf) (n := 3) (by norm_num) (by decide) hne
  have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (G ⧸ Subgroup.center G)) =
      Nat.gcd 3 (p ^ f + 1) := by
    rw [Nat.card_congr
        ((CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e₀).trans eM).toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hdvd := CFSG.ClassicalInvolution.Q3.TL4.E3S3M.natCard_center_dvd hG'
    (MulEquiv.refl (G ⧸ Subgroup.center G))
  rw [hcard] at hdvd
  have hdvd3 : Nat.card (Subgroup.center G) ∣ 3 := hdvd.trans (Nat.gcd_dvd_left 3 _)
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd3 with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    exact h3Z (by simpa [h3])

end Cover46


theorem k46Quasisimple_holds
    : K46Quasisimple := by
  intro G _ _ hK hQ hrank
  haveI : Group.IsPerfect G := Group.isPerfect_def.mpr hQ.1
  have h3Z : ¬ 3 ∣ Nat.card (Subgroup.center G) :=
    Cover46.not_three_dvd_card_center hQ.1 hrank
  let X := G ⧸ Subgroup.center G
  have hXK : CFSG.Open.IsKGroup X := hK.quotient (Subgroup.center G)
  have hXsimple : IsSimpleGroup X := hQ.2
  haveI : Nontrivial X := hXsimple.toNontrivial
  have hXnab : ∃ a b : X, a * b ≠ b * a := by
    haveI : Group.IsPerfect X :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (Subgroup.center G))
    have hnc : ¬ IsMulCommutative X := Group.IsPerfect.not_isMulCommutative X
    rw [isMulCommutative_iff] at hnc
    push Not at hnc
    exact hnc
  have hXrank : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1 := by
    rw [CFSG.SectionRank.pRank_quotient_eq (p := 3) (G := G) (N := Subgroup.center G) h3Z]
    exact hrank
  rcases k32_holds X hXK hXsimple hXnab hXrank with
    ⟨p, f, hL2⟩ | ⟨p, f, hmod3, hL3⟩ | ⟨p, f, hmodU, hLU⟩ | hJ1
  · by_cases hp2 : p = 2
    · subst hp2
      by_cases hf2 : f = 2
      · subst hf2
        have hL5 : LieModel X .PSL 2 5 1 :=
          CFSG.GH74.E2.lieModel_psl_two_five_of_alt
            (CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model X hL2)
        rcases Cover46.psl2_odd_of_lieModel hQ h3Z Nat.prime_five (by norm_num) hL5 with
          h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · have hbot := Cover46.psl2_even_center_eq_bot hQ hf2 hL2
        obtain ⟨e⟩ := CFSG.GH74.Generic.nonempty_mulEquiv_of_center_eq_bot hbot
          (MulEquiv.refl X)
        exact Or.inl ⟨2, f, CFSG.Blueprint.LieModel.of_mulEquiv e.symm hL2⟩
    · have hp : p.Prime := (CFSG.Blueprint.LieModel.admissible hL2).1
      rcases Cover46.psl2_odd_of_lieModel hQ h3Z hp hp2 hL2 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · by_cases hq2 : p ^ f = 2
    · have h321 : LieModel X .PSL 3 2 1 := by
        obtain ⟨-, F, hFld, hFfin, hFcard, ⟨e⟩⟩ :=
          CFSG.Blueprint.LieModel.statedClassicalModel hL3 (by decide)
        have hsc : CFSG.Open.StatedClassicalModel X .PSL 3 2 1 :=
          ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩, F, hFld, hFfin,
            by rw [pow_one]; exact hFcard.trans hq2, ⟨e⟩⟩
        exact Or.inl ⟨by decide, hsc⟩
      have h27 : LieModel X .PSL 2 7 1 :=
        CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism X h321
      rcases Cover46.psl2_odd_of_lieModel hQ h3Z Nat.prime_seven (by norm_num) h27 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · have hbot := Cover46.psl3_center_eq_bot hQ h3Z hmod3 hq2 hL3
      obtain ⟨e⟩ := CFSG.GH74.Generic.nonempty_mulEquiv_of_center_eq_bot hbot (MulEquiv.refl X)
      exact Or.inr (Or.inl ⟨p, f, hmod3, CFSG.Blueprint.LieModel.of_mulEquiv e.symm hL3⟩)
  · have hbot := Cover46.psu3_center_eq_bot hQ h3Z hmodU hLU
    obtain ⟨e⟩ := CFSG.GH74.Generic.nonempty_mulEquiv_of_center_eq_bot hbot (MulEquiv.refl X)
    exact Or.inr (Or.inr (Or.inl ⟨p, f, hmodU, CFSG.Blueprint.LieModel.of_mulEquiv e.symm hLU⟩))
  · obtain ⟨eXJ⟩ := hJ1
    have hNoCov : CFSG.GH74.Generic.S45.NoCentralCover X :=
      CFSG.GH74.Generic.S45.NoCentralCover.of_mulEquiv eXJ.symm
        (CFSG.GH74.Generic.S45.NoCentralCover.of_mulEquiv CFSG.Walter.walterJ1EquivNative
          CFSG.GH74.Generic.S45.noCentralCover_walterJ1)
    have hker : (QuotientGroup.mk' (Subgroup.center G)).ker = ⊥ :=
      hNoCov G (Group.isPerfect_def.mpr hQ.1) (QuotientGroup.mk' (Subgroup.center G))
        (QuotientGroup.mk'_surjective (Subgroup.center G))
        (QuotientGroup.ker_mk' (Subgroup.center G)).le
    have hbot : Subgroup.center G = ⊥ := by
      rw [← QuotientGroup.ker_mk' (Subgroup.center G)]
      exact hker
    obtain ⟨eGX⟩ := CFSG.GH74.Generic.nonempty_mulEquiv_of_center_eq_bot hbot (MulEquiv.refl X)
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨eGX.trans eXJ⟩)))

end CFSG.LocalAnalysis.UniquenessCase.UCK
