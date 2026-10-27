module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.M22CoverPoints
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c4
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214g
public import CFSG.Adapters.LieModelSmallOrders
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InP11OfStrongly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueB
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubBar2Equiv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenNineTransfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsB
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G}

theorem center_bar2_eq_bot_of_M22
    (hV : Hyp125 D V₀ V) (h17_1 : R17_1At D V₀ V hV)
    (hsp3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    (hK : K_M22CoverNine) (c : Ctx17_17 D V₀ V L) (hspor : IsSpor (BarInf L) .M22) :
    Subgroup.center (Bar2 L) = ⊥ := by
  classical
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := c.mem_calC.2.2
  have hodd : Odd (Nat.card (Subgroup.center (Bar2 L))) := by
    simpa [Bar2] using uc22p20p_odd_center_bar2 ↥L
  obtain ⟨eInf⟩ := uc22p21k_barInf_equiv hq
  obtain ⟨eM22⟩ := hspor
  have eZ : Bar2 L ⧸ Subgroup.center (Bar2 L) ≃*
      CFSG.Blueprint.NativeSporadic.M22 :=
    eInf.symm.trans eM22
  have hperf : Group.IsPerfect (Bar2 L) := ⟨hq.1⟩
  obtain ⟨-, hdvd⟩ :=
    CFSG.Sporadic.Recognition.M22Multiplier.center_cyclic_dvd_twelve_of_certificate hperf eZ
  have hcard13 : Nat.card (Subgroup.center (Bar2 L)) = 1 ∨
      Nat.card (Subgroup.center (Bar2 L)) = 3 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    obtain ⟨m, hm⟩ := hodd
    rw [hm] at hdvd hle
    have hm6 : m ≤ 6 := by omega
    interval_cases m <;> omega
  rcases hcard13 with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have hZne : Subgroup.center (Bar2 L) ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at h3
      omega
    have hExists : ∃ X : Subgroup G, X ≤ D.M ∧ X ≠ ⊥ ∧ IsPGroup 3 ↥X ∧
        (∀ x ∈ X, x ^ 3 = 1) ∧ ¬ IsCyclic ↥X ∧ Permutes X D.T := by
      refine exists_permutes_three_of_calC c.mem_calC ?_
      intro Y _ _ K hKn hKq hKodd hKe hKcent hKidx S hSyl
      have hKY : KYForm Y K S := ⟨hKn, hKq, hKodd, hKcent, hKidx, hSyl⟩
      obtain ⟨eK⟩ := hKe
      have hSporK : IsSpor (↥K ⧸ Subgroup.center ↥K) .M22 :=
        ⟨(CFSG.Fischer.quotientCenterCongr eK).trans eZ⟩
      have hZneK : Subgroup.center ↥K ≠ ⊥ := by
        intro hbot
        apply hZne
        rw [← Subgroup.map_center_eq eK, hbot, Subgroup.map_bot]
      exact hK Y K S hKY hSporK hZneK
    obtain ⟨X, hXM, hXne, hXp, hXexp, hXnc, hXperm⟩ := hExists
    have hInP11 : F11.InP11 D X :=
      inP11_of_strongly Nat.prime_three (by norm_num) hsp3 hXM hXp hXexp hXnc hXperm
    have hk1 : D.k = 1 := Data.k_eq_one_of_isStronglyPEmbedded D hsp3
    have hk2 : D.k = 2 := (h17_1.2 ⟨X, hInP11⟩).2.1
    omega

theorem isSpor_barSub_of_M22
    (hV : Hyp125 D V₀ V) (c : Ctx17_17 D V₀ V L)
    (hspor : IsSpor (BarInf L) .M22)
    (hc : Subgroup.center (Bar2 L) = ⊥)
    (hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥) :
    IsSpor (↥(barSub V₀ V hV.isElemAbelian L)) .M22 := by
  classical
  obtain ⟨eInf⟩ := uc22p21k_barInf_equiv_of_center_bot c.mem_calC.2.2 hc
  obtain ⟨eM22⟩ := hspor
  have eZ : Bar2 L ≃* CFSG.Blueprint.NativeSporadic.M22 := eInf.symm.trans eM22
  have : IsSimpleGroup (Bar2 L) :=
    (MulEquiv.isSimpleGroup_congr eZ).mpr CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  have hLS : L ≤ stabTil V₀ V :=
    c.mem_calC.1.le.trans
      (le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀)
  have h2 : barSub V₀ V hV.isElemAbelian (pCoreOf 2 L) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV.isElemAbelian c.mem_calC.1
      (barSub_pCoreOf_eq_bot_of_hyp125 hV)
  obtain ⟨eBar⟩ :=
    nonempty_bar2_mulEquiv_barSub_of_isSimpleGroup hV.isElemAbelian hLS h2 hL1 inferInstance
  exact ⟨eBar.symm.trans eZ⟩

private theorem two_pow_le_of_dvd_443520 {N : ℕ} (h : 2 ^ N ∣ 443520) : N ≤ 7 := by
  by_contra hlt
  have h8 : 2 ^ 8 ∣ 443520 := (pow_dvd_pow 2 (by omega)).trans h
  norm_num at h8

private theorem false_of_ordA_443520 {d f : ℕ} (hd : 2 ≤ d) (hf : 1 ≤ f)
    (hcard : CFSG.Open.ordA (d - 1) (2 ^ f) = 443520) : False := by
  have hprof := CFSG.Timmesfeld.Orders.profile_ordA (n := d - 1) (by omega) hf
  obtain ⟨r, -, hm⟩ := hprof.two
  have hdvd : 2 ^ (f * ((d - 1) * d / 2)) ∣ CFSG.Open.ordA (d - 1) (2 ^ f) := by
    rw [hm, Nat.sub_add_cancel (by omega : 1 ≤ d)]
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 le_rfl) r
  have hN : f * ((d - 1) * d / 2) ≤ 7 :=
    two_pow_le_of_dvd_443520 (hcard ▸ hdvd)
  have hd4 : d ≤ 4 := by
    by_contra hlt
    have h5 : 5 ≤ d := by omega
    have h20 : 4 * 5 ≤ (d - 1) * d := Nat.mul_le_mul (by omega) (by omega)
    have h10 : 10 ≤ (d - 1) * d / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      omega
    have hNle : (d - 1) * d / 2 ≤ f * ((d - 1) * d / 2) :=
      Nat.le_mul_of_pos_left ((d - 1) * d / 2) hf
    omega
  interval_cases d
  · have hf7 : f ≤ 7 := by
      have : f * ((2 - 1) * 2 / 2) ≤ 7 := hN
      norm_num at this
      omega
    interval_cases f <;> exact absurd hcard (by decide)
  · have hf2 : f ≤ 2 := by
      have : f * ((3 - 1) * 3 / 2) ≤ 7 := hN
      norm_num at this
      omega
    interval_cases f <;> exact absurd hcard (by decide)
  · have hf1 : f = 1 := by
      have : f * ((4 - 1) * 4 / 2) ≤ 7 := hN
      norm_num at this
      omega
    subst hf1
    exact absurd hcard (by decide)

private theorem false_of_ordTwistedA_443520 {d f : ℕ} (hd : 3 ≤ d) (hf : 1 ≤ f)
    (hcard : CFSG.Open.ordTwistedA (d - 1) (2 ^ f) = 443520) : False := by
  have hprof := CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := d - 1) (by omega) hf
  obtain ⟨r, -, hm⟩ := hprof.two
  have hdvd : 2 ^ (f * ((d - 1) * d / 2)) ∣
      CFSG.Open.ordTwistedA (d - 1) (2 ^ f) := by
    rw [hm, Nat.sub_add_cancel (by omega : 1 ≤ d)]
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 le_rfl) r
  have hN : f * ((d - 1) * d / 2) ≤ 7 :=
    two_pow_le_of_dvd_443520 (hcard ▸ hdvd)
  have hd4 : d ≤ 4 := by
    by_contra hlt
    have h5 : 5 ≤ d := by omega
    have h20 : 4 * 5 ≤ (d - 1) * d := Nat.mul_le_mul (by omega) (by omega)
    have h10 : 10 ≤ (d - 1) * d / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      omega
    have hNle : (d - 1) * d / 2 ≤ f * ((d - 1) * d / 2) :=
      Nat.le_mul_of_pos_left ((d - 1) * d / 2) hf
    omega
  interval_cases d
  · have hf2 : f ≤ 2 := by
      have : f * ((3 - 1) * 3 / 2) ≤ 7 := hN
      norm_num at this
      omega
    interval_cases f <;> exact absurd hcard (by decide)
  · have hf1 : f = 1 := by
      have : f * ((4 - 1) * 4 / 2) ≤ 7 := hN
      norm_num at this
      omega
    subst hf1
    exact absurd hcard (by decide)

private theorem false_of_ordBC_443520 {d f : ℕ} (hd : 2 ≤ d) (hf : 1 ≤ f)
    (hcard : CFSG.Open.ordBC d (2 ^ f) = 443520) : False := by
  have hprof := CFSG.Timmesfeld.Orders.profile_ordBC (n := d) hf
  obtain ⟨r, -, hm⟩ := hprof.two
  have hdvd : 2 ^ (f * (d * d)) ∣ CFSG.Open.ordBC d (2 ^ f) := by
    rw [hm]
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 le_rfl) r
  have hN : f * (d * d) ≤ 7 := two_pow_le_of_dvd_443520 (hcard ▸ hdvd)
  have hd2 : d = 2 := by
    by_contra hne
    have h3 : 3 ≤ d := by omega
    have h9 : 9 ≤ d * d := by
      simpa using Nat.mul_le_mul h3 h3
    have hle : d * d ≤ f * (d * d) := Nat.le_mul_of_pos_left (d * d) hf
    omega
  subst hd2
  have hf1 : f = 1 := by
    have : f * (2 * 2) ≤ 7 := hN
    omega
  subst hf1
  exact absurd hcard (by decide)

private theorem false_of_ordD_443520 {d f : ℕ} (hd : 4 ≤ d) (hf : 1 ≤ f)
    (hcard : CFSG.Open.ordD d (2 ^ f) = 443520) : False := by
  have hprof := CFSG.Timmesfeld.Orders.profile_ordD (n := d) (by omega) hf
  obtain ⟨r, -, hm⟩ := hprof.two
  have hdvd : 2 ^ (f * (d * (d - 1))) ∣ CFSG.Open.ordD d (2 ^ f) := by
    rw [hm]
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 le_rfl) r
  have hN : f * (d * (d - 1)) ≤ 7 := two_pow_le_of_dvd_443520 (hcard ▸ hdvd)
  have h12 : 4 * 3 ≤ d * (d - 1) := Nat.mul_le_mul hd (by omega)
  have hle : d * (d - 1) ≤ f * (d * (d - 1)) := Nat.le_mul_of_pos_left _ hf
  omega

private theorem false_of_ordTwistedD_443520 {d f : ℕ} (hd : 4 ≤ d) (hf : 1 ≤ f)
    (hcard : CFSG.Open.ordTwistedD d (2 ^ f) = 443520) : False := by
  have hprof := CFSG.Timmesfeld.Orders.profile_ordTwistedD (n := d) (by omega) hf
  obtain ⟨r, -, hm⟩ := hprof.two
  have hdvd : 2 ^ (f * (d * (d - 1))) ∣ CFSG.Open.ordTwistedD d (2 ^ f) := by
    rw [hm]
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 le_rfl) r
  have hN : f * (d * (d - 1)) ≤ 7 := two_pow_le_of_dvd_443520 (hcard ▸ hdvd)
  have h12 : 4 * 3 ≤ d * (d - 1) := Nat.mul_le_mul hd (by omega)
  have hle : d * (d - 1) ≤ f * (d * (d - 1)) := Nat.le_mul_of_pos_left _ hf
  omega

private theorem false_of_ordG2_443520 {f : ℕ} (hf : 1 ≤ f)
    (hcard : CFSG.Open.ordG2 (2 ^ f) = 443520) : False := by
  have hprof := CFSG.Timmesfeld.Orders.profile_ordG2 hf
  obtain ⟨r, -, hm⟩ := hprof.two
  have hdvd : 2 ^ (f * 6) ∣ CFSG.Open.ordG2 (2 ^ f) := by
    rw [hm]
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 le_rfl) r
  have hN : f * 6 ≤ 7 := two_pow_le_of_dvd_443520 (hcard ▸ hdvd)
  have hf1 : f = 1 := by omega
  subst hf1
  exact absurd hcard (by decide)

private theorem false_of_factorial_div_two_443520 {n : ℕ} (hn : 2 ≤ n)
    (hcard : n.factorial / 2 = 443520) : False := by
  have hn12 : n ≤ 12 := by
    by_contra hlt
    have h13 : 13 ≤ n := by omega
    have hle : Nat.factorial 13 ≤ Nat.factorial n := Nat.factorial_le h13
    have hdiv : Nat.factorial 13 / 2 ≤ Nat.factorial n / 2 := Nat.div_le_div_right hle
    have h13val : 443520 < Nat.factorial 13 / 2 := by norm_num
    omega
  interval_cases n <;> exact absurd hcard (by decide)

section OrderCertificates


theorem not_classicalEvenAltG2Der_of_M22
    {X : Type} [Group X] (h : IsSpor X .M22) :
    ¬ CFSG.LocalAnalysis.UniquenessCase.PartTwo.ClassicalEvenAltG2Der X := by
  intro hc
  obtain ⟨eM⟩ := h
  have hcard : Nat.card X = 443520 := by
    rw [Nat.card_congr eM.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M22
  have : IsSimpleGroup X :=
    (MulEquiv.isSimpleGroup_congr eM).mpr CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  rcases hc with hcl | ⟨n, hG2Der⟩
  · rcases hcl with ⟨hq, t, m, f, ht, hLie⟩ | ⟨hq, n, hAlt⟩ | ⟨n, hG2⟩
    · have hqo : CFSG.Open.IsQuasisimple X :=
        ⟨(Group.isPerfect_def).1 hq.1, hq.2.1⟩
      obtain ⟨eQ⟩ := uc22p2214_quotCenter_of_simple (X := X) hqo
      have hLieX : CFSG.Blueprint.LieModel X t m 2 f :=
        CFSG.Blueprint.LieModel.of_mulEquiv eQ.symm hLie
      have hsc : CFSG.Open.StatedClassicalModel X t m 2 f :=
        hLieX.statedClassicalModel (by
          rcases ht with rfl | rfl | rfl | rfl | rfl <;> simp [CFSG.Blueprint.classicalTags])
      have hord := CFSG.Timmesfeld.card_statedClassicalModel_two hsc
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · have hf : 1 ≤ f := hsc.1.2.1
        have hm : 2 ≤ m := hsc.1.2.2.1
        have hcardA : CFSG.Open.ordA (m - 1) (2 ^ f) = 443520 :=
          (hord.1 rfl).symm.trans hcard
        exact false_of_ordA_443520 hm hf hcardA
      · have hf : 1 ≤ f := hsc.1.2.1
        have hm : 3 ≤ m := hsc.1.2.2.1
        have hcardA : CFSG.Open.ordTwistedA (m - 1) (2 ^ f) = 443520 :=
          (hord.2.1 rfl).symm.trans hcard
        exact false_of_ordTwistedA_443520 hm hf hcardA
      · have hf : 1 ≤ f := hsc.1.2.1
        have hm : 2 ≤ m := hsc.1.2.2.1
        have hcardA : CFSG.Open.ordBC m (2 ^ f) = 443520 :=
          (hord.2.2.1 rfl).symm.trans hcard
        exact false_of_ordBC_443520 hm hf hcardA
      · have hf : 1 ≤ f := hsc.1.2.1
        have hm : 4 ≤ m := hsc.1.2.2
        have hcardA : CFSG.Open.ordD m (2 ^ f) = 443520 :=
          (hord.2.2.2.1 rfl).symm.trans hcard
        exact false_of_ordD_443520 hm hf hcardA
      · have hf : 1 ≤ f := hsc.1.2.1
        have hm : 4 ≤ m := hsc.1.2.2
        have hcardA : CFSG.Open.ordTwistedD m (2 ^ f) = 443520 :=
          (hord.2.2.2.2 rfl).symm.trans hcard
        exact false_of_ordTwistedD_443520 hm hf hcardA
    · have hqo : CFSG.Open.IsQuasisimple X :=
        ⟨(Group.isPerfect_def).1 hq.1, hq.2.1⟩
      obtain ⟨eQ⟩ := uc22p2214_quotCenter_of_simple (X := X) hqo
      obtain ⟨eAlt⟩ := hAlt
      have hcardAlt : Nat.card (alternatingGroup (Fin n)) = 443520 := by
        rw [← Nat.card_congr (eQ.trans eAlt).toEquiv]
        exact hcard
      by_cases hn2 : 2 ≤ n
      · have : Nontrivial (Fin n) :=
          Fintype.one_lt_card_iff_nontrivial.mp (by
            rw [Fintype.card_fin]
            omega)
        have hfac : n.factorial / 2 = 443520 := by
          rw [← hcardAlt, nat_card_alternatingGroup, Nat.card_fin]
        exact false_of_factorial_div_two_443520 hn2 hfac
      · have hn1 : n ≤ 1 := by omega
        have hbot : alternatingGroup (Fin n) = ⊥ :=
          alternatingGroup.eq_bot_of_card_le_two (by
            rw [Nat.card_fin]
            omega)
        have h1 : Nat.card (alternatingGroup (Fin n)) = 1 := by
          rw [hbot, Subgroup.card_bot]
        omega
    · have hCE : CFSG.Blueprint.ChevalleyExceptionalModel X .G2 2 n :=
        CFSG.Blueprint.LieModel.chevalleyExceptionalModel hG2 (by decide)
      have hordG2 : Nat.card X = CFSG.Open.ordG2 (2 ^ n) := by
        simpa using CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hCE
      have hn1 : 1 ≤ n := (CFSG.Blueprint.LieModel.admissible hG2).2.1
      exact false_of_ordG2_443520 hn1 (hordG2.symm.trans hcard)
  · rcases hG2Der with ⟨rfl, hLie⟩ | ⟨hn2, hG2⟩
    · have h6048 : Nat.card X = 6048 := CFSG.Blueprint.LieModel.card_psu_three_three hLie
      omega
    · have hCE : CFSG.Blueprint.ChevalleyExceptionalModel X .G2 2 n :=
        CFSG.Blueprint.LieModel.chevalleyExceptionalModel hG2 (by decide)
      have hordG2 : Nat.card X = CFSG.Open.ordG2 (2 ^ n) := by
        simpa using CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hCE
      exact false_of_ordG2_443520 (by omega) (hordG2.symm.trans hcard)

end OrderCertificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
