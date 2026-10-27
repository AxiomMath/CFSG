module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251r
public import CFSG.LocalAnalysis.UniquenessCase.UC22FinThreeN
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251s
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251p
import CFSG.LocalAnalysis.UniquenessCase.UC22P22o
import CFSG.LocalAnalysis.UniquenessCase.UC22P22finA
import CFSG.LocalAnalysis.UniquenessCase.UC22KHi2a
import CFSG.LocalAnalysis.UniquenessCase.UC22FinThreeShape
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bar13
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorBasic
import CFSG.GroupTheory.CharacteristicNormalizer
import CFSG.Foundations.SteinbergCADefinitionNodes
import CFSG.Adapters.LieModelSimple
import CFSG.Quasithin.H13.VolIA38Orders
import CFSG.RankThree.PartOne.S12K.OrdRigidL
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251q

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9 (R920odd)

variable {G : Type} [Group G] [Finite G]

namespace P2251t

private theorem three_dvd_ordA_two (n : ℕ) : 3 ∣ CFSG.Open.ordA 2 (2 ^ n) := by
  have hq2 : 3 ∣ (2 ^ n) ^ 2 - 1 := by
    have := Nat.sub_dvd_pow_sub_pow 4 1 n
    rw [one_pow] at this
    rwa [← pow_mul, mul_comm, pow_mul]
  rw [CFSG.LocalAnalysis.UniquenessCase.UC6.N588.ordA_two_eq]
  by_cases h3 : 3 ∣ 2 ^ n - 1
  · rw [Nat.gcd_eq_left h3]
    exact Nat.dvd_div_of_mul_dvd
      ((mul_dvd_mul hq2 (h3.trans (Nat.sub_one_dvd_pow_sub_one _ 3))).mul_left _)
  · rw [show Nat.gcd 3 (2 ^ n - 1) = 1 from
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3, Nat.div_one]
    exact (hq2.mul_right _).mul_left _

private theorem ordA_two_ne_one {n : ℕ} (hn : n ≠ 0) : CFSG.Open.ordA 2 (2 ^ n) ≠ 1 := by
  obtain ⟨r, hr, hm⟩ := CFSG.Quasithin.H13.VolI.two_part_ordA_two (e := n) (by omega)
  rw [hm]
  have h1 : 1 < 2 ^ (n * 3) := Nat.one_lt_two_pow (by omega)
  have h2 : 2 ^ (n * 3) ≤ 2 ^ (n * 3) * r := Nat.le_mul_of_pos_right _ hr.pos
  omega

private theorem ordA_two_ne_ordA_one_odd {n r : ℕ} (hn : 2 < n) (hrP : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.ordA 2 (2 ^ n) ≠ CFSG.Open.ordA 1 r := by
  intro hA
  have hrodd : Odd r := hrP.odd_of_ne_two hr2
  obtain ⟨d, hd0, hdodd, hmul⟩ : ∃ d, 0 < d ∧ Odd d ∧ CFSG.Open.ordA 2 (2 ^ n) * d =
      2 ^ (n * 3) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
    refine ⟨Nat.gcd 3 (2 ^ n - 1), Nat.gcd_pos_of_pos_left _ (by norm_num),
      Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left _ _), ?_⟩
    rw [CFSG.LocalAnalysis.UniquenessCase.UC6.N588.ordA_two_eq, pow_mul]
    exact Nat.div_mul_cancel ((Nat.gcd_dvd_right _ _).trans
      (((Nat.sub_one_dvd_pow_sub_one _ 2).mul_right _).mul_left _))
  have hEq : r * (r ^ 2 - 1) * d =
      2 * (2 ^ (n * 3) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1))) := by
    rw [← CFSG.LocalAnalysis.UniquenessCase.UC6.N588.two_mul_ordA_one hrodd, ← hA, ← hmul]
    ring
  have hcop : Nat.Coprime (2 * 2 ^ (n * 3)) (r * d) :=
    Nat.Coprime.mul_left (Nat.coprime_two_left.2 (hrodd.mul hdodd))
      ((Nat.coprime_two_left.2 (hrodd.mul hdodd)).pow_left _)
  have hdvd : 2 * 2 ^ (n * 3) ∣ r ^ 2 - 1 :=
    hcop.dvd_of_dvd_mul_left ⟨((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1), by
      rw [show r * d * (r ^ 2 - 1) = r * (r ^ 2 - 1) * d by ring, hEq]
      ring⟩
  obtain ⟨j, rfl⟩ := hrodd
  have hj : (2 * j + 1) ^ 2 - 1 = 4 * (j * (j + 1)) := by
    rw [show (2 * j + 1) ^ 2 = 4 * (j * (j + 1)) + 1 by ring, Nat.add_sub_cancel]
  have h2pow : 2 ^ (n * 3) = 2 * 2 ^ (n * 3 - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hj, h2pow, ← mul_assoc, show 2 * 2 = 4 by norm_num] at hdvd
  have hdvd' := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
  have hle : 2 ^ (n * 3 - 1) ≤ j + 1 := by
    rcases Nat.even_or_odd j with hje | hjo
    · have hc : Nat.Coprime (2 ^ (n * 3 - 1)) (j + 1) :=
        (Nat.coprime_two_left.2 hje.add_one).pow_left _
      have := hc.dvd_of_dvd_mul_right hdvd'
      have hj0 : j ≠ 0 := by rintro rfl; exact Nat.not_prime_one hrP
      exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) this).trans (Nat.le_succ j)
    · have hc : Nat.Coprime (2 ^ (n * 3 - 1)) j := (Nat.coprime_two_left.2 hjo).pow_left _
      exact Nat.le_of_dvd (Nat.succ_pos j) (hc.dvd_of_dvd_mul_left hdvd')
  have hS : 2 ^ (n * 3) ≤ 2 * j + 2 := by
    rw [h2pow]
    omega
  rw [pow_mul] at hEq hS
  generalize hT : 2 ^ n = T at hEq hS
  have hT8 : 8 ≤ T := by
    rw [← hT]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  generalize hA2 : T ^ 2 = A at hEq
  generalize hS3 : T ^ 3 = S at hEq hS
  have hSA : S = T * A := by rw [← hS3, ← hA2]; ring
  have hA1 : 1 ≤ A := by rw [← hA2]; exact Nat.one_le_pow _ _ (by omega)
  have h8A : 8 * A ≤ S := hSA ▸ Nat.mul_le_mul_right A hT8
  have hmono : (S - 1) * ((S - 1) ^ 2 - 1) ≤ (2 * j + 1) * ((2 * j + 1) ^ 2 - 1) :=
    Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right (Nat.pow_le_pow_left (by omega) 2) 1)
  obtain ⟨s, rfl⟩ : ∃ s, S = s + 2 := ⟨S - 2, by omega⟩
  have hs : 2 * (A - 1) < s := by omega
  have hlt : 2 * ((s + 2) * ((A - 1) * (s + 2 - 1))) < (s + 2 - 1) * ((s + 2 - 1) ^ 2 - 1) := by
    rw [show s + 2 - 1 = s + 1 by omega, show (s + 1) ^ 2 - 1 = (s + 2) * s by
      rw [show (s + 1) ^ 2 = (s + 2) * s + 1 by ring, Nat.add_sub_cancel]]
    calc 2 * ((s + 2) * ((A - 1) * (s + 1))) = (s + 1) * (s + 2) * (2 * (A - 1)) := by ring
      _ < (s + 1) * (s + 2) * s := Nat.mul_lt_mul_of_pos_left hs (by positivity)
      _ = (s + 1) * ((s + 2) * s) := by ring
  exact absurd ((hmono.trans (Nat.le_mul_of_pos_right _ hd0)).trans_eq hEq) (not_le.2 hlt)

private theorem card_eq_card_quotient_center {Q : Type} [Group Q] [IsSimpleGroup Q]
    (h : Nat.card (Q ⧸ center Q) ≠ 1) : Nat.card Q = Nat.card (Q ⧸ center Q) := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) with hb | ht
  · exact (CFSG.ComponentClassification.ExcSelector.card_centralQuotient_of_center_eq_bot hb).symm
  · have h1 : (center Q).index = 1 := by rw [ht, Subgroup.index_top]
    exact absurd h1 h

theorem card_quotCenter_eq_ordA {Q : Type} [Group Q] {n : ℕ} (hn : n ≠ 0)
    (e : Q ≃* CFSG.Open.StatedSL 3 (GaloisField 2 n)) :
    Nat.card (Q ⧸ center Q) = CFSG.Open.ordA 2 (2 ^ n) := by
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn
  have hZ : Nat.card (center Q) = Nat.gcd 3 (2 ^ n - 1) := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    by_cases h3 : 3 ∣ 2 ^ n - 1
    · rw [CFSG.Open.StatedCenterThree.card_center_statedSL_three (by rwa [hK]),
        Nat.gcd_eq_left h3]
    · have hd := CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (n := 3)
        (by norm_num) (GaloisField 2 n)
      rw [hK, show Nat.gcd 3 (2 ^ n - 1) = 1 from
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3, Nat.dvd_one] at hd
      rw [show Nat.gcd 3 (2 ^ n - 1) = 1 from
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3, ← hd]
      exact Nat.card_congr (Subgroup.centerCongr
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 _).symm).toEquiv
  have hQ := Subgroup.card_eq_card_quotient_mul_card_subgroup (center Q)
  rw [P22fin3.card_eq_of_equiv_statedSL_three hn e, hZ, pow_mul] at hQ
  rw [CFSG.LocalAnalysis.UniquenessCase.UC6.N588.ordA_two_eq]
  exact (Nat.div_eq_of_eq_mul_left (Nat.gcd_pos_of_pos_left _ (by norm_num)) hQ).symm

theorem not_s21_16 {Q : Type} [Group Q] [Finite Q] {n : ℕ} (hn : 2 < n)
    (hQ : Nat.card (Q ⧸ center Q) = CFSG.Open.ordA 2 (2 ^ n))
    (h : (∃ a : ℕ, Odd a ∧ IsSp4 Q a) ∨ (∃ a : ℕ, IsSU3 Q a) ∨ (∃ a : ℕ, IsL2 Q a) ∨
      (∃ a : ℕ, IsSz Q a) ∨ (∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ IsL2Odd Q r) ∨ IsJ1 Q) : False := by
  have hne1 : Nat.card (Q ⧸ center Q) ≠ 1 := by
    rw [hQ]
    exact ordA_two_ne_one (by omega)
  rcases h with ⟨a, -, ha⟩ | ⟨a, -, hU⟩ | ⟨a, ha⟩ | ⟨a, ha⟩ | ⟨r, hrP, hr2, hr⟩ | hJ
  · have := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) ha
    have hB : Nat.card Q = CFSG.Open.ordBC 2 (2 ^ a) := by
      simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using ha.card_eq_lieOrd (by norm_num)
    rw [← card_eq_card_quotient_center hne1, hB] at hQ
    exact CFSG.Timmesfeld.Orders.ordA_ne_ordBC_two (by norm_num) (by omega) ha.admissible.2.1
      hQ.symm
  · have hB : Nat.card (Q ⧸ center Q) = CFSG.Open.ordTwistedA 2 (2 ^ a) := by
      simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hU.card_eq_lieOrd (by norm_num)
    exact CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA (by norm_num) (by omega) le_rfl
      hU.admissible.2.1 (hQ.symm.trans hB)
  · have := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) ha
    have hB : Nat.card Q = CFSG.Open.ordA 1 (2 ^ a) := by
      simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using ha.card_eq_lieOrd (by norm_num)
    rw [← card_eq_card_quotient_center hne1, hB] at hQ
    exact CFSG.RankThree.PartOne.S12K.ordA_ne_ordA_one (by norm_num) (by omega)
      ha.admissible.2.1 hQ.symm
  · refine CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 ha ?_
    exact (hQ ▸ three_dvd_ordA_two n).trans (Subgroup.card_quotient_dvd_card _)
  · have := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hr
    have hB : Nat.card Q = CFSG.Open.ordA 1 r := by
      simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hr.card_eq_lieOrd (by norm_num)
    rw [← card_eq_card_quotient_center hne1, hB] at hQ
    exact ordA_two_ne_ordA_one_odd hn hrP hr2 hQ.symm
  · obtain ⟨hJc, hJs, -⟩ := kJ1_holds Q hJ
    have := hJs
    rw [← card_eq_card_quotient_center hne1, hJc] at hQ
    obtain ⟨r, hr, hm⟩ := CFSG.Quasithin.H13.VolI.two_part_ordA_two (e := n) (by omega)
    have h3 := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd (r := 21945) (a := 3) (by decide)
      hr (by rw [← hm, ← hQ]; norm_num)
    omega

theorem false_of_card_quotCenter (D : Data G) (Ch : Choice2011 G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h119 : R119W D) (h16 : S21_16 D Ch) (hH : H1930 D) (c : Ctx22 D Ch)
    {Lb : Subgroup (MBar D.M D.U)} (hLb : IsComponentOf Lb ⊤) {n : ℕ} (hn : 2 < n)
    (hcard : Nat.card (↥Lb ⧸ center ↥Lb) = CFSG.Open.ordA 2 (2 ^ n)) : False := by
  obtain ⟨K, hK, hKb⟩ := uc22p22wa_lift D hx h61 h119 c.hU hLb
  subst hKb
  have hne : mbarImage D.M D.U K ≠ ⊥ := by
    have := hLb.2.2.2
    have : Nontrivial ↥(mbarImage D.M D.U K) :=
      (QuotientGroup.mk'_surjective (center ↥(mbarImage D.M D.U K))).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance
  obtain ⟨ψ, hψs, hψk, -⟩ := uc22p22wa_onto D hK hne
  have hqK : CFSG.IsQuasisimple (Bar2 K) :=
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1).2 hK.2.2
  have hc : Nat.card (Bar2 K ⧸ center (Bar2 K)) = CFSG.Open.ordA 2 (2 ^ n) :=
    (Nat.card_congr
      (CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hqK hψs hψk).toEquiv).trans
      hcard
  exact not_s21_16 hn hc (h16 hH c.toCtx21 K hK)

theorem false_of_isL2Ev (D : Data G) (Ch : Choice2011 G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h33 : S22_3_3 D Ch) (h119 : R119W D) (h17 : S21_17 D Ch) (h211 : S21_1 D Ch)
    (h2112 : S21_12 D Ch) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n)
    (hSg : UC6S846.SigmaStd D) (h847 : R847E3L3 D) (h920 : R920odd D) (h923 : F09.R923 D)
    (h8107 : F08.R8107 D) (hnsp : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) {i : Fin m} (hbad : ¬ ∃ n : ℕ, IsL2Ev ↥(Nb i) n ∧ n ≠ 2)
    (hσ : ∀ p ∈ D.sig, p ∣ Nat.card ↥(Nb i)) {Lb : Subgroup (MBar D.M D.U)}
    (hLb : IsComponentOf Lb ⊤) {n : ℕ} (hn : 2 < n) (hL2 : IsL2Ev ↥Lb n) : False := by
  obtain ⟨K, hK, hKb, hKe, hKs, hKn⟩ :=
    uc22p2251b_exists_bad D hx h61 h119 h17 hH c.toCtx22 hNb hbad
  obtain ⟨L, hL, -, ⟨eL⟩⟩ :=
    uc22p2251b_exists_lift D hx h61 h119 c.hU hLb (Or.inl ⟨n, by omega, hL2⟩)
  have hL2' : IsL2Ev (Bar2 L) n := P22fin.isL2Ev_of_mulEquiv hL2 eL.symm
  have hLs : LayerShape22 (Bar2 L) := Or.inl ⟨n, by omega, hL2'⟩
  have hKL : K ≠ L := by
    rintro rfl
    have h1 := P2251b.lt_card_of_isL2Ev hL2' hn
    rcases hKs.card with h | h <;> omega
  obtain ⟨X, hXK, hX, hXU⟩ := uc22p2251p_exists_not_mem D Ch h33 h211 h2112 hn3 hSg h847 h920
    h923 hnsp hH c hNb hbad hσ hK hKb hKe hKs hKn
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3
    (hLs.three_dvd_card.trans (card_quotient_dvd_card _))
  have hYL : zpowers (y : G) ≤ L := zpowers_le.2 y.2
  have hY : Nat.card (zpowers (y : G)) = 3 := by rw [Nat.card_zpowers, orderOf_coe, hy]
  have hr : ∀ {Q E : Subgroup G}, LayerShape22 (Bar2 Q) → E ≤ Q → Nat.card E = 3 →
      CFSG.Open.pRank 3 Q = 1 := fun hQs hEQ hE =>
    le_antisymm (uc22p2251b_thin8 hQs 3 Nat.prime_three (by norm_num))
      (CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hEQ
        (CFSG.GroupTheory.isElemAbelian_of_card_prime hE) (by rw [hE, pow_one]))
  exact hXU (h8107 K hK L hL hKL (hr hKs.layerShape hXK hX) (hr hLs hYL hY)
    (Or.inl (uc22p2251b_thin8 hKs.layerShape)) (Or.inl (uc22p2251b_thin8 hLs)) X _ hXK hX hYL
    hY).1

end P2251t

theorem s22_5_1RStar_of_sn (D : Data G) (Ch : Choice2011 G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h119 : R119W D) (h17 : S21_17 D Ch) (h211 : S21_1 D Ch)
    (h2112 : S21_12 D Ch) (h31 : S22_3_1 D Ch) (h33 : S22_3_3 D Ch)
    (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (hSg : UC6S846.SigmaStd D)
    (h847 : R847E3L3 D) (h920 : R920odd D) (h923 : F09.R923 D) (h8107 : F08.R8107 D)
    (h16 : S21_16 D Ch) (h2014 : S20_14N D) (hR : S22_5_1RStarSn D Ch) : S22_5_1RStar D Ch := by
  intro hH c m Nb hNb i hk he hbad hS3 hσ hrk hcyc
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnsp : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := fun hsp =>
    hk (by unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam; rw [if_pos hsp])
  obtain ⟨K, hK, -⟩ := uc22p2251b_exists_bad D hx h61 h119 h17 hH c.toCtx22 hNb hbad
  obtain ⟨p, hp⟩ := hSg.nonempty
  obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
  have : Fact p.Prime := ⟨hpP⟩
  have hsp := UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hK) hp
  have hp5 : 5 ≤ p := by
    have hp3 : p ≠ 3 := by
      rintro rfl
      exact hnsp hsp
    have hp4 : p ≠ 4 := by
      rintro rfl
      norm_num at hpP
    have h2 := hpP.two_le
    omega
  obtain ⟨C, hC, hCS, hch, hCM⟩ : ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ proofS D ∧
      (C.subgroupOf (proofS D)).Characteristic ∧ ¬ normalizer (C : Set G) ≤ D.M := by
    by_contra hne
    refine (h31 hH c).2 (iSup_le fun C => iSup_le fun hC => iSup_le fun hCS =>
      iSup_le fun hch => ?_)
    by_contra hCM
    exact hne ⟨C, hC, hCS, hch, hCM⟩
  have hSC := CFSG.GroupTheory.normalizer_le_normalizer_of_characteristic hCS hch
  have hHs : normalizer (C : Set G) ∈ hSet D.T D.M :=
    ⟨fun t ht => hSC (P22k2.T_le_normalizer_proofS D ht), hCM, D.standing.charTwo _
      ⟨C, hC, D.sylowM.isPGroup.to_le (hCS.trans inf_le_left), rfl⟩⟩
  obtain ⟨Q, hQM, hQS, hQp, hQU⟩ := P2251r.exists_pSubgroup D Ch h33 hH c hNb hbad hS3 hpP hp5
    (by rw [hrk p hp]; norm_num)
  have hQH : Q ≤ normalizer (C : Set G) ⊓ D.M := le_inf (hQS.trans hSC) hQM
  have hpd : p ∣ Nat.card ↥(normalizer (C : Set G) ⊓ D.M) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hQp
    have hk0 : k ≠ 0 := by
      rintro rfl
      refine hQU ?_
      rw [Subgroup.eq_bot_of_card_eq Q (by rw [hk, pow_zero])]
      exact bot_le
    exact ((dvd_pow_self p hk0).trans hk.symm.dvd).trans (Subgroup.card_dvd_of_le hQH)
  obtain ⟨d, n, hd2, hd4, hn, -, -, -, ⟨e⟩⟩ := h2014 hH p hpP hp2 hsp _ hHs hpd
  set Y := Opp p (normalizer (C : Set G) ⊓ D.M) with hYdef
  have hYM : Y ≤ D.M := (PartTwo.s13_Bar13_opp_le p _).trans inf_le_right
  obtain ⟨eY⟩ := P2251s.bar2_opp_equiv hpP e
  have hqY : CFSG.IsQuasisimple (Bar2 Y) :=
    P2251s.isQuasisimple_of_equiv_statedSL (by omega) (by omega) eY
  have hQY : Q ≤ Y := fun y hy => by
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hQp ⟨y, hy⟩
    exact Subgroup.subset_closure ⟨hQH hy, k, (Subgroup.orderOf_mk y hy).symm.trans hk⟩
  have hYU : ¬ Y ≤ centralizer (D.U : Set G) := fun h => hQU (hQY.trans h)
  have hV : D.M ≤ normalizer (D.U : Set G) := (uc22p22e_inCalV_U D).2.2.1
  have hO : CFSG.pCore 2 (MBar D.M D.U) = ⊥ :=
    (uc22br4_pCore_bot_iff D.M D.U hV).2 (uc22p22o_inCalW_U_of_not_isTI D hx h61 c.hU).2.2
  have hsn := hR hH c m Nb hNb i hk he hbad hS3 hσ hrk hcyc p hp C hC hCS hch hCM
  obtain ⟨hLb, f, hfs, hfk⟩ := P2251s.isComponentOf_mbarImage hV hYM hO hqY hsn hYU
  obtain rfl | rfl : d = 3 ∨ d = 4 := by omega
  ·
    have hL2Y : IsL2Ev (Bar2 Y) n :=
      ⟨GaloisField 2 n, inferInstance, inferInstance, GaloisField.card 2 n (by omega), ⟨eY⟩⟩
    have hsh : LayerShape22 (Bar2 Y) := Or.inl ⟨n, by omega, hL2Y⟩
    have hinj : Function.Injective f :=
      (MonoidHom.ker_eq_bot_iff f).1 (le_bot_iff.1 (hfk.trans hsh.center_eq_bot.le))
    exact P2251t.false_of_isL2Ev D Ch hx h61 h33 h119 h17 h211 h2112 hn3 hSg h847 h920 h923 h8107
      hnsp hH c hNb hbad hσ hLb hn
      (P22fin.isL2Ev_of_mulEquiv hL2Y (MulEquiv.ofBijective f ⟨hinj, hfs⟩))
  ·
    exact P2251t.false_of_card_quotCenter D Ch hx h61 h119 h16 hH c.toCtx22 hLb hn
      ((Nat.card_congr (CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hqY hfs
        hfk).toEquiv).symm.trans (P2251t.card_quotCenter_eq_ordA (by omega) eY))

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
