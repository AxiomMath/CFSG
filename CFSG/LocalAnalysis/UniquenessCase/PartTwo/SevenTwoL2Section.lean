module

public import CFSG.LocalAnalysis.UniquenessCase.UCK35w
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35cRed
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Rank13
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
public import CFSG.GroupTheory.SimpleSectionPPrimeQuotient
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinGrp
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQHallHigman
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.ExcRank
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588D3
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QDiag
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GH74.Orders.LieType
public import CFSG.Quasithin.Background.D36GluedNDEven
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLift
public import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.J4Cards
public import CFSG.RankThree.PartOne.S12K.Rigidity

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Blueprint (LieModel)
open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem not_dvd_card_quotient_pElementSubgroup {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) :
    ¬ p ∣ Nat.card (X ⧸ CFSG.RankThree.PartOne.pElementSubgroup p (⊤ : Subgroup X)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let L : Subgroup X := CFSG.RankThree.PartOne.pElementSubgroup p (⊤ : Subgroup X)
  haveI hLn : L.Normal := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_pElementSubgroup_normal
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective L x
  obtain ⟨e, m, hpm, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' p hp.ne_one
  set n := m ^ Nat.totient (p ^ e) with hn
  have hφpos : 0 < Nat.totient (p ^ e) := Nat.totient_pos.mpr (pow_pos hp.pos e)
  have hmn : m ∣ n := dvd_pow_self m hφpos.ne'
  have hpn : ¬ p ∣ n := fun h => hpm (hp.dvd_of_dvd_pow h)
  have hgn : (QuotientGroup.mk' L g) ^ n = 1 := by
    rw [← map_pow]
    refine (QuotientGroup.eq_one_iff (N := L) (x := g ^ n)).mpr ?_
    refine Subgroup.subset_closure ⟨Subgroup.mem_top _, ?_⟩
    have hpow : (g ^ n) ^ p ^ e = 1 := by
      obtain ⟨j, hj⟩ := hmn
      rw [hj, ← pow_mul, show m * j * p ^ e = (p ^ e * m) * j by ring, ← hm,
        pow_mul, pow_orderOf_eq_one, one_pow]
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hpow)
    exact ⟨k, hk⟩
  have hpdvdn : p ∣ n := by
    rw [← hx]
    exact orderOf_dvd_of_pow_eq_one hgn
  exact hpn hpdvdn

private theorem imageModK_opp_eq_pElementSubgroup {p : ℕ} (hp : p.Prime) (H : Subgroup G) :
    ImageModK p H (Opp p H) =
      CFSG.RankThree.PartOne.pElementSubgroup p (⊤ : Subgroup (QuotK7 p H)) := by
  have htop : (⊤ : Subgroup ↥H).map H.subtype = H := by
    ext x
    exact ⟨fun hx => (Subgroup.mem_map.mp hx).elim fun y hy => hy.2 ▸ y.2,
      fun hx => Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩⟩
  have hmap : CFSG.RankThree.PartOne.pElementSubgroup p H =
      (CFSG.RankThree.PartOne.pElementSubgroup p (⊤ : Subgroup ↥H)).map H.subtype := by
    rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pElementSubgroup_map hp H.subtype ⊤, htop]
  have hsub : (CFSG.RankThree.PartOne.pElementSubgroup p H).subgroupOf H =
      CFSG.RankThree.PartOne.pElementSubgroup p (⊤ : Subgroup ↥H) := by
    rw [hmap, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  unfold ImageModK Opp
  rw [hsub]
  refine (CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pElementSubgroup_map hp
    (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) ⊤).trans ?_
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

private theorem pow_three_dvd_ordTwistedA_two {q : ℕ} (hq1 : 1 ≤ q) :
    q ^ 3 ∣ CFSG.Open.ordTwistedA 2 q := by
  have h1 : q + 1 ∣ q ^ 2 - 1 := by
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    refine ⟨r, ?_⟩
    have : (r + 1) ^ 2 = (r + 1 + 1) * r + 1 := by ring
    omega
  have hg : Nat.gcd 3 (q + 1) ∣ (q ^ 2 - 1) * (q ^ 3 + 1) :=
    (Nat.gcd_dvd_right 3 (q + 1)).trans
      (h1.trans (dvd_mul_right (q ^ 2 - 1) (q ^ 3 + 1)))
  rw [CFSG.Quasithin.H13.ordTwistedA_two_eq q hq1, Nat.mul_div_assoc _ hg]
  exact dvd_mul_right _ _

private theorem pow_three_dvd_card_of_lieModel_PSU {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L : Type} [Group L] (h : LieModel L .PSU 3 p m) : p ^ 3 ∣ Nat.card L := by
  rw [CFSG.GH74.card_of_lieModel_PSU (n := 3) (by norm_num) hp2 h]
  exact (pow_dvd_pow_of_dvd (dvd_pow_self p (by have := h.admissible.2.1; omega)) 3).trans
    (pow_three_dvd_ordTwistedA_two (Nat.one_le_pow _ _ hp.pos))

private theorem false_of_r72_alt_two_mul {p : ℕ} [hp : Fact p.Prime]
    (hp7 : 7 ≤ p)
    {L : Type} [Group L] [Finite L] (hcardL : Nat.card L = Nat.factorial (2 * p) / 2)
    (h : (∃ m, LieModel L .PSL 2 p m) ∨ (∃ m, LieModel L .PSU 3 p m) ∨
      (p = 11 ∧ IsSpor L .J4)) : False := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : 3 ≤ p := by omega
  have h2fac : 2 * (Nat.factorial (2 * p) / 2) = Nat.factorial (2 * p) :=
    Nat.mul_div_cancel' (Nat.dvd_factorial (by norm_num) (by omega))
  have hfact_bound : p ^ 6 < Nat.factorial (2 * p) := by
    have hle := Nat.factorial_mul_pow_sub_le_factorial (n := p) (m := 2 * p) (by omega)
    rw [show 2 * p - p = p by omega] at hle
    have hp6 : p ^ 6 < p ^ p := Nat.pow_lt_pow_right (by omega) (by omega)
    have h1 : p ^ p ≤ Nat.factorial p * p ^ p := by
      calc p ^ p = 1 * p ^ p := (one_mul _).symm
        _ ≤ Nat.factorial p * p ^ p := Nat.mul_le_mul_right _ (Nat.factorial_pos p)
    exact lt_of_lt_of_le (lt_of_lt_of_le hp6 h1) hle
  rcases h with ⟨m, hPSL⟩ | hPSU | ⟨hp11, hJ4⟩
  ·
    have hm1 : 1 ≤ m := hPSL.admissible.2.1
    have hcard : Nat.card L = CFSG.Open.ordA 1 (p ^ m) :=
      CFSG.GH74.card_of_lieModel_PSL (by norm_num) hPSL
    have hodd : Odd (p ^ m) := (hp.out.odd_of_ne_two hp2).pow
    have heq : 2 * CFSG.Open.ordA 1 (p ^ m) = Nat.factorial (2 * p) := by
      rw [← hcard, hcardL, h2fac]
    have hdvd : p ^ m ∣ Nat.factorial (2 * p) := by
      rw [← heq]
      exact ⟨(p ^ m) ^ 2 - 1,
        CFSG.LocalAnalysis.UniquenessCase.UC6.N588.two_mul_ordA_one hodd⟩
    have hmle : m ≤ 2 :=
      CFSG.LocalAnalysis.RankFourTheoremC.PPointP.pow_dvd_two_mul_factorial hp3 hdvd
    interval_cases m
    ·
      rw [pow_one] at heq
      have hlt : 2 * CFSG.Open.ordA 1 p < Nat.factorial (2 * p) := by
        rw [CFSG.LocalAnalysis.UniquenessCase.UC6.N588.two_mul_ordA_one
          (hp.out.odd_of_ne_two hp2)]
        have h1 : p * (p ^ 2 - 1) < p ^ 3 := by
          have h2 : p ^ 2 - 1 < p ^ 2 := Nat.sub_lt (by positivity) (by norm_num)
          calc p * (p ^ 2 - 1) < p * p ^ 2 := Nat.mul_lt_mul_of_pos_left h2 hp.out.pos
            _ = p ^ 3 := by ring
        have h3 : p ^ 3 ≤ Nat.factorial (2 * p) := by
          have hle := Nat.factorial_mul_pow_sub_le_factorial (n := p) (m := 2 * p) (by omega)
          rw [show 2 * p - p = p by omega] at hle
          have h4 : p ^ 3 ≤ p ^ p := Nat.pow_le_pow_right hp.out.pos hp3
          have h5 : p ^ p ≤ Nat.factorial p * p ^ p := by
            calc p ^ p = 1 * p ^ p := (one_mul _).symm
              _ ≤ Nat.factorial p * p ^ p := Nat.mul_le_mul_right _ (Nat.factorial_pos p)
          exact (h4.trans h5).trans hle
        exact lt_of_lt_of_le h1 h3
      omega
    ·
      have hlt : 2 * CFSG.Open.ordA 1 (p ^ 2) < Nat.factorial (2 * p) := by
        rw [CFSG.LocalAnalysis.UniquenessCase.UC6.N588.two_mul_ordA_one
          (hp.out.odd_of_ne_two hp2 |>.pow)]
        have h1 : p ^ 2 * ((p ^ 2) ^ 2 - 1) < p ^ 6 := by
          have h2 : (p ^ 2) ^ 2 - 1 < (p ^ 2) ^ 2 := Nat.sub_lt (by positivity) (by norm_num)
          calc p ^ 2 * ((p ^ 2) ^ 2 - 1) < p ^ 2 * (p ^ 2) ^ 2 :=
                Nat.mul_lt_mul_of_pos_left h2 (by positivity)
            _ = p ^ 6 := by ring
        exact lt_of_lt_of_le h1 hfact_bound.le
      omega
  ·
    obtain ⟨m, hPSU⟩ := hPSU
    have hpdvd : p ^ 3 ∣ Nat.factorial (2 * p) := by
      have h1 : p ^ 3 ∣ Nat.factorial (2 * p) / 2 :=
        hcardL ▸ pow_three_dvd_card_of_lieModel_PSU hp.out hp2 hPSU
      rw [← h2fac]
      simpa [mul_comm] using dvd_mul_of_dvd_right h1 2
    have := CFSG.LocalAnalysis.RankFourTheoremC.PPointP.pow_dvd_two_mul_factorial hp3 hpdvd
    omega
  ·
    subst hp11
    haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    obtain ⟨e⟩ := hJ4
    have hfac : (Nat.card L).factorization 11 = 3 := by
      rw [Nat.card_congr e.toEquiv]
      dsimp only [CFSG.Blueprint.NativeSporadic.Carrier]
      exact CFSG.AGLEmbeddingD2.Wilson.Proving.card_J4_factorization_eleven
    have h11dvd : 11 ^ 3 ∣ Nat.card L := by
      rw [Nat.Prime.pow_dvd_iff_le_factorization (by norm_num : Nat.Prime 11) (by positivity)]
      omega
    have hcardEq : Nat.card L = Nat.factorial (2 * 11) / 2 := by
      simpa using hcardL
    have hpdvd : 11 ^ 3 ∣ Nat.factorial (2 * 11) := by
      have h1 : 11 ^ 3 ∣ Nat.factorial (2 * 11) / 2 := hcardEq ▸ h11dvd
      have h2fac' : 2 * (Nat.factorial (2 * 11) / 2) = Nat.factorial (2 * 11) :=
        Nat.mul_div_cancel' (Nat.dvd_factorial (by norm_num) (by omega))
      rw [← h2fac']
      simpa [mul_comm] using dvd_mul_of_dvd_right h1 2
    have := CFSG.LocalAnalysis.RankFourTheoremC.PPointP.pow_dvd_two_mul_factorial
      (p := 11) (by norm_num) hpdvd
    omega

theorem not_isL2_section_of_sec7Hyp_of_dvd
    {D : Data G} {p n : ℕ} {H : Subgroup G}
    (hK35 : UCK.K35w) (h72 : F07.R72 D) (hH : F07.Sec7Hyp D p H)
    (hn : 3 ≤ n) (hpn : p ∣ 2 ^ (2 * n) - 1)
    (Y : Subgroup (F07.QuotK7 p H))
    (hY : Y ≤ ((H ⊓ D.M).subgroupOf H).map
      (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)))
    (N : Subgroup ↥Y) [N.Normal] :
    ¬ IsL2 (↥Y ⧸ N) n := by
  intro hS
  classical
  have hp : p.Prime := hH.1
  have hp2 : p ≠ 2 := hH.2.1
  have hMsp : IsStronglyPEmbedded p D.M := hH.2.2.1
  have hHtop : H ≠ ⊤ := hH.2.2.2.1
  have hHnotle : ¬ H ≤ D.M := hH.2.2.2.2.1
  have hHrank : 1 < CFSG.Open.pRank p (H ⊓ D.M) := hH.2.2.2.2.2
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvdHM : p ∣ Nat.card (H ⊓ D.M : Subgroup G) := by
    have h2 : p ^ 2 ∣ Nat.card (H ⊓ D.M : Subgroup G) :=
      (pow_dvd_pow p (by omega : 2 ≤ CFSG.Open.pRank p (H ⊓ D.M))).trans
        (CFSG.RankThreeEvenClassification.Helpers.prime_power_pRank_dvd_card p hp (H ⊓ D.M))
    exact (dvd_pow_self p (by norm_num : (2 : ℕ) ≠ 0)).trans h2
  have hMs : IsStronglyPEmbedded p ((H ⊓ D.M).subgroupOf H) :=
    hMsp.subgroupOf hHnotle hdvdHM
  have h2H : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥H) := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup H]
    exact le_trans hHrank (CFSG.SectionRank.pRank_mono hp.one_lt
      (inf_le_left : H ⊓ D.M ≤ H))
  have hKle : CFSG.pPrimeCore p ↥H ≤ (H ⊓ D.M).subgroupOf H :=
    UCK.pPrimeCore_le_of_stronglyPEmbedded hMs h2H
  have hcopK : ¬ p ∣ Nat.card (CFSG.pPrimeCore p ↥H) :=
    (hp.coprime_iff_not_dvd).mp (CFSG.pPrimeCore_coprime_card (G := ↥H) (p := p))
  have hMbar : IsStronglyPEmbedded p (ImageModK p H (H ⊓ D.M)) := by
    rw [ImageModK]
    exact hMs.map_quotient hKle hcopK
  have hMbar' : IsStronglyPEmbedded p
      (((H ⊓ D.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) := hMbar
  have h2Hbar : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (QuotK7 p H)) := by
    rw [CFSG.SectionRank.pRank_quotient_eq (CFSG.pPrimeCore p ↥H) hcopK]
    exact h2H
  have hcore : CFSG.pPrimeCore p (QuotK7 p H) = ⊥ := CFSG.pPrimeCore_quotient_eq_bot hp
  have hKH : CFSG.Open.IsKGroup ↥H := D.standing.kProper.isKGroup H hHtop
  have hKq : CFSG.Open.IsKGroup (QuotK7 p H) := hKH.quotient (CFSG.pPrimeCore p ↥H)
  have hcases := hK35 (QuotK7 p H) hKq p hp hp2 (ImageModK p H (H ⊓ D.M)) hMbar h2Hbar hcore
  haveI hLnorm : (Opp p (⊤ : Subgroup (QuotK7 p H))).Normal := by
    simpa [Opp] using CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_pElementSubgroup_normal
  have hbridge : LKQuot7 p H ≃* ↥(Opp p (⊤ : Subgroup (QuotK7 p H))) :=
    MulEquiv.subgroupCongr (imageModK_opp_eq_pElementSubgroup hp H)
  have hSsimple : IsSimpleGroup (↥Y ⧸ N) :=
    CFSG.ComponentClassification.HarrisLit.isSimpleGroup_of_lieModel_psl2 hS
  have hSnonab : ¬ IsMulCommutative (↥Y ⧸ N) := by
    obtain ⟨a, b, hab⟩ := CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2 hS
    exact fun hc => hab (hc.is_comm.comm a b)
  have hScard : Nat.card (↥Y ⧸ N) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    have hcard := CFSG.GH74.card_of_lieModel_PSL (G := ↥Y ⧸ N) (n := 2) (p := 2) (f := n)
      (by norm_num) hS
    rw [hcard, CFSG.LocalAnalysis.UniquenessCase.UC6.N588.ordA_one_eq]
    have hodd : Odd (2 ^ n - 1) := by
      have h := CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one (f := n) (n := 1)
        (by omega) le_rfl
      rwa [pow_one] at h
    rw [(Nat.coprime_two_left).mpr hodd, Nat.div_one]
  have hSdvd : p ∣ Nat.card (↥Y ⧸ N) := by
    have hdvd : 2 ^ (2 * n) - 1 ∣ Nat.card (↥Y ⧸ N) := by
      rw [hScard]
      have h : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [Nat.mul_comm 2 n, pow_mul]
      rw [h]
      exact dvd_mul_left _ _
    exact hpn.trans hdvd
  have hSL : Nat.card (↥Y ⧸ N) ∣ Nat.card ↥(Opp p (⊤ : Subgroup (QuotK7 p H))) :=
    CFSG.GroupTheory.card_dvd_of_isSimpleGroup_quotient_of_isPPrimeQuotient
      (L := Opp p (⊤ : Subgroup (QuotK7 p H)))
      (by simpa [Opp] using not_dvd_card_quotient_pElementSubgroup (X := QuotK7 p H) hp)
      (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hSsimple hSdvd
  rcases hcases with hMps | hAlt | ⟨hp5, hFi⟩
  ·
    have hSPS : CFSG.HallHigman.IsPSolvable p (↥Y ⧸ N) :=
      CFSG.LocalAnalysis.RankThreeTheoremC.InnerQ.HallHigman.IsPSolvable.quotient'
        (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
          hMps hY) N
    exact (CFSG.LocalAnalysis.RankThreeUC.S15.K421GrpProof.not_isPSolvable_of_simple
      hSsimple hp hSdvd (by
        intro hc
        haveI : IsCyclic (↥Y ⧸ N) := isCyclic_of_prime_card hc
        exact hSnonab IsCyclic.isMulCommutative)) hSPS
  ·
    obtain ⟨eAlt⟩ := hAlt
    have hSdvdAlt : Nat.card (↥Y ⧸ N) ∣ Nat.card (alternatingGroup (Fin (2 * p))) := by
      rw [← Nat.card_congr eAlt.toEquiv]
      exact hSL
    have hp37 : p = 3 ∨ p = 5 ∨ 7 ≤ p := by
      have hp3le : 3 ≤ p := by have := hp.two_le; omega
      rcases Nat.lt_or_ge p 7 with h | h
      · interval_cases p <;> simp_all +decide
      · exact Or.inr (Or.inr h)
    rcases hp37 with rfl | rfl | hp7
    ·
      have hcardA6 : Nat.card (alternatingGroup (Fin (2 * 3))) = 360 := by
        have h := CFSG.Alternating.Multipliers.nat_card_alternatingGroup_fin 4
        rw [h]; norm_num
      have h360 : Nat.card (↥Y ⧸ N) ≤ 360 := by
        rw [hcardA6] at hSdvdAlt
        exact Nat.le_of_dvd (by norm_num) hSdvdAlt
      have h504 : 504 ≤ Nat.card (↥Y ⧸ N) := by
        rw [hScard]
        have h8 : 8 ≤ 2 ^ n := by
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
        have h64 : 64 ≤ (2 ^ n) ^ 2 := by
          calc 64 = 8 ^ 2 := by norm_num
            _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h8 2
        have h63 : 63 ≤ (2 ^ n) ^ 2 - 1 := by omega
        calc 504 = 8 * 63 := by norm_num
          _ ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h8 h63
      omega
    ·
      have hcardA10 : Nat.card (alternatingGroup (Fin (2 * 5))) = 1814400 := by
        have h := CFSG.Alternating.Multipliers.nat_card_alternatingGroup_fin 8
        rw [h]; norm_num
      have hdvdA : Nat.card (↥Y ⧸ N) ∣ 1814400 := by
        rw [← hcardA10]
        exact hSdvdAlt
      have h2dvd : 2 ^ n ∣ Nat.card (↥Y ⧸ N) := by
        rw [hScard]
        exact dvd_mul_right _ _
      have hn7 : n ≤ 7 := by
        by_contra h
        have h8 : 2 ^ 8 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
        have : 2 ^ 8 ∣ 1814400 := h8.trans (h2dvd.trans hdvdA)
        norm_num at this
      have hn46 : n = 4 ∨ n = 6 := by
        interval_cases n
        · norm_num at hpn
        · exact Or.inl rfl
        · norm_num at hpn
        · exact Or.inr rfl
        · norm_num at hpn
      rcases hn46 with rfl | rfl
      ·
        have h17 : 17 ∣ Nat.card (↥Y ⧸ N) := by
          rw [hScard]
          norm_num
        have : 17 ∣ 1814400 := h17.trans hdvdA
        norm_num at this
      ·
        have h13 : 13 ∣ Nat.card (↥Y ⧸ N) := by
          rw [hScard]
          norm_num
        have : 13 ∣ 1814400 := h13.trans hdvdA
        norm_num at this
    ·
      have hcardLK : Nat.card (LKQuot7 p H) = Nat.factorial (2 * p) / 2 := by
        have h1 : Nat.card (LKQuot7 p H) = Nat.card ↥(Opp p (⊤ : Subgroup (QuotK7 p H))) :=
          Nat.card_congr hbridge.toEquiv
        have h2 : Nat.card ↥(Opp p (⊤ : Subgroup (QuotK7 p H))) =
            Nat.card (alternatingGroup (Fin (2 * p))) := Nat.card_congr eAlt.toEquiv
        have h3 : Nat.card (alternatingGroup (Fin (2 * p))) = Nat.factorial (2 * p) / 2 := by
          have h := CFSG.Alternating.Multipliers.nat_card_alternatingGroup_fin (2 * p - 2)
          rwa [Nat.sub_add_cancel (by omega : 2 ≤ 2 * p)] at h
        rw [h1, h2, h3]
      have h72cases := (h72 p H hH).2
      rcases h72cases with ⟨m, hPSL⟩ | hPSU | ⟨hp3, -⟩ | ⟨hp5, -⟩ | ⟨hp11, hJ4'⟩
      · exact false_of_r72_alt_two_mul hp7 hcardLK (Or.inl ⟨m, hPSL⟩)
      · exact false_of_r72_alt_two_mul hp7 hcardLK (Or.inr (Or.inl hPSU))
      · omega
      · omega
      · exact false_of_r72_alt_two_mul hp7 hcardLK (Or.inr (Or.inr ⟨hp11, hJ4'⟩))
  ·
    subst hp5
    obtain ⟨eFi⟩ := hFi
    have hcardFi : Nat.card (LKQuot7 5 H) = 64561751654400 := by
      have h1 : Nat.card (LKQuot7 5 H) = Nat.card ↥(Opp 5 (⊤ : Subgroup (QuotK7 5 H))) :=
        Nat.card_congr hbridge.toEquiv
      have h2 : Nat.card ↥(Opp 5 (⊤ : Subgroup (QuotK7 5 H))) =
          Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Fi22) := Nat.card_congr eFi.toEquiv
      rw [h1, h2]
      dsimp only [CFSG.Blueprint.NativeSporadic.Carrier]
      exact CFSG.Sporadic.Fi22.card_Fi22
    have h72cases := (h72 5 H hH).2
    rcases h72cases with ⟨m, hPSL⟩ | hPSU | ⟨hp3, -⟩ | ⟨hp5', hBranch⟩ | ⟨hp11, -⟩
    ·
      have hcard : Nat.card (LKQuot7 5 H) = CFSG.Open.ordA 1 (5 ^ m) :=
        CFSG.GH74.card_of_lieModel_PSL (by norm_num) hPSL
      have hm1 : 1 ≤ m := hPSL.admissible.2.1
      have h5dvd : 5 ^ m ∣ 64561751654400 := by
        have hodd : Odd (5 ^ m) := (by norm_num : Odd 5).pow
        have hdvd : 5 ^ m ∣ 2 * CFSG.Open.ordA 1 (5 ^ m) := by
          rw [CFSG.LocalAnalysis.UniquenessCase.UC6.N588.two_mul_ordA_one hodd]
          exact dvd_mul_right _ _
        rw [← hcard] at hdvd
        rw [hcardFi] at hdvd
        exact (Nat.Coprime.pow_left m (by norm_num : Nat.Coprime 5 2)).dvd_of_dvd_mul_right hdvd
      have hm2 : m ≤ 2 := by
        by_contra h
        have h3 : 5 ^ 3 ∣ 5 ^ m := pow_dvd_pow 5 (by omega)
        have : 5 ^ 3 ∣ 64561751654400 := h3.trans h5dvd
        norm_num at this
      interval_cases m
      · have h60 : CFSG.Open.ordA 1 5 = 60 := by
          rw [CFSG.LocalAnalysis.UniquenessCase.UC6.N588.ordA_one_eq]; norm_num
        have : Nat.card (LKQuot7 5 H) = 60 := by
          rw [hcard]; simpa using h60
        rw [this] at hcardFi
        norm_num at hcardFi
      · have h7800 : CFSG.Open.ordA 1 25 = 7800 := by
          rw [CFSG.LocalAnalysis.UniquenessCase.UC6.N588.ordA_one_eq]; norm_num
        have : Nat.card (LKQuot7 5 H) = 7800 := by
          rw [hcard]; simpa using h7800
        rw [this] at hcardFi
        norm_num at hcardFi
    ·
      obtain ⟨m, hPSU⟩ := hPSU
      have h125 : 5 ^ 3 ∣ Nat.card (LKQuot7 5 H) :=
        pow_three_dvd_card_of_lieModel_PSU Nat.prime_five (by norm_num) hPSU
      rw [hcardFi] at h125
      norm_num at h125
    · omega
    ·
      rcases hBranch with hSz | hTits | hMcL | hAlt10
      ·
        obtain ⟨S, hSgrp, hSzS, ⟨eAut⟩⟩ := hSz
        letI : Group S := hSgrp
        have hSuz : CFSG.Blueprint.SuzukiModel S 2 5 :=
          (CFSG.Blueprint.LieModel.suzukiModel hSzS).2
        have hSsimple : IsSimpleGroup S :=
          (CFSG.LieType.Simplicity.fam_2b2_simplicity S 2 5 hSuz).2
        obtain ⟨-, a, ha, hf, hcardS⟩ := CFSG.GH74.card_of_suzukiModel hSuz
        have hSnonab : ∃ x y : S, x * y ≠ y * x := by
          by_contra hcon
          push Not at hcon
          haveI : IsMulCommutative S := ⟨⟨hcon⟩⟩
          have hpS := CFSG.OrderReductions.Helpers.prime_card_of_simple_commutative S
          rw [hcardS, CFSG.Open.ordSuzuki] at hpS
          norm_num at hpS
        have hdvdS : Nat.card S ∣ Nat.card (MulAut S) :=
          Subgroup.card_dvd_of_injective (MulAut.conj : S →* MulAut S)
            (CFSG.Quasithin.conj_injective_of_simple hSsimple hSnonab)
        have hcardAut : Nat.card (MulAut S) = Nat.card (LKQuot7 5 H) := by
          rw [Nat.card_congr eAut.symm.toEquiv]
        have h41S : 41 ∣ Nat.card S := by
          rw [hcardS, CFSG.Open.ordSuzuki]
          norm_num
        have h41Fi : 41 ∣ 64561751654400 := by
          have h := h41S.trans hdvdS
          rwa [hcardAut, hcardFi] at h
        norm_num at h41Fi
      ·
        obtain ⟨-, hTits'⟩ := CFSG.Blueprint.LieModel.reeTitsModel hTits (by decide)
        have hcard : Nat.card (LKQuot7 5 H) = CFSG.Open.ordTits :=
          CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_Tits hTits'
        rw [hcard] at hcardFi
        norm_num [CFSG.Open.ordTits] at hcardFi
      ·
        obtain ⟨eMcL⟩ := hMcL
        have hcard : Nat.card (LKQuot7 5 H) = 898128000 := by
          rw [Nat.card_congr eMcL.toEquiv]
          dsimp only [CFSG.Blueprint.NativeSporadic.Carrier]
          exact CFSG.Sporadic.McL.card_McL
        rw [hcard] at hcardFi
        norm_num at hcardFi
      ·
        obtain ⟨eAlt10⟩ := hAlt10
        have hcard : Nat.card (LKQuot7 5 H) = 1814400 := by
          have h := CFSG.Alternating.Multipliers.nat_card_alternatingGroup_fin 8
          rw [Nat.card_congr eAlt10.toEquiv, h]
          norm_num
        rw [hcard] at hcardFi
        norm_num at hcardFi
    · omega

theorem not_isL2_section_of_sec7Hyp
    {D : Data G} {p n : ℕ} {H : Subgroup G}
    (hK35 : UCK.K35w) (h72 : F07.R72 D) (hH : F07.Sec7Hyp D p H)
    (hn : 3 ≤ n) (hpn : p ∣ 2 ^ n + 1)
    (Y : Subgroup (F07.QuotK7 p H))
    (hY : Y ≤ ((H ⊓ D.M).subgroupOf H).map
      (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)))
    (N : Subgroup ↥Y) [N.Normal] :
    ¬ IsL2 (↥Y ⧸ N) n :=
  not_isL2_section_of_sec7Hyp_of_dvd hK35 h72 hH hn (by
    rw [CFSG.Timmesfeld.IsPrimitivePrimeDivisor.two_pow_two_mul_sub_one]
    exact dvd_mul_of_dvd_right hpn _) Y hY N

theorem le_M_of_no_isL2_section
    {D : Data G} {p n : ℕ} {H : Subgroup G}
    (hK35 : UCK.K35w) (h72 : F07.R72 D)
    (hp : p.Prime) (hp2 : p ≠ 2) (hMsp : IsStronglyPEmbedded p D.M)
    (hHtop : H ≠ ⊤) (hrank : 1 < CFSG.Open.pRank p (H ⊓ D.M))
    (hn : 3 ≤ n) (hpn : p ∣ 2 ^ n + 1)
    (Y : Subgroup (QuotK7 p H)) (N : Subgroup ↥Y) [N.Normal]
    (hY : Y ≤ ImageModK p H (H ⊓ D.M)) (hS : IsL2 (↥Y ⧸ N) n) :
    H ≤ D.M := by
  by_contra hHle
  exact (not_isL2_section_of_sec7Hyp hK35 h72 ⟨hp, hp2, hMsp, hHtop, hHle, hrank⟩ hn hpn
    Y hY N) hS

theorem le_M_of_no_isL2_section_of_dvd
    {D : Data G} {p n : ℕ} {H : Subgroup G}
    (hK35 : UCK.K35w) (h72 : F07.R72 D)
    (hp : p.Prime) (hp2 : p ≠ 2) (hMsp : IsStronglyPEmbedded p D.M)
    (hHtop : H ≠ ⊤) (hrank : 1 < CFSG.Open.pRank p (H ⊓ D.M))
    (hn : 3 ≤ n) (hpn : p ∣ 2 ^ (2 * n) - 1)
    (Y : Subgroup (QuotK7 p H)) (N : Subgroup ↥Y) [N.Normal]
    (hY : Y ≤ ImageModK p H (H ⊓ D.M)) (hS : IsL2 (↥Y ⧸ N) n) :
    H ≤ D.M := by
  by_contra hHle
  exact (not_isL2_section_of_sec7Hyp_of_dvd hK35 h72
    ⟨hp, hp2, hMsp, hHtop, hHle, hrank⟩ hn hpn Y hY N) hS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
