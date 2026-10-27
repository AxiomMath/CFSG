module

public import CFSG.LocalAnalysis.UniquenessCase.UCK35w
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35cRed
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Rank13
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
public import CFSG.GroupTheory.SimpleSectionPPrimeQuotient
public import CFSG.GroupTheory.QuotientImageSection
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinGrp
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQHallHigman
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588D3
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QDiag
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GH74.Orders.LieType
public import CFSG.Quasithin.Background.D36GluedNDEven
public import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
public import CFSG.RankThree.PartOne.S12K.Rigidity

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Blueprint (LieModel)
open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem not_dvd_card_quotient_pElementSubgroup_simple {X : Type} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) :
    ¬ p ∣ Nat.card (X ⧸ CFSG.RankThree.PartOne.pElementSubgroup p (⊤ : Subgroup X)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let L : Subgroup X := CFSG.RankThree.PartOne.pElementSubgroup p (⊤ : Subgroup X)
  have hLn : L.Normal := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_pElementSubgroup_normal
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

private theorem imageModK_opp_eq_pElementSubgroup_simple {p : ℕ} (hp : p.Prime)
    (H : Subgroup G) :
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

theorem ordTwistedA_two_pow_three_dvd {q : ℕ} (hq1 : 1 ≤ q) :
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

theorem pow_three_dvd_card_of_PSU_model {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L : Type} [Group L] (h : LieModel L .PSU 3 p m) : p ^ 3 ∣ Nat.card L := by
  rw [CFSG.GH74.card_of_lieModel_PSU (n := 3) (by norm_num) hp2 h]
  exact (pow_dvd_pow_of_dvd (dvd_pow_self p (by have := h.admissible.2.1; omega)) 3).trans
    (ordTwistedA_two_pow_three_dvd (Nat.one_le_pow _ _ hp.pos))

theorem not_isSimple_section_of_sec7Hyp
    {D : Data G} {p : ℕ} {H : Subgroup G}
    (hK35 : UCK.K35w) (h72 : F07.R72 D) (hH : F07.Sec7Hyp D p H)
    (Y : Subgroup (F07.QuotK7 p H))
    (hY : Y ≤ ImageModK p H (H ⊓ D.M))
    (N : Subgroup ↥Y) [N.Normal]
    (hSsimple : IsSimpleGroup (↥Y ⧸ N))
    (hSnonab : ¬ IsMulCommutative (↥Y ⧸ N))
    (hpS : p ∣ Nat.card (↥Y ⧸ N))
    (hSnotAlt : ¬ Nat.card (↥Y ⧸ N) ∣ Nat.card (alternatingGroup (Fin (2 * p)))) :
    False := by
  classical
  have hp : p.Prime := hH.1
  have hp2 : p ≠ 2 := hH.2.1
  have hMsp : IsStronglyPEmbedded p D.M := hH.2.2.1
  have hHtop : H ≠ ⊤ := hH.2.2.2.1
  have hHnotle : ¬ H ≤ D.M := hH.2.2.2.2.1
  have hHrank : 1 < CFSG.Open.pRank p (H ⊓ D.M) := hH.2.2.2.2.2
  have : Fact p.Prime := ⟨hp⟩
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
  have hLnorm : (Opp p (⊤ : Subgroup (QuotK7 p H))).Normal := by
    simpa [Opp] using CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_pElementSubgroup_normal
  have hbridge : LKQuot7 p H ≃* ↥(Opp p (⊤ : Subgroup (QuotK7 p H))) :=
    MulEquiv.subgroupCongr (imageModK_opp_eq_pElementSubgroup_simple hp H)
  have hSL : Nat.card (↥Y ⧸ N) ∣ Nat.card ↥(Opp p (⊤ : Subgroup (QuotK7 p H))) :=
    CFSG.GroupTheory.card_dvd_of_isSimpleGroup_quotient_of_isPPrimeQuotient
      (L := Opp p (⊤ : Subgroup (QuotK7 p H)))
      (by simpa [Opp] using
        not_dvd_card_quotient_pElementSubgroup_simple (X := QuotK7 p H) hp)
      (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hSsimple hpS
  rcases hcases with hMps | hAlt | ⟨hp5, hFi⟩
  ·
    have hSPS : CFSG.HallHigman.IsPSolvable p (↥Y ⧸ N) :=
      CFSG.LocalAnalysis.RankThreeTheoremC.InnerQ.HallHigman.IsPSolvable.quotient'
        (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
          hMps hY) N
    exact (CFSG.LocalAnalysis.RankThreeUC.S15.K421GrpProof.not_isPSolvable_of_simple
      hSsimple hp hpS (by
        intro hc
        have : IsCyclic (↥Y ⧸ N) := isCyclic_of_prime_card hc
        exact hSnonab IsCyclic.isMulCommutative)) hSPS
  ·
    obtain ⟨eAlt⟩ := hAlt
    exact hSnotAlt (by
      rw [← Nat.card_congr eAlt.toEquiv]
      exact hSL)
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
        pow_three_dvd_card_of_PSU_model Nat.prime_five (by norm_num) hPSU
      rw [hcardFi] at h125
      norm_num at h125
    · omega
    ·
      rcases hBranch with hSz | hTits | hMcL | hAlt10
      ·
        obtain ⟨S, hSgrp, hSzS, ⟨eAut⟩⟩ := hSz
        let : Group S := hSgrp
        have hSuz : CFSG.Blueprint.SuzukiModel S 2 5 :=
          (CFSG.Blueprint.LieModel.suzukiModel hSzS).2
        have hSsimple : IsSimpleGroup S :=
          (CFSG.LieType.Simplicity.fam_2b2_simplicity S 2 5 hSuz).2
        obtain ⟨-, a, ha, hf, hcardS⟩ := CFSG.GH74.card_of_suzukiModel hSuz
        have hSnonab : ∃ x y : S, x * y ≠ y * x := by
          by_contra hcon
          push Not at hcon
          have : IsMulCommutative S := ⟨⟨hcon⟩⟩
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

theorem exists_normal_quotientEquiv_imageModK
    {D : Data G} {p : ℕ} {H A : Subgroup G} {S : Type} [Group S] [Finite S]
    (hp : p.Prime) (hA : A ≤ H ⊓ D.M) (ψ : ↥A →* S) (hψ : Function.Surjective ψ)
    (hS : IsSimpleGroup S) (hpS : p ∣ Nat.card S) :
    ∃ (Y : Subgroup (F07.QuotK7 p H)) (N : Subgroup ↥Y) (hN : N.Normal),
      letI := hN
      Y ≤ F07.ImageModK p H (H ⊓ D.M) ∧ Nonempty ((↥Y ⧸ N) ≃* S) := by
  have hAH : A ≤ H := hA.trans inf_le_left
  have : Fact p.Prime := ⟨hp⟩
  let K : Subgroup ↥H := CFSG.pPrimeCore p ↥H
  have hKnorm : K.Normal := CFSG.pPrimeCore_normal
  have hKp : ¬ p ∣ Nat.card ↥K :=
    hp.coprime_iff_not_dvd.mp (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥H))
  let eA : ↥(A.subgroupOf H) ≃* ↥A := Subgroup.subgroupOfEquivOfLe hAH
  let N : Subgroup ↥(A.subgroupOf H) := ψ.ker.comap eA.toMonoidHom
  have hNnorm : N.Normal := (MonoidHom.normal_ker ψ).comap eA.toMonoidHom
  let KA : Subgroup ↥A := K.comap (Subgroup.inclusion hAH)
  have hKAnorm : KA.Normal := hKnorm.comap (Subgroup.inclusion hAH)
  have hKAdvd : Nat.card ↥KA ∣ Nat.card ↥K := by
    have hcard : Nat.card ↥(KA.map (Subgroup.inclusion hAH)) = Nat.card ↥KA :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective hAH)
    rw [← hcard]
    exact Subgroup.card_dvd_of_le fun x hx => by
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_comap.mp ha
  have hKAp : ¬ p ∣ Nat.card ↥KA := fun hd => hKp (hd.trans hKAdvd)
  have hKAker : KA ≤ ψ.ker := by
    have : (KA.map ψ).Normal := hKAnorm.map ψ hψ
    have hpdvd : ¬ p ∣ Nat.card ↥(KA.map ψ) :=
      fun hd => hKAp (hd.trans (Subgroup.card_map_dvd KA ψ))
    rcases hS.eq_bot_or_eq_top_of_normal (KA.map ψ) with hbot | htop
    · intro a ha
      have h1 : ψ a ∈ KA.map ψ := Subgroup.mem_map_of_mem ψ ha
      rw [hbot, Subgroup.mem_bot] at h1
      exact MonoidHom.mem_ker.mpr h1
    · exfalso
      have hdvd : p ∣ Nat.card ↥(KA.map ψ) := by
        rw [htop]
        simpa using hpS
      exact hpdvd hdvd
  have hNK : ∀ a : ↥(A.subgroupOf H), (a : ↥H) ∈ K → a ∈ N := by
    intro a ha
    have hmem : eA a ∈ KA := by
      rw [Subgroup.mem_comap]
      show Subgroup.inclusion hAH (eA a) ∈ K
      have hincl : Subgroup.inclusion hAH (eA a) = a := by
        apply Subtype.ext
        exact Subgroup.subgroupOfEquivOfLe_apply_coe hAH a
      rw [hincl]
      exact ha
    exact hKAker hmem
  obtain ⟨N', hN'norm, ⟨eQ⟩⟩ :=
    CFSG.GroupTheory.exists_normal_quotientEquiv_map K (A.subgroupOf H) N hNK
  let Y : Subgroup (F07.QuotK7 p H) := (A.subgroupOf H).map (QuotientGroup.mk' K)
  have eN : (↥(A.subgroupOf H) ⧸ N) ≃* (↥A ⧸ ψ.ker) :=
    QuotientGroup.congr N ψ.ker eA (Subgroup.map_comap_eq_self_of_surjective eA.surjective ψ.ker)
  have eS : (↥A ⧸ ψ.ker) ≃* S := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  have eY : (↥Y ⧸ N') ≃* S := eQ.trans (eN.trans eS)
  have hYle : Y ≤ F07.ImageModK p H (H ⊓ D.M) := by
    rw [F07.ImageModK]
    exact Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hA (Subgroup.mem_subgroupOf.mp hx))
  exact ⟨Y, N', hN'norm, hYle, ⟨eY⟩⟩

theorem le_M_of_simple_section
    {D : Data G} {p : ℕ} {H : Subgroup G}
    (hK35 : UCK.K35w) (h72 : F07.R72 D)
    (hp : p.Prime) (hp2 : p ≠ 2) (hMsp : IsStronglyPEmbedded p D.M)
    (hHtop : H ≠ ⊤) (hrank : 1 < CFSG.Open.pRank p (H ⊓ D.M))
    (Y : Subgroup (F07.QuotK7 p H)) (N : Subgroup ↥Y) [N.Normal]
    (hY : Y ≤ ImageModK p H (H ⊓ D.M))
    (hSsimple : IsSimpleGroup (↥Y ⧸ N))
    (hSnonab : ¬ IsMulCommutative (↥Y ⧸ N))
    (hpS : p ∣ Nat.card (↥Y ⧸ N))
    (hSnotAlt : ¬ Nat.card (↥Y ⧸ N) ∣ Nat.card (alternatingGroup (Fin (2 * p)))) :
    H ≤ D.M := by
  by_contra hHle
  exact not_isSimple_section_of_sec7Hyp hK35 h72
    ⟨hp, hp2, hMsp, hHtop, hHle, hrank⟩ Y hY N hSsimple hSnonab hpS hSnotAlt

theorem le_M_of_surjective_simple
    {D : Data G} {p : ℕ} {H A : Subgroup G} {S : Type}
    [Group S] [Finite S]
    (hK35 : UCK.K35w) (h72 : F07.R72 D) (hp : p.Prime) (hp2 : p ≠ 2)
    (hMsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M) (hHtop : H ≠ ⊤)
    (hrank : 1 < CFSG.Open.pRank p (H ⊓ D.M)) (hA : A ≤ H ⊓ D.M) (ψ : ↥A →* S)
    (hψ : Function.Surjective ψ) (hS : IsSimpleGroup S) (hSnonab : ¬ IsMulCommutative S)
    (hpS : p ∣ Nat.card S)
    (hSnotAlt : ¬ Nat.card S ∣ Nat.card (alternatingGroup (Fin (2 * p)))) :
    H ≤ D.M := by
  obtain ⟨Y, N, hN, hYle, ⟨eY⟩⟩ :=
    exists_normal_quotientEquiv_imageModK hp hA ψ hψ hS hpS
  have : IsSimpleGroup (↥Y ⧸ N) := eY.isSimpleGroup
  have hSnonab' : ¬ IsMulCommutative (↥Y ⧸ N) := by
    intro hc
    apply hSnonab
    rw [isMulCommutative_iff] at hc ⊢
    intro a b
    obtain ⟨a', rfl⟩ := eY.surjective a
    obtain ⟨b', rfl⟩ := eY.surjective b
    calc eY a' * eY b' = eY (a' * b') := (map_mul eY a' b').symm
      _ = eY (b' * a') := by rw [hc a' b']
      _ = eY b' * eY a' := map_mul eY b' a'
  have hpS' : p ∣ Nat.card (↥Y ⧸ N) := by
    rw [Nat.card_congr eY.toEquiv]
    exact hpS
  have hSnotAlt' : ¬ Nat.card (↥Y ⧸ N) ∣
      Nat.card (alternatingGroup (Fin (2 * p))) := by
    rw [Nat.card_congr eY.toEquiv]
    exact hSnotAlt
  exact le_M_of_simple_section hK35 h72 hp hp2 hMsp hHtop hrank Y N hYle
    inferInstance hSnonab' hpS' hSnotAlt'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
