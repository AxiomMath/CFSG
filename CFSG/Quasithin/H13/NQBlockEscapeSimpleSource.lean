module

public import CFSG.Quasithin.H13.NQBlockEscapeThreeDivisible
public import CFSG.Quasithin.H13.NQBlockLayerProduct
public import CFSG.Quasithin.H13.NQBlockSourceYReduction
public import CFSG.Quasithin.H13.NQCoreT2Holds
public import CFSG.Quasithin.H13.A7Nat1236Theta
public import CFSG.Quasithin.Background.F918G2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyResidual

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open

theorem complementaryEscapeSimpleSourceY_of (h1323 : Stmt13_1_2_three)
    : ComplementaryEscapeSimpleSourceY := by
  intro G _ _ T L M h H hH hKTH hHM A hA hKA hAu hY
  classical
  have := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKH : nqOriginalK T L ≤ H := le_sup_left.trans hKTH
  obtain ⟨-, hiff, hB3, -⟩ :=
    complementaryEscapeThreeDivisible_of h1323 G T L M h H hH hKTH hHM A hA hKA hAu
  obtain ⟨B, hB, hBA, hBM, -⟩ := hiff.mp hY
  obtain ⟨-, -, hBn, hTB, -, -, ⟨B', ⟨hB'm, hB'f⟩, hBB'⟩, hall, -⟩ := hB3 B hB hBA hBM
  have hBH : B ≤ H := le_of_mem_cComp hB
  obtain ⟨-, hTB', hB'M⟩ := hall B' hB'm hBB'
  have hq : CFSG.IsQuasisimple (↥B' ⧸ CFSG.pCore 2 ↥B') := by
    by_contra hq
    exact hB'M (NQCore.every_sylow_normalized_maximal_nonquasisimple_local_is_confined_holds h
      hB'm hB'f hTB' hq).1
  have h5 := h1323 G T B' h.simple h.nonabelian h.qtke h.sylow h.not_excluded hB'm hB'f hq
  have hBB : B = B' := NQCore.stmtFiveModelLocalChainRigid_holds G T B' B h.sylow
    (perfect_of_mem_cComp (CFSG.Quasithin.cComp_of_isLocal hB'm.1)) hTB' hBB'
    (ne_bot_of_mem_cComp hB) (perfect_of_mem_cComp hB) hTB h5
  rw [← hBB] at h5
  have hr : CFSG.pRank 3 (↥B ⧸ CFSG.pCore 2 ↥B) ≤ 1 := by
    obtain ⟨R, hR⟩ := exists_originalCentralizer (h.t_le.trans h.eq_normalizer.le)
    have hloc : QuasithinUnique.LocalSQTK G :=
      (QuasithinUnique.qtkeCore_of_cat h.nonabelian h.qtke).1
    have hO2 := CFSG.Quasithin.pCoreOf_ne_bot_of_isTwoLocal hH.1
    have hAB := (QuasithinUnique.Vol2Native.lemma_1_2_1_two hloc
      QuasithinUnique.Vol2Native.a37ForSQTKCat_proved hO2 hA hB (Ne.symm hBA)).1
    have hKB : ⁅nqOriginalK T L, B⁆ ≤ pCoreOf 2 B :=
      (commutator_mono hKA le_rfl).trans (hAB.trans inf_le_right)
    obtain ⟨-, -, -, hover⟩ :=
      normal_original_K_overgroup_factors_have_core_containment_and_commutator_transport h hR
    obtain ⟨-, -, hcomm⟩ := hover H B hKTH hBH hBn
    obtain ⟨-, hBK, hKBc, -⟩ := hcomm hKB
    have hHB : H ≤ normalizer (B : Set G) := (normal_subgroupOf_iff_le_normalizer hBH).mp hBn
    obtain ⟨-, -, -, hKs, hKnab, s, hs, hs5, -, hKcard⟩ := original_K_quotient_facts h
    have hsum := commuting_product_pRank (hKH.trans hHB) hBK hKBc hKs hKnab Nat.prime_three
      (by norm_num)
    have hH3 : CFSG.pRank 3 ↥H ≤ 2 := by
      rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_three H]
      exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
        (by norm_num) H hH.1).trans h.qtke.2.2
    have hKBH : CFSG.pRank 3 ↥(nqOriginalK T L ⊔ B) ≤ CFSG.pRank 3 ↥H := by
      rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_three,
        CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_three]
      exact CFSG.SectionRank.pRank_mono (by norm_num) (sup_le hKH hBH)
    have hK1 : 1 ≤ CFSG.pRank 3 (↥(nqOriginalK T L) ⧸ CFSG.pCore 2 ↥(nqOriginalK T L)) := by
      have h3K : 3 ∣ Nat.card (↥(nqOriginalK T L) ⧸ CFSG.pCore 2 ↥(nqOriginalK T L)) := by
        rw [hKcard]
        exact three_dvd_half_order hs hs5
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3K
      have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
      exact CFSG.Quasithin.SteinbergBS.le_pRank_of_card (by norm_num)
        (CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hx3) (by rw [Nat.card_zpowers, hx, pow_one])
    have hcop : ¬ 3 ∣ Nat.card ↥(CFSG.pCore 2 ↥B) := by
      intro hdvd
      obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥B)).exists_card_eq
      rw [ha] at hdvd
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow hdvd)
      omega
    rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_three
      (CFSG.pCore 2 ↥B) hcop]
    omega
  refine ⟨B, hB, hBA, hBM, hBH, hBn, ?_⟩
  rcases h5 with h5 | h5 | h6 | ⟨hp, hZ, ⟨e⟩⟩ | h5
  · exact Or.inl h5
  · exact Or.inr h5
  · obtain ⟨e⟩ := h6
    have h2 := CFSG.QuasithinUnique.Setup.Family.two_le_pRank_three_of_alternating_six e
    omega
  · have : Group.IsPerfect (↥B ⧸ CFSG.pCore 2 ↥B) := hp
    have h2 := (A7.A6quot_facts (by rw [hZ]; exact ⟨1, rfl⟩) e).2
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
    omega
  · have hpsu : CFSG.Quasithin.IsPSU 3 3 1 (↥B ⧸ CFSG.pCore 2 ↥B) :=
      CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h5
    have h2 := CFSG.Quasithin.pRank_three_psu33 hpsu
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
    omega

theorem originalKEscapingSourceY_of_five (h1323 : Stmt13_1_2_three)
    : OriginalKEscapingSourceY :=
  originalKEscapingSourceY_of_complementary h1323 (complementaryEscapeSimpleSourceY_of h1323)

end CFSG.Quasithin.H13.NQBlock
