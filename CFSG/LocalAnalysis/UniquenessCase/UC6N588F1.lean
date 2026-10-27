module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588E6
public import CFSG.LocalAnalysis.UniquenessCase.UC6Star36a
public import CFSG.LocalAnalysis.UniquenessCase.UC6C632c
public import CFSG.RankThree.PartOne.CTP.StrongPQuotient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor IsAlt)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

theorem exists_elemAbelian_le_of_twoLocalPrimeRank {G : Type} [Group G] [Finite G]
    (H : Subgroup G) {q : ℕ} (hq : q.Prime) (h3 : 3 < twoLocalPrimeRank q ↥H) :
    ∃ F : Subgroup G, F ≤ H ∧ IsElemAbelian q F ∧ q ^ 4 ≤ Nat.card F := by
  have hne : {k | ∃ N : Subgroup ↥H, IsTwoLocal N ∧ Open.pRank q N = k}.Nonempty := by
    by_contra hempty
    have hset : {k | ∃ N : Subgroup ↥H, IsTwoLocal N ∧ Open.pRank q N = k} = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hempty
    have h0 : twoLocalPrimeRank q ↥H = 0 := by
      unfold twoLocalPrimeRank
      rw [hset]
      exact csSup_empty
    omega
  obtain ⟨N, -, hNk⟩ :=
    Nat.sSup_mem hne (CFSG.PreuniquenessRankFour.Helpers.twoLocalRank_bddAbove q hq)
  have hNk' : Open.pRank q N = twoLocalPrimeRank q ↥H := hNk
  have h1 : Open.pRank q N ≤ Open.pRank q (N.map H.subtype) :=
    CFSG.SectionRank.pRank_le_map hq.one_lt H.subtype H.subtype_injective _
  obtain ⟨F, hFN, hFel, hFcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained q hq (N.map H.subtype)
  refine ⟨F, hFN.trans (map_subtype_le _), hFel, ?_⟩
  rw [hFcard]
  exact Nat.pow_le_pow_right hq.pos (by omega)

theorem le_of_isStronglyPEmbedded_of_coprime {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {M' F V : Subgroup G} (hM' : IsStronglyPEmbedded p M') (hFM : F ≤ M')
    (hFel : IsElemAbelian p F) (hF : p ^ 2 ≤ Nat.card F) (hFV : F ≤ normalizer (V : Set G))
    (hVp : ¬ p ∣ Nat.card V) : V ≤ M' := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hpp : p < p ^ 2 := by nlinarith
  haveI : IsMulCommutative ↥F := hFel.1
  haveI : CFSG.IsElementaryAbelian p ↥F :=
    ⟨Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hFel.2 x x.2)⟩
  haveI : Nontrivial ↥F := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro h
    rw [h, Subgroup.card_bot] at hF
    omega
  refine (CFSG.RankThree.PartOne.KE8F.le_iSup_hyperplane_centralizers hFV hVp).trans
    (iSup₂_le fun B hB => inf_le_right.trans ?_)
  have hBc : Nat.card B * p = Nat.card F := by
    have h := B.card_mul_index
    rwa [hB] at h
  have hBne : B.map F.subtype ≠ ⊥ := by
    intro h
    have h1 : Nat.card (B.map F.subtype) = Nat.card B :=
      Subgroup.card_map_of_injective F.subtype_injective
    rw [h, Subgroup.card_bot] at h1
    rw [← h1, one_mul] at hBc
    omega
  have hBp : IsPGroup p (B.map F.subtype) := hFel.isPGroup.to_le (map_subtype_le _)
  exact (Subgroup.centralizer_le_normalizer _).trans
    (hM'.normalizer_le hBne hBp ((map_subtype_le _).trans hFM))

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

open N588

theorem not_dvd_card_rCoreL_of_mem_sigma (hLM : ¬ m.L ≤ m.M) {q : ℕ}
    (hq : q ∈ uniqueFourSigma m.M) : ¬ q ∣ Nat.card (rCore m.r m.L) := by
  haveI : Fact q.Prime := ⟨hq.1.1⟩
  have hOM : rCore m.r m.L ≤ m.M := m.rCoreL_le_M
  intro hd
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow q ↥(rCore m.r m.L)))
  have hQsyl : IsSylowOf q ((P : Subgroup ↥(rCore m.r m.L)).map (rCore m.r m.L).subtype)
      (rCore m.r m.L) := ⟨P, rfl⟩
  have hPne : (P : Subgroup ↥(rCore m.r m.L)) ≠ ⊥ := P.ne_bot_of_dvd_card hd
  have hQne : (P : Subgroup ↥(rCore m.r m.L)).map (rCore m.r m.L).subtype ≠ ⊥ := fun h =>
    hPne ((Subgroup.map_eq_bot_iff_of_injective _ (rCore m.r m.L).subtype_injective).1 h)
  have hQp : IsPGroup q ((P : Subgroup ↥(rCore m.r m.L)).map (rCore m.r m.L).subtype) :=
    P.isPGroup'.map _
  have hNQ := (m.isStronglyPEmbedded_M hq).normalizer_le hQne hQp
    ((map_subtype_le _).trans hOM)
  have hfr := frattini_of_isSylowOf (rCore_le m.r m.L) m.L_le_normalizer_rCoreL hQsyl
  apply hLM
  rw [hfr]
  exact sup_le hOM (inf_le_right.trans hNQ)

end Mz614

theorem Mz614.not_alt_fi22_of_inputs {G : Type} [Group G] [Finite G] (m : Mz614 G)
    (hKM : UCK.KMult) (hK3 : UCK.KMult3) (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S))
    (hSch : UCK.KSch) (hX : UCK.K620Exc) :
    ¬ ((∃ n : ℕ, 13 ≤ n ∧ IsAlt m.Lbar n) ∨ IsSpor m.Lbar .Fi22) := by
  intro hL
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h619 := m.c619_of_inputs hKM hK3 h69 hSch
  have hLM := m.not_L_le_M_of_inputs hKM hK3 h69 hSch
  have h3 : 3 < twoLocalPrimeRank 3 ↥m.L :=
    hX.1 ↥m.L m.isKGroup_L (CFSG.pPrimeCore m.r ↥m.L) m.odd_card_pPrimeCore_L
      (fun q hq hq2 => m.pRank_pPrimeCore_L_le_three h619 hq hq2) hL
  have hσ : 3 ∈ uniqueFourSigma m.M := by
    have hp : m.S.p = 3 :=
      m.hMS.1 (mem_beta_of_twoLocalPrimeRank m.L Nat.prime_three (by norm_num) h3)
    have h := m.S.hp
    rwa [hp] at h
  have hMs : IsStronglyPEmbedded 3 m.M := m.isStronglyPEmbedded_M hσ
  have h3Y : ¬ 3 ∣ Nat.card (N588.rCore m.r m.L) := m.not_dvd_card_rCoreL_of_mem_sigma hLM hσ
  obtain ⟨F, hFL, hFel, hF⟩ := exists_elemAbelian_le_of_twoLocalPrimeRank m.L Nat.prime_three h3
  have hFne : F ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hF
    norm_num at hF
  obtain ⟨Q, hQ, hFQ⟩ := exists_isSylowOf_ge hFL hFel.isPGroup
  have hQne : Q ≠ ⊥ := fun h => hFne (eq_bot_iff.2 (h ▸ hFQ))
  obtain ⟨P, hP, hQP⟩ := exists_isSylowOf_ge (le_top : Q ≤ ⊤) hQ.isPGroup
  obtain ⟨g, hPg⟩ := hMs.exists_conj_ge (isSylowOf_iff.1 hP)
  set M' := CFSG.RankThree.PartOne.StrongP.conjSub g m.M with hM'
  have hM's : IsStronglyPEmbedded 3 M' := hMs.conj g
  have hQM : Q ≤ M' := hQP.trans hPg
  have hYM : N588.rCore m.r m.L ≤ M' :=
    le_of_isStronglyPEmbedded_of_coprime hM's (hFQ.trans hQM) hFel
      ((by norm_num : 3 ^ 2 ≤ 3 ^ 4).trans hF) (hFL.trans m.L_le_normalizer_rCoreL) h3Y
  have hLM' : m.L ≤ M' := by
    by_contra hLM'
    have hdvd : 3 ∣ Nat.card ↥(M' ⊓ m.L) := by
      have hQ3 : 3 ∣ Nat.card Q := by
        rcases hQ.isPGroup.card_eq_or_dvd with h | h
        · exact absurd (Subgroup.card_eq_one.mp h) hQne
        · exact h
      exact hQ3.trans (Subgroup.card_dvd_of_le (le_inf hQM hQ.le))
    have hY := isStronglyPEmbedded_inf hM's hLM' hdvd
    have hNY : CFSG.pPrimeCore m.r ↥m.L ≤ (M' ⊓ m.L).subgroupOf m.L := fun x hx =>
      Subgroup.mem_subgroupOf.2 ⟨hYM (Subgroup.mem_map.2 ⟨x, hx, rfl⟩), x.2⟩
    have hpN : ¬ 3 ∣ Nat.card ↥(CFSG.pPrimeCore m.r ↥m.L) := by
      have hc : Nat.card (N588.rCore m.r m.L) = Nat.card ↥(CFSG.pPrimeCore m.r ↥m.L) :=
        Subgroup.card_map_of_injective m.L.subtype_injective
      rwa [← hc]
    exact hX.2 m.Lbar hL _ (hY.map_quotient hNY hpN)
  have hHM' : m.H ≤ M' := by
    rw [frattini_of_isSylowOf m.L_le_H m.H_le_normalizer_L hQ]
    exact sup_le hLM' (inf_le_right.trans (hM's.normalizer_le hQne hQ.isPGroup hQM))
  have hconj : uniqueFourConj g⁻¹ m.M = M' := by
    rw [hM', uniqueFourConj, inv_inv]
  have hU := m.d.inU_of_le m.hC le_rfl (Mc614.E_ne_bot m.toMc614)
  have hMM : M' = m.M := by
    rw [← hconj]
    exact hU.2 g⁻¹ (hconj ▸ m.hZ.E_le_centralizer.trans hHM')
  exact m.hZ.not_le (hMM ▸ hHM')

end CFSG.LocalAnalysis.UniquenessCase.UC6
