module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Stab
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36StrongEmb
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneSixSeven
import CFSG.LocalAnalysis.UniquenessCase.UC6K36Sub
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
import CFSG.RankThree.PartOne.S11d.ThreeAux
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (Star36)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.RankThree.PartOne.StrongP (conjSub)

variable {G : Type} [Group G] [Finite G]

theorem not_le_of_isComponent {q : ℕ} [Fact q.Prime] {H K : Subgroup G} (hH : IsStronglyPEmbedded q H)
    (hK : CFSG.IsComponent K) (hqK : q ∣ Nat.card K) : ¬ K ≤ H := by
  intro hKH
  obtain ⟨x, hxo⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) q hqK
  have hxq : (x : G) ^ q = 1 := by
    have := pow_orderOf_eq_one x
    rw [hxo] at this
    exact congrArg Subtype.val this
  have hx1 : (x : G) ≠ 1 := by
    intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hxo
    exact (Fact.out : q.Prime).one_lt.ne hxo
  have hC : centralizer ({(x : G)} : Set G) ≤ H := hH.centralizer_le hx1 hxq (hKH x.2)
  have hconj : ∀ g : G, K.map (MulAut.conj g).toMonoidHom ≤ H := by
    intro g
    rcases CFSG.LocalCores.distinct_components_commute
      (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hK) hK with hg | hg
    · rw [hg]
      exact hKH
    · have hle : K.map (MulAut.conj g).toMonoidHom ≤ centralizer (K : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.1 hg
      intro y hy
      refine hC (Subgroup.mem_centralizer_iff.2 fun z hz => ?_)
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact Subgroup.mem_centralizer_iff.1 (hle hy) _ x.2
  have hN : (Subgroup.normalClosure (K : Set G)) ≤ H := by
    refine (Subgroup.closure_le H).2 fun y hy => ?_
    obtain ⟨a, ha, hc⟩ := Group.mem_conjugatesOfSet_iff.1 hy
    obtain ⟨c, rfl⟩ := isConj_iff.1 hc
    exact hconj c ⟨a, ha, by simp [MulAut.conj_apply]⟩
  haveI : (Subgroup.normalClosure (K : Set G)).Normal := Subgroup.normalClosure_normal
  exact hH.not_dvd_card_of_normal_le hN (hqK.trans (Subgroup.card_dvd_of_le Subgroup.le_normalClosure))

theorem map_star36Sup_le {X : Subgroup G} {q : ℕ} (hq : q.Prime) {S : Subgroup ↥X} {S' : Subgroup G}
    (hSS' : S.map X.subtype ≤ S') : (star36Sup q S).map X.subtype ≤ star36Sup q S' := by
  have hΓ : rankThreeGamma 1 q S' ≤ star36Sup q S' := le_sup_left
  rw [star36Sup, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · refine le_trans ?_ hΓ
    rw [Subgroup.map_le_iff_le_comap, CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff]
    intro Y hYS hY1 x hx
    have hY' : Y.map X.subtype ≤ S' := (Subgroup.map_mono hYS).trans hSS'
    have hr : 1 ≤ CFSG.Open.pRank q (Y.map X.subtype) :=
      hY1.trans (CFSG.SectionRank.pRank_le_map hq.one_lt X.subtype X.subtype_injective Y)
    exact CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hY' hr
      (map_normalizer_subtype_le' Y (Subgroup.mem_map.2 ⟨x, hx, rfl⟩))
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup_le fun Y => iSup_le fun hYS => iSup_le fun hY2 => iSup₂_le fun N hN => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    obtain ⟨hNmax, hYN⟩ := hN
    obtain ⟨P, hPne, hP2, hNP⟩ := hNmax.1
    have hP₀ne : P.map X.subtype ≠ ⊥ := fun h0 =>
      hPne ((Subgroup.map_eq_bot_iff_of_injective P X.subtype_injective).1 h0)
    have hloc : IsTwoLocal (Subgroup.normalizer (P.map X.subtype : Set G)) :=
      ⟨_, hP₀ne, hP2.map X.subtype, rfl⟩
    obtain ⟨N', hN'max, hN'⟩ := exists_isMaxTwoLocal_ge_of_isTwoLocal hloc
    have hNN' : N.map X.subtype ≤ N' := by
      rw [hNP]
      exact (map_normalizer_subtype_le' P).trans hN'
    have hY'S : Y.map X.subtype ≤ S' := (Subgroup.map_mono hYS).trans hSS'
    have hY'2 : 1 < CFSG.Open.pRank q (Y.map X.subtype) :=
      hY2.trans_le (CFSG.SectionRank.pRank_le_map hq.one_lt X.subtype X.subtype_injective Y)
    have hmem : N' ∈ calMOf (Y.map X.subtype) := ⟨hN'max, (Subgroup.map_mono hYN).trans hNN'⟩
    have hle : N' ≤ star36Sup q S' := le_star36Sup_of_mem_calMOf hY'S hY'2 hmem
    exact hNN'.trans hle

theorem dvd_card_of_three_lt_twoLocalPrimeRank {q : ℕ} (hq : q.Prime) {Y : Type} [Group Y] [Finite Y]
    (h : 3 < twoLocalPrimeRank q Y) : q ∣ Nat.card Y := by
  have hne : {k | ∃ H : Subgroup Y, IsTwoLocal H ∧ CFSG.Open.pRank q H = k}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    unfold twoLocalPrimeRank at h
    simp [hemp] at h
  obtain ⟨H, -, hH⟩ := Nat.sSup_mem hne (CFSG.PreuniquenessRankFour.Helpers.twoLocalRank_bddAbove q hq)
  refine CFSG.PreuniquenessRankFour.Helpers.prime_dvd_card_of_positive_rank q hq H ?_
  unfold twoLocalPrimeRank at h
  rw [← hH] at h
  omega

namespace Hyp36

variable {M E : Subgroup G} {p : ℕ} (h : Hyp36 G M p E)
include h

theorem card_sup_dvd {N : Subgroup G} (hEN : E ≤ normalizer (N : Set G))
    (hQN : pCoreOf 2 M ≤ normalizer (N : Set G)) :
    Nat.card ↥(E ⊔ pCoreOf 2 M ⊔ N) ∣ Nat.card E * Nat.card (pCoreOf 2 M) * Nat.card N := by
  have hEQ : E ≤ normalizer (pCoreOf 2 M : Set G) :=
    h.E_le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have h1 : Nat.card ↥(pCoreOf 2 M ⊔ E) ∣ Nat.card (pCoreOf 2 M) * Nat.card E :=
    CFSG.RankThree.PartOne.card_sup_dvd_of_le_normalizer' _ _ hEQ
  have h2 : Nat.card ↥(N ⊔ (pCoreOf 2 M ⊔ E)) ∣ Nat.card N * Nat.card ↥(pCoreOf 2 M ⊔ E) :=
    CFSG.RankThree.PartOne.card_sup_dvd_of_le_normalizer' _ _ (sup_le hQN hEN)
  have heq : E ⊔ pCoreOf 2 M ⊔ N = N ⊔ (pCoreOf 2 M ⊔ E) := by rw [sup_comm E, sup_comm N]
  rw [heq]
  refine h2.trans ?_
  have h3 := mul_dvd_mul_left (Nat.card N) h1
  have h4 : Nat.card E * Nat.card (pCoreOf 2 M) * Nat.card N =
      Nat.card N * (Nat.card (pCoreOf 2 M) * Nat.card E) := by ring
  rw [h4]
  exact h3

theorem eq_or_dvd_of_dvd_card_sup {N : Subgroup G} (hEN : E ≤ normalizer (N : Set G))
    (hQN : pCoreOf 2 M ≤ normalizer (N : Set G)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrX : r ∣ Nat.card ↥(E ⊔ pCoreOf 2 M ⊔ N)) : r = p ∨ r ∣ Nat.card N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := hrX.trans (h.card_sup_dvd hEN hQN)
  rcases (Nat.Prime.dvd_mul hr).1 hd with hd | hd
  · rcases (Nat.Prime.dvd_mul hr).1 hd with hd | hd
    · left
      rw [h.card] at hd
      exact (Nat.prime_dvd_prime_iff_eq hr h.prime).1 (hr.dvd_of_dvd_pow hd)
    · exfalso
      obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).exists_card_eq
      rw [ha] at hd
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hd))
  · right
    exact hd

end Hyp36

theorem star36_sub_or (hS : Star36 G) (X : Subgroup G) :
    Star36 ↥X ∨ ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ Nat.card X ∧
      ∃ H : Subgroup G, IsStronglyPEmbedded q H ∧ X ≤ H := by
  by_cases hex : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ Nat.card X ∧
      ∃ H : Subgroup G, IsStronglyPEmbedded q H ∧ X ≤ H
  · exact Or.inr hex
  left
  push Not at hex
  intro q hq hq2 h4 S hSX
  haveI : Fact q.Prime := ⟨hq⟩
  have hqX : q ∣ Nat.card X := dvd_card_of_three_lt_twoLocalPrimeRank hq h4
  have hqG : q ∣ Nat.card G := hqX.trans (Subgroup.card_subgroup_dvd_card X)
  obtain ⟨SG, hSSG⟩ := (hSX.isPGroup.map X.subtype).exists_le_sylow
  have hSG : CFSG.ABGLocalTools.IsSylowOf q (SG : Subgroup G) ⊤ :=
    (CFSG.ABGLocalTools.isSylowOf_iff).2 ⟨le_top, SG.isPGroup', by
      rw [Subgroup.relIndex_top_right]
      exact SG.not_dvd_index⟩
  have h4G : 3 < twoLocalPrimeRank q G := h4.trans_le (twoLocalPrimeRank_subgroup_le' hq X)
  rcases hS q hq hq2 h4G SG hSG with ha | ⟨hq3, hb⟩
  · left
    have hSG1 : (SG : Subgroup G) ≠ ⊥ := SG.ne_bot_of_dvd_card hqG
    have hH : IsStronglyPEmbedded q (star36Sup q (SG : Subgroup G)) :=
      isStronglyPEmbedded_star36Sup hSG hSG1 ha
    intro htop
    have htop' : star36Sup q S = ⊤ := htop
    have hmap := map_star36Sup_le hq hSSG
    rw [htop', ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
    exact hex q hq hq2 hqX _ hH hmap
  · right
    refine ⟨hq3, fun h3X => ?_⟩
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3G : 3 ∣ Nat.card G := h3X.trans (Subgroup.card_subgroup_dvd_card X)
    obtain ⟨N, hN⟩ := hb h3G
    obtain ⟨T⟩ : Nonempty (Sylow 3 ↥X) := inferInstance
    obtain ⟨P₁, hTP₁⟩ := (T.isPGroup'.map X.subtype).exists_le_sylow
    have hP₁ : CFSG.RankThree.PartOne.IsSylowOf 3 (P₁ : Subgroup G) ⊤ :=
      ⟨le_top, P₁.isPGroup', by
        rw [Subgroup.relIndex_top_right]
        exact P₁.not_dvd_index⟩
    obtain ⟨g, hg⟩ := hN.exists_conj_ge hP₁
    have hN' := hN.conj g
    have hXN : ¬ X ≤ conjSub g N := hex 3 Nat.prime_three (by norm_num) h3X _ hN'
    have hdvd : 3 ∣ Nat.card (X ⊓ conjSub g N : Subgroup G) := by
      have hT3 : 3 ∣ Nat.card (T : Subgroup ↥X) := T.dvd_card_of_dvd_card h3X
      have hle : (T : Subgroup ↥X).map X.subtype ≤ X ⊓ conjSub g N :=
        le_inf (Subgroup.map_subtype_le _) (hTP₁.trans hg)
      refine (Dvd.dvd.trans ?_ (Subgroup.card_dvd_of_le hle))
      rwa [Subgroup.card_map_of_injective X.subtype_injective]
    exact ⟨_, hN'.subgroupOf hXN hdvd⟩

namespace Hyp36

variable {M E : Subgroup G} {p : ℕ} (h : Hyp36 G M p E)
include h

theorem star36_comp (hS : Star36 G) {K : Subgroup G} (hK : CFSG.IsComponent K)
    (hne : ⁅K, pCoreOf 2 M⁆ ≠ ⊥) : Star36 ↥(E ⊔ pCoreOf 2 M ⊔ K) := by
  rcases star36_sub_or hS (E ⊔ pCoreOf 2 M ⊔ K) with hst | ⟨q, hq, hq2, hqX, H, hH, hXH⟩
  · exact hst
  · exfalso
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨hEN, hQN⟩ := h.normalizes_component hK hne
    have hqK : q ∣ Nat.card K := by
      rcases h.eq_or_dvd_of_dvd_card_sup hEN hQN hq hq2 hqX with hqp | hqK
      · rw [hqp]
        exact h.dvd_card_component hK hne
      · exact hqK
    exact not_le_of_isComponent hH hK hqK (le_sup_right.trans hXH)

theorem star36_cent_or_le (hS : Star36 G) (Λ : Subgroup G) [Λ.Normal] :
    Star36 ↥(E ⊔ pCoreOf 2 M ⊔ centralizer (Λ : Set G)) ∨ centralizer (Λ : Set G) ≤ M := by
  haveI hCn : (centralizer (Λ : Set G)).Normal := Subgroup.normal_centralizer (H := Λ)
  have hCnorm : normalizer (centralizer (Λ : Set G) : Set G) = ⊤ := Subgroup.normalizer_eq_top_iff.2 hCn
  rcases star36_sub_or hS (E ⊔ pCoreOf 2 M ⊔ centralizer (Λ : Set G)) with
    hst | ⟨q, hq, hq2, hqX, H, hH, hXH⟩
  · exact Or.inl hst
  · right
    haveI : Fact q.Prime := ⟨hq⟩
    have hEN : E ≤ normalizer (centralizer (Λ : Set G) : Set G) := by
      rw [hCnorm]
      exact le_top
    have hQN : pCoreOf 2 M ≤ normalizer (centralizer (Λ : Set G) : Set G) := by
      rw [hCnorm]
      exact le_top
    have hqC : ¬ q ∣ Nat.card (centralizer (Λ : Set G)) :=
      hH.not_dvd_card_of_normal_le (le_sup_right.trans hXH)
    have hqp : q = p := (h.eq_or_dvd_of_dvd_card_sup hEN hQN hq hq2 hqX).resolve_right hqC
    rw [hqp] at hqC
    haveI : Fact p.Prime := ⟨h.prime⟩
    have hle : centralizer (Λ : Set G) ≤ relPPrimeCore p (⊤ : Subgroup G) :=
      le_sSup ⟨le_top, hCn.subgroupOf ⊤, (Nat.Prime.coprime_iff_not_dvd h.prime).2 hqC⟩
    exact hle.trans h.pPrimeCore_le

end Hyp36

end CFSG.LocalAnalysis.UniquenessCase.UCK
