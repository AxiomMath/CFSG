module

import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3LRank
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3Tor
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251h
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.AGLEmbedding.AltBetaRank
import CFSG.Quasithin.Vol2.Ch4Sec2T425C27A
import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Rank
import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114r3l_kernel {K : Subgroup G} {Z : Type*} [Group Z] [Finite Z] (θ : ↥K →* Z)
    {p : ℕ} (hp : p.Prime) (hZ : CFSG.Open.pRank p (⊤ : Subgroup Z) ≤ 1) {R : Subgroup G}
    (hRK : R ≤ K) (hR : IsElemAbelian p R) (hRc : Nat.card R = p ^ 3) :
    ∃ F ≤ R, IsElemAbelian p F ∧ Nat.card F = p ^ 2 ∧ ∀ x : ↥K, (x : G) ∈ F → θ x = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hR' : IsElemAbelian p (R.subgroupOf K) := hR.subgroupOf K
  have hRc' : Nat.card (R.subgroupOf K) = p ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv, hRc]
  have hle : θ.ker ⊓ R.subgroupOf K ≤ R.subgroupOf K := inf_le_right
  obtain ⟨i, hi⟩ := IsPGroup.iff_card.mp (hR'.map θ).isPGroup
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (hR'.isPGroup.to_le hle)
  have hi1 := (CFSG.SectionRank.le_pRank hp.one_lt le_top (hR'.map θ) hi).trans hZ
  have h := Subgroup.relIndex_mul_card θ.ker (R.subgroupOf K)
  rw [Subgroup.relIndex_ker, hi, hj, hRc', ← pow_add] at h
  have hij := Nat.pow_right_injective hp.two_le h
  obtain ⟨F, hF, hFel, hFc⟩ := UC6S846.exists_card_p_sq hp (hR'.mono hle)
    (by rw [hj]; exact Nat.pow_le_pow_right hp.pos (by omega))
  refine ⟨F.map K.subtype, ?_, hFel.map K.subtype, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hF hx).2
  · rw [Subgroup.card_map_of_injective K.subtype_injective, hFc]
  · rintro x ⟨y, hy, hyx⟩
    obtain rfl : y = x := K.subtype_injective hyx
    exact MonoidHom.mem_ker.1 (hF hy).1

theorem uc22s2114r3l_strongly_of_a8 (hGA : GriessAllModelsStatement) {D : Data G}
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hML : D.M ≤ normalizer (L : Set G))
    (hX : LieModel (BarInf L) .PSL 4 2 1) : IsStronglyPEmbedded 3 D.M := by
  have hns := UC6S846.not_solvable_of_mem_calC hL
  by_contra h3
  obtain ⟨eA⟩ := uc22s2114r3l_nonempty_mulEquiv_alt_eight hGA hL hX
  obtain ⟨p, hpσ⟩ := hSg.nonempty
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  have hp3 : p ≠ 3 := fun h => h3 (h ▸ UC6S846.sp_of_mem_sig hSg hns hpσ)
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    by_contra h
    interval_cases p <;> first | omega | norm_num at hp
  obtain ⟨R, hRM, hRel, hRc⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hp (hSg.three_le p hpσ)
  have hAut : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Bar2 L))) ≤ 1 := by
    have h8 := CFSG.AGLEmbedding.pRank_top_mulAut_le (by norm_num) (by norm_num) eA hp
    have := (Nat.div_lt_iff_lt_mul hp.pos).2 (show 8 < 2 * p by omega)
    omega
  obtain ⟨F, hFR, hFel, hFc, hFker⟩ := uc22s2114r3l_kernel
    ((UC6S846.rhoL L).comp (Subgroup.inclusion hML)) hp hAut hRM hRel hRc
  have hFN : F ≤ normalizer (L : Set G) := fun x hx => hML (hRM (hFR hx))
  have hc : ⁅F, L⁆ ≤ pCoreOf 2 L := by
    rw [Subgroup.commutator_le]
    intro a ha l hl
    have h1 : UC6S846.rhoL L ⟨a, hFN ha⟩ = 1 := hFker ⟨a, hRM (hFR ha)⟩ ha
    have h2 : UC6S846.rhoL L ⟨a, hFN ha⟩ (QuotientGroup.mk ⟨l, hl⟩) =
        QuotientGroup.mk ⟨l, hl⟩ := by
      rw [h1]
      rfl
    rw [commutatorElement_def]
    exact (UC6S846.rhoL_fix_iff L _ _).1 h2
  have hYL : L ⊓ centralizer (F : Set G) ≤ L := inf_le_left
  have hsurj := P2251h.barMap_surjective hYL fun b hb =>
    P2251h.exists_mem_inf_centralizer hp hp2 hFel.isPGroup hFN hc hb
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hY3 : 2 ≤ CFSG.Open.pRank 3 (L ⊓ centralizer (F : Set G)) :=
    CFSG.Quasithin.H13.Ch4.T425C27.two_le_pRank_of_surjective
      (eA.toMonoidHom.comp (P2251h.barMap hYL)) (eA.surjective.comp hsurj) (by norm_num)
      CFSG.Quasithin.H13.Rank8.two_le_pRank_alternating_eight
  obtain ⟨E, hEY, hEel, hEc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank Nat.prime_three hY3
  have hFE : F ≤ D.M ⊓ centralizer (E : Set G) := fun x hx =>
    ⟨hRM (hFR hx), Subgroup.mem_centralizer_iff.2 fun e he =>
      (Subgroup.mem_centralizer_iff.1 (hEY he).2 x hx).symm⟩
  have hcard : Nat.card (Bar2 L) = 20160 := by
    rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have hab : ∀ P : Sylow 3 (Bar2 L), IsMulCommutative (P : Subgroup (Bar2 L)) := by
    intro P
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
    have h9 : 3 ^ 2 ∣ 3 ^ k := hk ▸ P.pow_dvd_card_of_pow_dvd_card (by rw [hcard]; norm_num)
    have hdvd : 3 ^ k ∣ 20160 := hk ▸ hcard ▸ Subgroup.card_subgroup_dvd_card _
    have hk2 : k = 2 := by
      have := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h9
      by_contra hne
      have h27 : 3 ^ 3 ∣ 20160 := (Nat.pow_dvd_pow 3 (by omega)).trans hdvd
      norm_num at h27
    exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (by rw [hk, hk2])
  have hout : ¬ 3 ∣ Nat.card (Outer (Bar2 L)) := by
    obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2
      (Subgroup.card_eq_one.1 (uc22s2114r3l_card_center_eq_one hGA hL (Or.inl hX)))
    have hd := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      (T := BarInf L) (Or.inl rfl) (by norm_num) Nat.prime_two le_rfl
      (LieModel.statedClassicalModel hX (by decide))).1
    rw [Nat.card_congr (equivalence e).toEquiv] at hd
    intro h3d
    have h32 : 3 ∣ 2 * 1 * Nat.gcd 4 (2 ^ 1 - 1) := h3d.trans hd
    norm_num at h32
  exact h3 (uc22s2114r3_strongly_of_centralizer hSg h76 h614 hL hML Nat.prime_three
    (by norm_num) hab hout hpσ (hEY.trans hYL) hEel hEc
    (CFSG.SectionRank.le_pRank hp.one_lt hFE hFel hFc))

end CFSG.LocalAnalysis.UniquenessCase.UC22
