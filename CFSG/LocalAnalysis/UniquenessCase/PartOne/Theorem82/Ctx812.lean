module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Core
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
import CFSG.LocalAnalysis.SectionRank.PRankIndex

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Yardstones.Mf4cdcdf2e013 (Hyp81 TheoremCAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Sec7Core4)

variable {G : Type} [Group G] [Finite G]

theorem pRank_le_of_not_dvd_index {p : ℕ} (hpp : p.Prime) {M L : Subgroup G} (hLM : L ≤ M)
    (hindex : ¬ p ∣ (L.subgroupOf M).index) :
    CFSG.Open.pRank p M ≤ CFSG.Open.pRank p L := by
  have hrankM : CFSG.Open.pRank p (⊤ : Subgroup ↥M) ≤ CFSG.Open.pRank p (L.subgroupOf M) :=
    CFSG.SectionRank.pRank_top_le_of_not_dvd_index hpp _ hindex
  have hMtop : CFSG.Open.pRank p (⊤ : Subgroup ↥M) = CFSG.Open.pRank p M :=
    (CFSG.SectionRank.pRank_eq_open_pRank_top p ↥M).symm.trans
      (CFSG.SectionRank.pRank_coe_eq_openPRank p M)
  have hLtop : CFSG.Open.pRank p (L.subgroupOf M) = CFSG.Open.pRank p L := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank p (L.subgroupOf M),
      CFSG.pRank_congr_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLM) p,
      CFSG.SectionRank.pRank_coe_eq_openPRank p L]
  rw [← hMtop, ← hLtop]
  exact hrankM

structure Setup812 (G : Type) [Group G] [Finite G] where
  M : Subgroup G
  maxLocal : IsMaxTwoLocalSubgroup M

structure C4Data (G : Type) [Group G] [Finite G] (M : Subgroup G) where
  notCatalog : ¬ CFSG.Blueprint.Catalog G
  V : Subgroup G
  le : V ≤ M
  le_normalizer : M ≤ Subgroup.normalizer (V : Set G)
  elemAbelian : IsElemAbelian 2 V
  not_isTI : ¬ CFSG.CGT.Timmesfeld75.IsTI V

structure Ctx812E (G : Type) [Group G] [Finite G] where
  k : ℕ
  three_le_k : 3 ≤ k
  standing : CFSG.LocalAnalysis.UniquenessCase.UC22.StandingGe3 G
  S : Setup812 G
  sig : Set ℕ
  sig_prime : ∀ p ∈ sig, p.Prime ∧ p ≠ 2
  rank_ge : ∀ p ∈ sig, k ≤ CFSG.Open.pRank p S.M
  four_le_imp_mem : ∀ r : ℕ, r.Prime → r ≠ 2 → 4 ≤ CFSG.Open.pRank r S.M → r ∈ sig
  strong : ∀ p ∈ sig, IsStronglyPEmbedded p S.M
  u2 : ∀ p ∈ sig, ∀ H : Subgroup G, IsTwoLocal H → 2 ≤ CFSG.Open.pRank p (H ⊓ S.M) → H ≤ S.M
  rankK : ∀ p ∈ sig, ∀ H : Subgroup G, ¬ H ≤ S.M → 2 ≤ CFSG.Open.pRank p (H ⊓ S.M) →
    ∀ q : ℕ, q.Prime → CFSG.Open.pRank q ((CFSG.pPrimeCore p ↥H).map H.subtype) ≤ 3
  theoremC : TheoremCAt S.M
  three_not_mem_beta : 3 ∉ uniqueFourBeta G
  not_rankThreeGamma_le_of_le_center : ∀ {P E : Subgroup G},
    CFSG.ABGLocalTools.IsSylowOf 3 P S.M → E ≤ P ⊓ Subgroup.centralizer (P : Set G) →
    IsElemAbelian 3 E → Nat.card E = 3 ^ 2 → ¬ rankThreeGamma 1 3 E ≤ S.M
  L : Subgroup G
  hyp81 : Hyp81 S.M L
  not_strong : ¬ IsStronglyPEmbedded 3 S.M

structure Ctx812 (G : Type) [Group G] [Finite G] extends Ctx812E G where
  dvd_index : ∀ p ∈ sig, CFSG.Open.pRank p L ≤ 3 → p ∣ (L.subgroupOf S.M).index
  c4 : C4Data G S.M

namespace Ctx812E

theorem isStronglyPEmbedded_of_mem_sigma (c : Ctx812E G) {p : ℕ} (hp : p ∈ c.sig) :
    IsStronglyPEmbedded p c.S.M :=
  c.strong p hp

theorem three_not_mem_sigma (c : Ctx812E G) : 3 ∉ c.sig :=
  fun h3 => c.not_strong (c.strong 3 h3)

theorem five_le_of_mem_sigma (c : Ctx812E G) {p : ℕ} (hp : p ∈ c.sig) : 5 ≤ p := by
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact three_not_mem_sigma c hp
  exact Nat.Prime.five_le_of_ne_two_of_ne_three (c.sig_prime p hp).1 (c.sig_prime p hp).2 hp3

theorem M_ne_top (c : Ctx812E G) : c.S.M ≠ ⊤ := by
  have := c.standing.simple
  exact CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top c.standing.nonab c.S.maxLocal.1

theorem pRank_three_M (c : Ctx812E G) : CFSG.Open.pRank 3 c.S.M = 3 := by
  have h3prime : (3 : ℕ).Prime := by norm_num
  have h3dvdG : 3 ∣ Nat.card G :=
    CFSG.PreuniquenessRankFour.Helpers.prime_dvd_card_of_positive_rank 3 h3prime c.L
      (by have := c.hyp81.2.2.2.1; omega)
  have hle3 : CFSG.Open.pRank 3 c.S.M ≤ 3 := by
    have hrank : CFSG.Open.pRank 3 c.S.M ≤ uniqueFourTwoLocalRank 3 G :=
      le_csSup (CFSG.PreuniquenessRankFour.Helpers.twoLocalRank_bddAbove 3 h3prime)
        ⟨c.S.M, c.S.maxLocal.1, rfl⟩
    have hnot4 : ¬ 4 ≤ uniqueFourTwoLocalRank 3 G := by
      intro h4
      exact c.three_not_mem_beta ⟨h3prime, by norm_num, h3dvdG, h4⟩
    omega
  have hge3 : 3 ≤ CFSG.Open.pRank 3 c.S.M :=
    c.hyp81.2.2.2.1.trans
      (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3prime c.hyp81.1)
  omega

theorem pRank_three_L (c : Ctx812E G) : CFSG.Open.pRank 3 c.L = 3 := by
  apply le_antisymm
  · exact (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 (by norm_num) c.hyp81.1).trans
      (pRank_three_M c).le
  · exact c.hyp81.2.2.2.1

@[expose] def toSec7Core4 (c : Ctx812E G) {p : ℕ} (hp : p ∈ c.sig) : Sec7Core4 G where
  standing := c.standing
  M := c.S.M
  maxLocal := c.S.maxLocal
  p := p
  prime := (c.sig_prime p hp).1
  odd := (c.sig_prime p hp).2
  strong := c.strong p hp
  huniq := fun D hD hD2 h2 => c.u2 p hp _ ⟨D, hD, hD2, rfl⟩ h2
  rankK := c.rankK p hp

end Ctx812E

@[expose] def Counterexample4.toCtx812 (c : Counterexample4 G) : Ctx812 G where
  k := 4
  three_le_k := by norm_num
  standing := ⟨c.standing.simple, c.standing.nonab, c.standing.kProper, c.standing.charTwo,
    le_trans (by norm_num) c.standing.rank⟩
  S := ⟨c.S.M, c.S.maxLocal⟩
  c4 := ⟨c.S.notCatalog, c.S.V, c.S.le, c.S.le_normalizer, c.S.elemAbelian, c.S.not_isTI⟩
  sig := uniqueFourSigma c.S.M
  sig_prime := fun _ hp => ⟨hp.1.1, hp.1.2.1⟩
  rank_ge := fun _ hp => c.four_le_pRank_of_mem_sigma hp
  four_le_imp_mem := fun _ hr hr2 h4 =>
    CFSG.LocalAnalysis.UniquenessCase.UC6.four_le_pRank_imp_mem_sigma c.unique c.S.maxLocal
      hr hr2 h4
  strong := fun _ hp => c.isStronglyPEmbedded_of_mem_sigma hp
  u2 := fun _ hp _ hH h2 =>
    CFSG.LocalAnalysis.UniquenessCase.UC6.sec61 c.unique c.S.maxLocal hp inf_le_right h2 hH
      inf_le_left
  rankK := fun _ hp _ hHM h2 _ hq =>
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.pRank_pPrimeCore_le_three_of_uniqueFourUnique
      c.unique c.S.maxLocal hp (c.isStronglyPEmbedded_of_mem_sigma hp) hHM h2 hq
  theoremC := c.theoremC
  three_not_mem_beta := c.three_not_mem_beta
  not_rankThreeGamma_le_of_le_center := fun hP hE hEab hcard =>
    c.not_rankThreeGamma_le_of_le_center hP hE hEab hcard
  L := c.L
  hyp81 := c.hyp81
  not_strong := c.not_strong
  dvd_index := fun p hp hL3 => by
    by_contra hnd
    have h4 := c.four_le_pRank_of_mem_sigma hp
    have hle := pRank_le_of_not_dvd_index hp.1.1 c.hyp81.1 hnd
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
