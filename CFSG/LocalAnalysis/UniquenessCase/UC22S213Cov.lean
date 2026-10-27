module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213CovSylow
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Inner
import CFSG.LocalAnalysis.UniquenessCase.UC6R869MConj
import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizingRank
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ConjRank857
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SylowNormalizer859
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.InnerBarDecomp
import CFSG.LocalAnalysis.StronglyEmbedded.OfCentralizers
import CFSG.LocalAnalysis.StronglyEmbedded.GammaOne
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.GroupTheory.ComponentCovering
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Setup
import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76 StronglyEmbeddedFive)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem uc22s213_mem_of_pow_three_eq_one {X : Type*} [Group X] [Finite X]
    {M Q C E : Subgroup X} (hm3 : CFSG.Open.pRank 3 M ≤ 2) (hQM : Q ≤ M) (hCM : C ≤ M)
    (hCQ : C ≤ normalizer (Q : Set X)) (hcomm : ∀ q ∈ Q, ∀ c ∈ C, q * c = c * q)
    (hexp : ∀ q ∈ Q, q ^ 3 = 1) (hEQ : E ≤ Q) (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 2) {x : X} (hx : x ∈ Q ⊔ C) (hx3 : x ^ 3 = 1) : x ∈ Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left Q C hCQ] at hx
  obtain ⟨q, hq, c, hc, rfl⟩ := Set.mem_mul.mp hx
  have hc3 : c ^ 3 = 1 := by
    rwa [Commute.mul_pow (hcomm q hq c hc) 3, hexp q hq, one_mul] at hx3
  by_cases hcQ : c ∈ Q
  · exact Q.mul_mem hq hcQ
  exfalso
  have hco : orderOf c = 3 := orderOf_eq_prime hc3 fun h => hcQ (h ▸ Q.one_mem)
  have hcE : c ∈ centralizer (E : Set X) := by
    rw [mem_centralizer_iff]
    exact fun e he => hcomm e (hEQ he) c hc
  have h3 := CFSG.AGLEmbedding.three_le_pRank_of_isElemAbelian_sq_of_mem_centralizer
    Nat.prime_three hE hEc hco (fun h => hcQ (hEQ h)) hcE (hEQ.trans hQM) (hCM hc)
  omega

theorem uc22s213_strong_of_cover (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hσ : S.InMSigma) (hSE : StronglyEmbeddedFive)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (hout : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
      ∀ s : TauCeti.SporadicName, IsSpor X s → Nat.card (Outer X) ≤ 2)
    {L : Subgroup G} (hL : L ∈ calC S.M)
    (hcov : F08.IsA6Z3 (Bar2 L) ∨ F08.IsA7Z3 (Bar2 L) ∨ F08.IsM22Z3 (Bar2 L))
    (hm3 : CFSG.Open.pRank 3 S.M ≤ 2) (hp : CFSG.Open.pRank S.p L ≤ 1) :
    IsStronglyPEmbedded 3 S.M := by
  by_contra hnot
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hodd : ∀ {r : ℕ} {H : Subgroup G}, r.Prime → r ≠ 2 → IsPGroup r H → ∀ y ∈ H,
      Odd (orderOf y) := by
    intro r H hr hr2 hH y hy
    haveI := Fact.mk hr
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hH ⟨y, hy⟩
    rw [Subgroup.orderOf_mk] at hk
    exact hk ▸ (hr.odd_of_ne_two hr2).pow
  have hLM : L ≤ S.M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hcard := PartOne.Section8.ncard_conjSetOf_le_two_of_cover hL hcov (by omega)
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 S.M
  have hPN := PartOne.Section8.sylow_le_normalizer_of_ncard_conjSetOf_le_two hP hL hcard
  have hQ : IsSylowOf 3 (P ⊓ L) L := hP.inf_of_isSubnormal hL.1
  obtain ⟨hQ27, hQexp, E, hEQ, hEel, hEc⟩ := uc22s213_card_sylow_of_cover hcov hQ
  have hQr : 2 ≤ CFSG.Open.pRank 3 (P ⊓ L) :=
    CFSG.SectionRank.le_pRank (by norm_num) hEQ hEel hEc
  have hPQ : P ≤ normalizer ((P ⊓ L : Subgroup G) : Set G) :=
    (le_inf le_normalizer hPN).trans inf_normalizer_le_normalizer_inf
  have hdec : P ≤ P ⊓ L ⊔ PartOne.Section8.centralizerBar P L :=
    PartOne.Section8.le_sup_centralizerBar_of_inner inf_le_left inf_le_right rfl
      (normal_subgroupOf_of_le_normalizer hPQ) hQ hP.isPGroup hPN le_rfl fun y hy =>
        uc22s213_exists_inner_of_odd hL.2.2 (uc22s213_inner_of_cover hout hL hcov) (hPN hy)
          (hodd Nat.prime_three (by norm_num) hP.isPGroup y hy)
  have hQO2 : P ⊓ L ⊓ CFSG.Open.pCoreOf 2 L = ⊥ :=
    (IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _ hQ.isPGroup
      (UC6S846.isPGroup_pCoreOf L)).eq_bot
  have hcomm : ∀ q ∈ P ⊓ L, ∀ c ∈ PartOne.Section8.centralizerBar P L, q * c = c * q := by
    intro q hq c hc
    have h := commutator_mem_commutator hq hc
    rwa [PartOne.Section8.commutator_eq_bot_centralizerBar inf_le_right hQO2 hPQ, mem_bot,
      commutatorElement_eq_one_iff_mul_comm] at h
  have hall : ∀ y ∈ P, y ^ 3 = 1 → y ∈ P ⊓ L := fun y hy hy3 =>
    uc22s213_mem_of_pow_three_eq_one hm3 (inf_le_left.trans hP.le)
      ((PartOne.Section8.centralizerBar_le P L).trans hP.le)
      ((PartOne.Section8.centralizerBar_le P L).trans hPQ) hcomm hQexp hEQ hEel hEc (hdec hy) hy3
  have hNQ : normalizer (P : Set G) ≤ normalizer ((P ⊓ L : Subgroup G) : Set G) := by
    intro g hg
    rw [mem_normalizer_iff] at hg ⊢
    intro y
    constructor
    · intro hy
      refine hall _ ((hg y).1 (mem_inf.mp hy).1) ?_
      rw [conj_pow, hQexp y hy, mul_one, mul_inv_cancel]
    · intro hy
      refine hall y ((hg y).2 (mem_inf.mp hy).1) ?_
      have h := hQexp _ hy
      rwa [conj_pow, conj_eq_one_iff] at h
  have h3β : 3 ∉ uniqueFourBeta G := fun h =>
    hnot (isStronglyPEmbedded_three_of_mem_uniqueFourBeta hU S hσ h)
  have hpp : S.p.Prime := S.hp.1.1
  have hp2 : S.p ≠ 2 := S.hp.1.2.1
  haveI : Fact S.p.Prime := ⟨hpp⟩
  have hsp := PartOne.Section8.isStronglyPEmbedded_of_mem_sigma_of_calC hS hU S hL S.hp
  have h76 : Conclusion76 S.M S.p := UC6.conclusion76_dataOfSetup4 hSE hS hU S h3β S.hp hsp
  obtain ⟨B, hBM, hBel, hBc⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hpp (UC6.four_le_pRank_of_sigma S.hp)
  have hBN : B ≤ normalizer (L : Set G) := fun b hb =>
    PartOne.Section8.mem_normalizer_of_ncard_conjSetOf_le_two_of_odd_order hcard (hBM hb)
      (hodd hpp hp2 hBel.isPGroup b hb)
  have hLtop : L ≠ ⊤ :=
    ne_top_of_le_ne_top (uc22p20a_M_ne_top (UC6.dataOfSetup4 hS hU S)) hLM
  have hF := UC6.R869S.two_le_pRank_centralizer_of_pRank_mulAut hLM hpp hp2
    (UC6.R869S.pRank_mulAut_bar2_le_two hOut (hS.kProper.isKGroup L hLtop) hL.2.2 hpp hp2 hp)
    hBM hBN hBel hBc Nat.prime_three (by norm_num) inf_le_right hQ.isPGroup
  have hΓ : CFSG.Open.rankThreeGamma 1 3 (P ⊓ L) ≤ S.M :=
    PartOne.Section7.rankThreeGamma_le_of_two_le_pRank_inf_centralizer hsp h76
      (inf_le_right.trans hLM) hQ.isPGroup hQr hF
  have hP1 : P ≠ ⊥ := by
    rintro rfl
    rw [bot_inf_eq, card_bot] at hQ27
    omega
  exact hnot (CFSG.RankThree.PartOne.isStronglyPEmbedded_of_normalizer_sylow_le
    (uc22p20a_M_ne_top (UC6.dataOfSetup4 hS hU S)) hP hP1
    (hNQ.trans ((CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore le_rfl
      (le_trans (by norm_num) hQr)).trans hΓ))
    fun y hy hyo => CFSG.RankThree.PartOne.centralizer_le_of_rankThreeGamma_le hΓ
      (hall y hy (hyo ▸ pow_orderOf_eq_one y)) hyo)

theorem uc22s213_not_centralizesBar_of_cover (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (hσ : S.InMSigma) (hSE : StronglyEmbeddedFive)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (hout : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
      ∀ s : TauCeti.SporadicName, IsSpor X s → Nat.card (Outer X) ≤ 2)
    {L : Subgroup G} (hL : L ∈ calC S.M)
    (hcov : F08.IsA6Z3 (Bar2 L) ∨ F08.IsA7Z3 (Bar2 L) ∨ F08.IsM22Z3 (Bar2 L))
    (hm3 : CFSG.Open.pRank 3 S.M ≤ 2)
    (hk1 : IsStronglyPEmbedded 3 S.M → CFSG.Open.pRank 3 L ≤ 1) {a : G}
    (hodd : Odd (orderOf a)) (hpr : (orderOf a).Prime)
    (hN : CFSG.Open.pRank S.p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ S.M) ≤ 1) :
    ¬ CentralizesBar a L := by
  intro haL
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp := uc22s213_pRank_le_one_of_centralizesBar (CFSG.Quasithin.A3.subnormal_le hL.1) hodd
    hpr haL S.hp.1.1 S.hp.1.2.1 hN
  have h1 := hk1 (uc22s213_strong_of_cover hS hU S hσ hSE hOut hout hL hcov hm3 hp)
  obtain ⟨Q, hQ⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 L
  obtain ⟨-, -, E, hEQ, hEel, hEc⟩ := uc22s213_card_sylow_of_cover hcov hQ
  have h2 := CFSG.SectionRank.le_pRank (by norm_num) (hEQ.trans hQ.le) hEel hEc
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
