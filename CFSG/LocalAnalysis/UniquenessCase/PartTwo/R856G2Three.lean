module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R856CoverThree
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xBR865Types
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBarCyclic
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBarKernel
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight62CenterOfNormal
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight67Cases23
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight5xAChoiceY
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCNoncyc
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56SpineChainChoiceY

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
open CFSG.LocalAnalysis.UniquenessCase.UC22.R856NormalFour

variable {G : Type} [Group G] [Finite G]


theorem false_of_normal_g2_of_outer_prime_dataOfSetup
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G)
    {L Q P X : Subgroup G} (hX : ChoiceX (dataOfSetup hS S) L Q P X)
    (hML : S.M ≤ normalizer (L : Set G)) {p f : ℕ} (hp3 : p ≠ 3)
    (hmodel : CFSG.Blueprint.LieModel (Bar2 L) .G2 0 p f)
    (hOut : ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 L))) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc := hX.cex
  have hZ := center_eq_bot_of_lieModel_g2 hmodel
  have hPNL : P ≤ normalizer (L : Set G) := hc.sylowP.le.trans hML
  have hQeq : Q = P ⊓ L :=
    (hc.sylowQ.eq_of_le (le_inf hc.le hc.sylowQ.le) inf_le_right
      (hc.sylowP.isPGroup.to_le inf_le_left)).symm
  have hQn : (Q.subgroupOf P).Normal :=
    normal_subgroupOf_of_isSylowOf_of_le_normalizer hc.sylowQ hc.le hc.sylowP.isPGroup hPNL
  have hPQ : P ≤ Q ⊔ centralizerBar P L :=
    le_sup_centralizerBar_of_inner hc.le hc.sylowQ.le hQeq hQn hc.sylowQ
      hc.sylowP.isPGroup hPNL le_rfl (inner_action_of_not_three_dvd_outer hOut hc.sylowP.isPGroup hPNL)
  have hcap : Q ⊓ centralizerBar P L = ⊥ :=
    inf_centralizerBar_eq_bot_of_ker hc.sylowQ.le hc.inf_pCore_eq_bot
      (inf_centralizerBar_le_pCore_of_center_bar2 hZ)
  have hcomm : ∀ q ∈ Q, ∀ c ∈ centralizerBar P L, q * c = c * q := fun q hq c hcc =>
    commute_of_mem_centralizerBar Nat.prime_three (by norm_num) hc.sylowP.isPGroup
      hc.sylowQ.le hc.le hq hcc
  have hQr : CFSG.Open.pRank 3 Q = 2 := hc.pRank_sylowQ_eq_two
  have hPr : CFSG.Open.pRank 3 P ≤ 3 := hc.pRank_sylowP_le_three
    (UC6S846.sigmaStd_dataOfSetup hS S)
  have hCr : CFSG.Open.pRank 3 (centralizerBar P L) ≤ 1 := by
    have ha := CFSG.LocalAnalysis.RankThreeUC.S15.pRank_add_le_pRank_sup_of_commute
      Nat.prime_three hcomm hcap
    have hr := (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt
      (sup_le hc.le (centralizerBar_le P L))).trans hPr
    omega
  have hCcyc : IsCyclic (centralizerBar P L) :=
    CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.isCyclic_of_pRank_le_one
      Nat.prime_three (by norm_num) (hc.sylowP.isPGroup.to_le (centralizerBar_le P L))
      (by rwa [CFSG.SectionRank.pRank_coe_eq_openPRank])
  have hm := hmodel.chevalleyExceptionalModel (by decide)
  have hp := hm.1.1
  have hpf : p = 2 → 2 ≤ f := by
    intro heq
    have hq := hm.1.2.2.2
    rw [heq] at hq
    by_contra hf
    have ht := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : f ≤ 1)
    norm_num at ht
    omega
  have hnc := sylowNoncyclicOfG2_holds (Bar2 L) p f hp hp3 hpf hmodel
  have hQZ : Nat.card (center Q) = 3 := by
    have h3 := card_center_map_sylow_eq_three_of_g2 hc.sylowQ hp hp3 hpf hmodel
    rwa [Subgroup.card_map_of_injective Q.subtype_injective] at h3
  have hQnotcomm : ¬ IsMulCommutative Q := by
    intro hcommQ
    have : IsMulCommutative Q := hcommQ
    have hcard : Nat.card Q = 3 := by simpa only [Subgroup.center_eq_top, Subgroup.card_top] using hQZ
    have hcyc : IsCyclic Q := isCyclic_of_prime_card hcard
    exact hc.not_isCyclic_sylowQ hcyc
  have hcard : 3 ^ 3 ∣ Nat.card Q := by
    obtain ⟨n, hn⟩ := hc.sylowQ.isPGroup.exists_card_eq
    have hge := CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.pow_three_le_card_of_nonabelian
      hc.sylowQ.isPGroup hQnotcomm
    rw [hn] at hge
    have hn3 : 3 ≤ n := by
      by_contra hn3
      interval_cases n <;> norm_num at hge
    rw [hn]
    exact pow_dvd_pow 3 hn3
  obtain ⟨X', Y, hY⟩ := exists_choiceY_of_choiceX (dataOfSetup hS S) hX
  have hYQ := ChoiceY.inf_eq_bot (r862_dataOfSetup hS hUC hC S) hY
  have hcyc : IsCyclic Y := isCyclic_of_le_of_sup_cyclic_of_inf_eq_bot hc.le
    (centralizerBar_le P L) hY.YP (le_antisymm (sup_le hc.le (centralizerBar_le P L)) hPQ)
    hQn hCcyc hYQ
  exact false_of_choiceY_of_noncyclic_centralizers UCK.k35w_holds stronglyEmbeddedCentralFree_holds
    hY hML hZ hPQ hcyc hYQ (fun y hy => not_isCyclic_inf_centralizer_of_bar hc.sylowQ
      hc.le hc.sylowP.isPGroup hPNL hOut hnc hy) hcard

theorem false_of_normal_g2_of_field_degree_dataOfSetup
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G)
    {L Q P X : Subgroup G} (hX : ChoiceX (dataOfSetup hS S) L Q P X)
    (hML : S.M ≤ normalizer (L : Set G)) {p f : ℕ} (hp3 : p ≠ 3)
    (hmodel : CFSG.Blueprint.LieModel (Bar2 L) .G2 0 p f) (hf3 : ¬ 3 ∣ f) : False := by
  have hc := hmodel.chevalleyExceptionalModel (by decide)
  obtain ⟨K, _, _, hKcard, ⟨e⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hc.2
  have hq : 3 ≤ Nat.card K := hKcard ▸ hc.1.2.2.2
  have hOut : ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 L)) := by
    have hbound := card_outer_adjointGroup_G2_dvd hc.1.1 hc.1.2.1 hKcard hq
    rw [CFSG.SignalizerFunctorTheorem.CatalogBridge.card_outer_eq_of_mulEquiv e]
    exact fun h => (Nat.prime_three.not_dvd_mul (by norm_num) hf3) (h.trans hbound)
  exact false_of_normal_g2_of_outer_prime_dataOfSetup hS hUC hC S hX hML hp3 hmodel hOut



end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
