module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76Basic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R77EqThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OutPRankBound
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneSixThirtyEight
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.RankFourTheoremC.PPointSetup
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.GroupTheory.OddPGroupNoncyclicChar
import CFSG.Goldschmidt.Steps.Sec82PGroup
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive StronglyEmbeddedThree)

variable {G : Type} [Group G] [Finite G]

theorem pRank_le_one_of_gammaFree (hS : Standing G) (S : Setup G)
    (hns : ¬ Group.IsSolvable ↥(dataOfSetup hS S).M) {L : Subgroup G} (hLM : L ≤ S.M)
    (hfree : ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ Q : Subgroup G, Q ≤ L → IsPGroup q Q →
      2 ≤ CFSG.Open.pRank q Q → ¬ rankThreeGamma 1 q Q ≤ S.M)
    {p : ℕ} (hp : p ∈ sigmaOf S.M) : CFSG.Open.pRank p L ≤ 1 := by
  have hσ := (dataOfSetup hS S).sig_prime p hp
  have : Fact p.Prime := ⟨hσ.1⟩
  by_contra h
  obtain ⟨E, hEL, hEel, hEc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank (M := L) hσ.1
    (k := 2) (by omega)
  exact hfree p hσ.1 hσ.2 E hEL hEel.isPGroup (UC6S846.le_pRank' hσ.1 le_rfl hEel hEc)
    (PartOne.Section7.rankThreeGamma_self_le
      (UC6S846.sp_of_mem_sig (UC6S846.sigmaStd_dataOfSetup hS S) hns hp) (hEL.trans hLM)
      hEel.isPGroup)

theorem exists_gamma_le_of_not_dvd (hSE : StronglyEmbeddedFive) (hSE3 : StronglyEmbeddedThree)
    (hS : Standing G) (hUC : rankThreeUC G) (S : Setup G)
    (hns : ¬ Group.IsSolvable ↥(dataOfSetup hS S).M) {L : Subgroup G} (hLM : L ≤ S.M)
    (hML : S.M ≤ normalizer (L : Set G)) (hthin : ¬ F08.Thin8 L) {p : ℕ}
    (hp : p ∈ sigmaOf S.M) (hLp : ¬ p ∣ Nat.card L) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ ∃ Q : Subgroup G, Q ≤ L ∧ IsPGroup q Q ∧
      2 ≤ CFSG.Open.pRank q Q ∧ rankThreeGamma 1 q Q ≤ S.M := by
  have hσ := (dataOfSetup hS S).sig_prime p hp
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  obtain ⟨B, hBM, hBel, hBc⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hσ.1 (hSg.three_le p hp)
  obtain ⟨q, hq, hq2, h1q⟩ : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 1 < CFSG.Open.pRank q L := by
    by_contra h
    exact hthin fun q hq hq2 => not_lt.1 fun hlt => h ⟨q, hq, hq2, hlt⟩
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨R₀, hR₀⟩ := CFSG.GroupTheory.exists_sylow_le_normalizer_of_isPGroup hσ.1 hq
    hBel.isPGroup (hBM.trans hML) hLp
  have hRp : IsPGroup q ((R₀ : Subgroup ↥L).map L.subtype) := R₀.isPGroup'.map _
  have hRr : CFSG.Open.pRank q ((R₀ : Subgroup ↥L).map L.subtype) = CFSG.Open.pRank q L :=
    CFSG.LocalAnalysis.RankFourTheoremC.pRank_eq_of_isSylowOf hq ⟨R₀, rfl⟩
  have hRnc : ¬ IsCyclic ((R₀ : Subgroup ↥L).map L.subtype) :=
    CFSG.Goldschmidt.Sec82.not_isCyclic_of_two_le_pRank hq (by rw [hRr]; omega)
  obtain ⟨D, hDR, -, hDnc, hDexp, hDcl, hND⟩ :=
    CFSG.GroupTheory.exists_noncyclic_exponent_classTwo_normalized hq2 hRp hRnc
  have hDL : D ≤ L := hDR.trans (Subgroup.map_subtype_le _)
  have hDp : IsPGroup q D := hRp.to_le hDR
  refine ⟨q, hq, hq2, D, hDL, hDp, UC6.two_le_pRank_of_not_isCyclic hq hq2 hDp hDnc, ?_⟩
  by_cases hqσ : q ∈ sigmaOf S.M
  · exact PartOne.Section7.rankThreeGamma_self_le (UC6S846.sp_of_mem_sig hSg hns hqσ)
      (hDL.trans hLM) hDp
  · have h3 : 3 ≤ CFSG.Open.pRank p ((dataOfSetup hS S).M ⊓ normalizer (D : Set G)) :=
      UC6S846.le_pRank' hσ.1 (le_inf hBM (hR₀.trans hND)) hBel hBc
    have hle : CFSG.Open.pRank p (dataOfSetup hS S).M ≤ 3 := by
      have := CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank p hσ.1 hσ.2
        (dataOfSetup hS S).M S.witness.maxLocal.1
      rwa [hS.rank] at this
    have hmono : CFSG.Open.pRank p ((dataOfSetup hS S).M ⊓ normalizer (D : Set G)) ≤
        CFSG.Open.pRank p (dataOfSetup hS S).M :=
      CFSG.SectionRank.pRank_mono hσ.1.one_lt inf_le_left
    exact r77Eq_dataOfSetup hSE hSE3 hS hUC S (UC6S846.sig_subset_sig1 hSg hns) p hp hσ.2
      (UC6S846.sp_of_mem_sig hSg hns hp) q hq hq2 hqσ D (hDL.trans hLM) hDp hDnc hDexp hDcl
      (by omega) (by omega)

theorem exists_gamma_le_of_centralizing (hSE : StronglyEmbeddedFive)
    (hSE3 : StronglyEmbeddedThree) (hS : Standing G) (S : Setup G)
    (hns : ¬ Group.IsSolvable ↥(dataOfSetup hS S).M) {L : Subgroup G} (hLM : L ≤ S.M)
    (hML : S.M ≤ normalizer (L : Set G)) (hthin : ¬ F08.Thin8 L) {p : ℕ}
    (hp : p ∈ sigmaOf S.M) {A : Subgroup G} (hAM : A ≤ S.M) (hAel : IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) (hAL : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ pCoreOf 2 L) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ ∃ Q : Subgroup G, Q ≤ L ∧ IsPGroup q Q ∧
      2 ≤ CFSG.Open.pRank q Q ∧ rankThreeGamma 1 q Q ≤ S.M := by
  have hσ := (dataOfSetup hS S).sig_prime p hp
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  obtain ⟨q, hq, hq2, h1q⟩ : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 1 < CFSG.Open.pRank q L := by
    by_contra h
    exact hthin fun q hq hq2 => not_lt.1 fun hlt => h ⟨q, hq, hq2, hlt⟩
  obtain ⟨E, hEL, hEel, hEc⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank (M := L) hq (k := 2) (by omega)
  have hNO := UC6S846.normalizer_le_normalizer_pCoreOf L
  obtain ⟨A', hA'C, hA'le, ⟨eA⟩⟩ := UC6S846.exists_centralizing_copy hq hq2 hσ.1 hσ.2
    (pCoreOf 2 L) A E (UC6S846.isPGroup_pCoreOf L) ((hAM.trans hML).trans hNO)
    ((hEL.trans Subgroup.le_normalizer).trans hNO) hAel.isPGroup hEel.isPGroup
    (fun e he a ha => by
      have h3 : e * a * e⁻¹ * a⁻¹ = (a * e * a⁻¹ * e⁻¹)⁻¹ := by group
      rw [h3]
      exact inv_mem (hAL a ha e (hEL he)))
  have hA'M : A' ≤ S.M := hA'le.trans (sup_le hAM ((Subgroup.map_subtype_le _).trans hLM))
  have hA'el : IsElemAbelian p A' := UC6S846.isElemAbelian_of_mulEquiv eA hAel
  have hA'c : Nat.card A' = p ^ 2 := by rw [Nat.card_congr eA.toEquiv, hAc]
  have h2 : 2 ≤ CFSG.Open.pRank p ((dataOfSetup hS S).M ⊓ centralizer (E : Set G)) :=
    UC6S846.le_pRank' hσ.1 (le_inf hA'M hA'C) hA'el hA'c
  refine ⟨q, hq, hq2, E, hEL, hEel.isPGroup, UC6S846.le_pRank' hq le_rfl hEel hEc, ?_⟩
  refine r76Sig_dataOfSetup hSE hSE3 hS S p hp hσ.2 (UC6S846.sp_of_mem_sig hSg hns hp) q hq E
    (hEL.trans hLM) hEel hEc (by omega) fun Y hYE _ => ?_
  refine lt_of_lt_of_le (by norm_num) (h2.trans (CFSG.SectionRank.pRank_mono hσ.1.one_lt ?_))
  exact inf_le_inf_left _ ((Subgroup.centralizer_le hYE).trans
    (Subgroup.centralizer_le_normalizer _))

theorem exists_centralizing_of_cyclic_outer (hS : Standing G) (S : Setup G) {L : Subgroup G}
    (hLM : L ≤ S.M) (hML : S.M ≤ normalizer (L : Set G)) (hZ : center (Bar2 L) = ⊥)
    (hOut : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 L)))
    {p : ℕ} (hp : p ∈ sigmaOf S.M) (h1 : CFSG.Open.pRank p L ≤ 1) :
    ∃ A : Subgroup G, A ≤ S.M ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧
      ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  have hσ := (dataOfSetup hS S).sig_prime p hp
  have : Fact p.Prime := ⟨hσ.1⟩
  have hX1 : CFSG.Open.pRank p (⊤ : Subgroup (Bar2 L)) ≤ 1 := by
    have h3 : ¬ p ∣ Nat.card (CFSG.pCore 2 ↥L) :=
      CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := p)
        (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) hσ.1 hσ.2
    rw [CFSG.SectionRank.pRank_quotient_eq (p := p) (N := CFSG.pCore 2 ↥L) h3,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
    exact h1
  have hb := PartTwo.pRank_le_pRank_bar2_add_pRank_centOverO2 hLM hML hZ hOut hσ.1 hσ.2
    (r6_38_dataOfSetup hS S p hσ.1 hσ.2 (Or.inl hp))
  have h3 : 3 ≤ CFSG.Open.pRank p S.M := (UC6S846.sigmaStd_dataOfSetup hS S).three_le p hp
  obtain ⟨A, hA, hAel, hAc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank
    (M := F08.CentOverO2 S.M L) hσ.1 (k := 2) (by omega)
  exact ⟨A, fun a ha => (PartTwo.mem_centOverO2_iff.1 (hA ha)).1, hAel, hAc,
    fun a ha l hl => (PartTwo.mem_centOverO2_iff.1 (hA ha)).2 l hl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
