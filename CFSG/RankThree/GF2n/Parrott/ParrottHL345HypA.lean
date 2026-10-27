module

public import CFSG.RankThree.GF2n.Parrott.ParrottSubgroupE
public import CFSG.RankThree.GF2n.Parrott.ParrottSubgroupEWeak
public import CFSG.RankThree.GF2n.Parrott.ParrottSubgroupEFusion
public import CFSG.RankThree.GF2n.Parrott.ParrottSubgroupEPairFusion
public import CFSG.RankThree.GF2n.Parrott.ParrottTheorem3Inputs
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma34HypA
public import CFSG.RankThree.GF2n.Parrott.CaseIIF1Local
public import CFSG.Holt.PSL2Natural.Defs
public import CFSG.Holt.PermFacts
public import CFSG.Holt.ThreePoint
public import CFSG.LieType.Chevalley.C2E6A5ExteriorCubeModel
public import CFSG.LieType.Chevalley.C2E6ExactRootRestrictions
public import CFSG.LieType.Chevalley.C2E6StandardFixedBorelOrder
public import CFSG.LieType.Chevalley.C2E6StandardLeviFactors
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatSuzuki
public import CFSG.Quasithin.Background.E2NParamStar
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.Quasithin.Vol2.E2TenEight
public import CFSG.RankThree.Holt.Basic
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement


theorem parrott_hL345_hypA
    (hThm1 : ∀ (G : Type) [Group G] [Finite G] (z : G) (h : Tim79a.ParrottHyp z)
      (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN),
      ParrottEqualityBranch (z := z) (D := D) h → H z ⊔ pPrimeCore 2 G = ⊤)
    {K : Type} [Group K] [Finite K] {w : K} (h : Tim79a.ParrottHypA w)
    (hne : ¬ (Subgroup.centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤))
    (hT3w : ∃ K₁ : Subgroup K, K₁.index = 2 ∧ (∀ c : K, (∀ x ∈ K₁, c * x = x * c) → c = 1) ∧
      (∃ (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
        Nonempty (↥K₁ ≃* X)) ∧ K₁ ⊓ H w ≤ ⁅H w, H w⁆) :
    ∃ E K' : Subgroup K,
      E ≤ H w ∧ E ≤ ⁅H w, H w⁆ ⊔ J w ∧ w ∈ E ∧
      Nat.card E = 2 ^ 9 ∧ Nat.card ↥(E ⊓ J w) = 2 ^ 5 ∧
      E = H w ⊓ Subgroup.centralizer ((E ⊓ J w : Subgroup K) : Set K) ∧
      E.relIndex (normalizer (E : Set K) ⊓ H w) = 1920 ∧
      (∀ x ∈ E, x ∈ Subgroup.closure
        {y : K | ∃ n ∈ normalizer (E : Set K), y = n * w * n⁻¹}) ∧
      E ≤ K' ∧ K'.relIndex (normalizer (E : Set K)) = 2 ∧
      normalizer (E : Set K) ⊓ ⁅H w, H w⁆ ≤ K' ∧ ¬ (normalizer (E : Set K) ⊓ H w ≤ K') ∧
      ((E.subgroupOf K').Normal ∧ Nat.card (↥K' ⧸ E.subgroupOf K') = 20160 ∧
         ∀ L : Subgroup K, E ≤ L → L ≤ K' → L.relIndex K' ≠ 2) ∧
      ∃ t j₀ : K, t ∈ E ∧ t ∉ J w ∧ orderOf t = 2 ∧ IsConj w t ∧
        j₀ ∈ J w ∧ j₀ ∉ Subgroup.zpowers w ∧ IsConj (t * w) j₀ := by
  obtain ⟨D⟩ := h.quotient
  have hIII := not_equalityBranch_of_theorem1_A hThm1 h D hne
  have hJ0 := not_isConj_z_of_mem_J_A h D hIII
  have hJ : ∀ j ∈ J w, j ∉ Subgroup.zpowers w → ¬ IsConj w j := fun j hj hjw hc =>
    hJ0 j hj ((IsConj.orderOf_eq hc).symm.trans (orderOf_z_A h)) hjw hc
  obtain ⟨E, hEH, hEHJ, hwE, hcard, hcardJ, hECE, hrel, -, hJN, hgen1, hJE, hM3, hmeet, horb⟩ :=
    exists_parrottE_hypA h D hIII
  have hE2 := isElemAbelian_parrottE_of_hT3 h hM3 hT3w
  obtain ⟨K₁, hK₁i, -, -, hK₁H⟩ := id hT3w
  have hF2 := parrott_F2_of_hT3 h D hIII ⟨K₁, hK₁i, hK₁H⟩
  have hweak := hweak_of_isElemAbelian h D hIII hEH hEHJ hwE hE2 hcard hcardJ hECE hrel
  have hy := exists_isConj_mem_parrottE hne (orderOf_z_A h) hJ hF2 (hmeet hE2)
  have hfus := hfus_of_isConj_mem hEH hE2 hweak hy
  have hgen := hgen_of_hfus (orderOf_z_A h) hEH hwE hJ hgen1 hfus
  obtain ⟨K', hEK', hKi, hKM, hKq, hKQ⟩ :=
    hL345_Kprime_of_lemma34 h D hIII hEH hEHJ hwE hcard hcardJ hECE hrel hgen hweak hJ hfus
  obtain ⟨t, j₀, htE, htJ, ht2, htc, hj₀, hj₀w, hj₀c⟩ :=
    exists_t_j0_of_orbit (orderOf_z_A h) hEH hJ hJN hcard hrel hJE horb hEK' hKi hKQ hfus
  exact ⟨E, K', hEH, hEHJ, hwE, hcard, hcardJ, hECE, hrel, hgen, hEK', hKi, hKM, hKq, hKQ,
    t, j₀, htE, htJ, ht2, htc, hj₀, hj₀w, hj₀c⟩

end CFSG.RankThree.GF2n.Parrott
