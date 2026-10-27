module

public import CFSG.RankThree.GF2n.Parrott.CaseIIHv
public import CFSG.RankThree.GF2n.Parrott.CaseIITheoremAFromA1
public import CFSG.Holt.PSL2Natural.Defs
public import CFSG.Holt.PermFacts
public import CFSG.Holt.ThreePoint
public import CFSG.LocalAnalysis.EvenSmallLie.Children
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatSuzuki
public import CFSG.Quasithin.Background.E2NParamStar
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.Quasithin.Vol2.E2TenEight
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma45
public import CFSG.RankThree.Holt.Basic
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup

variable {G : Type} [Group G] [Finite G] {z : G}

theorem parrott_theorem3_caseII
    (hA1 : ∀ (K : Type) [Group K] [Finite K] (w : K), Tim79a.ParrottHypA1 w →
      centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤ ∨ CFSG.Blueprint.LieModel K .PSU 6 2 1)
    (hThm1 : ∀ (G : Type) [Group G] [Finite G] (z : G) (h : Tim79a.ParrottHyp z)
      (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN),
      ParrottEqualityBranch (z := z) (D := D) h → H z ⊔ pPrimeCore 2 G = ⊤)
    (h : Tim79a.ParrottHypA z) :
    centralizer ({z} : Set G) ⊔ pPrimeCore 2 G = ⊤ ∨
      ∃ G₁ : Subgroup G, G₁.index = 2 ∧ (∀ c : G, (∀ x ∈ G₁, c * x = x * c) → c = 1) ∧
        (∃ (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
          Nonempty (↥G₁ ≃* X)) ∧
        G₁ ⊓ H z ≤ ⁅H z, H z⁆ := by
  obtain ⟨D⟩ := h.quotient
  by_cases heq : ∃ σ₂ : ↥(H z), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂
  · exact Or.inl (parrott_theorem1_caseII hThm1 h D heq)
  · obtain ⟨G₀, hG₀, hidx, hzG₀, hHG₀⟩ := parrott_lemma36_caseII h D heq
    exact parrott_theoremA_two_of_index_two hA1 h hG₀ hidx hzG₀
      (J_le_commutator_of_not_equalityBranch_A h D heq)
      (relIndex_commutator_of_not_equalityBranch_A h D heq) hHG₀

theorem parrott_theorem3_export
    (hA1 : ∀ (K : Type) [Group K] [Finite K] (w : K), Tim79a.ParrottHypA1 w →
      centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤ ∨ CFSG.Blueprint.LieModel K .PSU 6 2 1)
    (hThm1 : ∀ (G : Type) [Group G] [Finite G] (z : G) (h : Tim79a.ParrottHyp z)
      (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN),
      ParrottEqualityBranch (z := z) (D := D) h → H z ⊔ pPrimeCore 2 G = ⊤) :
    ∀ (K : Type) [Group K] [Finite K] (w : K), Tim79a.ParrottHypA w →
      ¬ (Subgroup.centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤) →
      ∃ K₁ : Subgroup K, K₁.index = 2 ∧ (∀ c : K, (∀ x ∈ K₁, c * x = x * c) → c = 1) ∧
        (∃ (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
          Nonempty (↥K₁ ≃* X)) ∧
        K₁ ⊓ H w ≤ ⁅H w, H w⁆ :=
  fun _ _ _ _ h hne => (parrott_theorem3_caseII hA1 hThm1 h).resolve_left hne

end CFSG.RankThree.GF2n.Parrott
