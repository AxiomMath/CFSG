module

public import CFSG.RankThree.GF2n.Parrott.A1Lemma21b
public import CFSG.RankThree.GF2n.Parrott.A1Lemma22
public import CFSG.RankThree.GF2n.Parrott.A1Theorem1
public import CFSG.RankThree.GF2n.Parrott.A1AschbacherSmith
public import CFSG.RankThree.GF2n.Parrott.Proposition6IndexTwo
public import CFSG.GF2Type.AschbacherFSmith1977Holds
import all CFSG.RankThree.GF2n.Parrott.A1LocalData
public import CFSG.GF2Type.Aschbacher1976
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.Holt.PermFacts
public import CFSG.LargeExtraspecial.AS62EnumInputs
public import CFSG.LargeExtraspecial.S14Main
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11AutQTCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11SingleXClass
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OFactsF0Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.Quasithin.Background.E2NParamStar
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.Quasithin.Vol2.E2TenEight
public import Certificates.Certificate19780

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)

namespace Remarks

variable {G : Type} [Group G] [Finite G] {z : G}

theorem lemma22_weakly_closed
    (hJ : IsExtraspecial2 (J z)) (hcard : Nat.card (J z) = 2 ^ 9)
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hrange : φ.range = QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)
    {σ₁ σ₂ : ↥(H z)} (hσ₁ : φ σ₁ = ⟨sigma1, sigma1_mem_A⟩) (hσ₂ : φ σ₂ = ⟨sigma2, sigma2_mem_A⟩)
    (h3₂ : orderOf σ₂ = 3) (hc : Commute σ₁ σ₂) (hne : CJ z (σ₁ : G) ≠ CJ z (σ₂ : G))
    (hy : ∃ y : ↥(H z), orderOf y = 9 ∧ y ^ 3 = σ₁) (hu : ∃ u' : ↥(H z), u' * σ₁ * u'⁻¹ = σ₂)
    (hP6I : ∀ (G : Type) [Group G] [Finite G] (z : G), orderOf z = 2 →
      [_hO23 : ((CFSG.OddStandard.SmallF3.HarrisU33.twoThreeCore
        (Subgroup.centralizer ({z} : Set G))).subgroupOf
        (Subgroup.centralizer ({z} : Set G))).Normal] →
      (∃ L1 L2 : Subgroup G,
        L1 ≤ Subgroup.centralizer ({z} : Set G) ∧ L2 ≤ Subgroup.centralizer ({z} : Set G) ∧
        Nonempty (↥L1 ≃* CFSG.OddStandard.Solomon75.SL23) ∧
        Nonempty (↥L2 ≃* CFSG.OddStandard.Solomon75.SL23) ∧
        (∀ x ∈ L1, ∀ y ∈ L2, x * y = y * x) ∧
        L1 ⊓ L2 = (Subgroup.center L1).map L1.subtype ∧
        L1 ⊓ L2 = (Subgroup.center L2).map L2.subtype ∧
        L1 ⊔ L2 = CFSG.OddStandard.SmallF3.HarrisU33.twoThreeCore
          (Subgroup.centralizer ({z} : Set G)) ∧
        ¬ (L1.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal ∧
        ¬ (L2.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal ∧
        Nat.card (↥(Subgroup.centralizer ({z} : Set G)) ⧸
            (CFSG.OddStandard.SmallF3.HarrisU33.twoThreeCore
              (Subgroup.centralizer ({z} : Set G))).subgroupOf
              (Subgroup.centralizer ({z} : Set G))) = 2) →
      Subgroup.centralizer ({z} : Set G) ⊔ pPrimeCore 2 G = ⊤ ∨
        CFSG.Blueprint.LieModel G .PSp 2 3 1) :
    ∀ g : G, g⁻¹ * z * g ∈ J z → g⁻¹ * z * g = z :=
  lemma22_weakly_closed_of_dichotomy hJ hcard hcomm hCHJ φ hker hrange hσ₁ hσ₂ h3₂ hc hne hy hu
    (lemma21_dichotomy hJ hcard hcomm hCHJ φ hker hrange hσ₁ hσ₂ h3₂ hc hne hy hu hP6I)

end Remarks

theorem parrott_theoremA_one_of_prop6IndexTwo
    (hP6I : ∀ (G : Type) [Group G] [Finite G] (z : G), orderOf z = 2 →
      [_hO23 : ((CFSG.OddStandard.SmallF3.HarrisU33.twoThreeCore
        (Subgroup.centralizer ({z} : Set G))).subgroupOf
        (Subgroup.centralizer ({z} : Set G))).Normal] →
      (∃ L1 L2 : Subgroup G,
        L1 ≤ Subgroup.centralizer ({z} : Set G) ∧ L2 ≤ Subgroup.centralizer ({z} : Set G) ∧
        Nonempty (↥L1 ≃* CFSG.OddStandard.Solomon75.SL23) ∧
        Nonempty (↥L2 ≃* CFSG.OddStandard.Solomon75.SL23) ∧
        (∀ x ∈ L1, ∀ y ∈ L2, x * y = y * x) ∧
        L1 ⊓ L2 = (Subgroup.center L1).map L1.subtype ∧
        L1 ⊓ L2 = (Subgroup.center L2).map L2.subtype ∧
        L1 ⊔ L2 = CFSG.OddStandard.SmallF3.HarrisU33.twoThreeCore
          (Subgroup.centralizer ({z} : Set G)) ∧
        ¬ (L1.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal ∧
        ¬ (L2.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal ∧
        Nat.card (↥(Subgroup.centralizer ({z} : Set G)) ⧸
            (CFSG.OddStandard.SmallF3.HarrisU33.twoThreeCore
              (Subgroup.centralizer ({z} : Set G))).subgroupOf
              (Subgroup.centralizer ({z} : Set G))) = 2) →
      Subgroup.centralizer ({z} : Set G) ⊔ pPrimeCore 2 G = ⊤ ∨
        CFSG.Blueprint.LieModel G .PSp 2 3 1)
    (G : Type) [Group G] [Finite G] (z : G) (h : Tim79a.ParrottHypA1 z) :
    Subgroup.centralizer ({z} : Set G) ⊔ pPrimeCore 2 G = ⊤ ∨
      CFSG.Blueprint.LieModel G .PSU 6 2 1 := by
  by_cases hsup : Subgroup.centralizer ({z} : Set G) ⊔ pPrimeCore 2 G = ⊤
  · exact Or.inl hsup
  refine Or.inr ?_
  set D := quotientDataA1 h with hD
  by_cases heq : CJ z ((s1HP D : ↥(H z)) : G) = CJ z ((s2HP D : ↥(H z)) : G)
  · exact absurd (parrott_theorem1_A1 h heq) hsup
  have hy : ∃ y : ↥(H z), orderOf y = 9 ∧ y ^ 3 = s1HP D :=
    ⟨nineRootHP D, orderOf_nineRootHP D, rfl⟩
  have hu : ∃ u' : ↥(H z), u' * s1HP D * u'⁻¹ = s2HP D := ⟨uHP D, rfl⟩
  have hwc := Remarks.lemma22_weakly_closed h.extraspecial h.card_J h.commutator h.centralizer_le
    (qHPA D) (ker_qHPA D) (range_qHPA D) (qHPA_s1HP D) (qHPA_s2HP D) (orderOf_s2HP D)
    (commute_s1HP_s2HP D) heq hy hu hP6I
  have hJH := Remarks.commutator_J_H_eq_J h.extraspecial h.card_J h.commutator h.centralizer_le
    (orderOf_s2HP D) (commute_s1HP_s2HP D) heq hy hu
  exact lieModel_psu_six_of_aschbacherFSmith_A1 GF2Type.aschbacherFSmith1977Statement_holds h hsup
    hwc hJH

theorem parrott_theoremA_one_cited
    (hJ14 : ∀ (X : Type) [Group X], CFSG.Blueprint.LieModel X .PSp 2 3 1 → ∀ x : X,
      orderOf x = 2 →
      (∃ S : Sylow 2 X, x ∈ (S : Subgroup X) ∧ ∀ s ∈ (S : Subgroup X), x * s = s * x) →
      ∀ (G : Type) [Group G] [Finite G], (∀ N : Subgroup G, N.index ≠ 2) →
        ∀ j : G, orderOf j = 2 →
          Nonempty (Subgroup.centralizer ({j} : Set G) ≃* Subgroup.centralizer ({x} : Set X)) →
            CFSG.Blueprint.LieModel G .PSp 2 3 1) :
    ∀ (K : Type) [Group K] [Finite K] (w : K), Tim79a.ParrottHypA1 w →
      Subgroup.centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤ ∨
        CFSG.Blueprint.LieModel K .PSU 6 2 1 :=
  fun K _ _ w h => parrott_theoremA_one_of_prop6IndexTwo (parrott_proposition6_indexTwo hJ14) K w h

end CFSG.RankThree.GF2n.Parrott
