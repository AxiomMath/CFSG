module

public import CFSG.OddTranspositions.HalphaQuotient
public import CFSG.OddTranspositions.PartThree.EightEight.Star
public import CFSG.Timmesfeld.Bridge.Asc72Defs

import CFSG.OddTranspositions.PartThree.EightEight.ConnectedPerfect
import CFSG.Timmesfeld.Bridge.Asc72Central
import CFSG.Timmesfeld.Bridge.Asc72ZMain
import CFSG.CGT.Timmesfeld75.Statements
import CFSG.CGT.Timmesfeld75.Targets
import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ

@[expose] def StarWreath (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D),
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
    ¬ (∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) →
    ¬ Group.IsSolvable (Halpha D hC.alpha) → FaithfulOnBlocks hC.alpha →
    ¬ O4PairData G D →
    derivedSeries (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 1 ≠
      derivedSeries (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 2 →
    ∀ f : ℕ, 2 ≤ f →
      Nonempty ((Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
        L2Wreath f n) →
    ∀ x w y : G, ¬ IsStarTriangle hC x w y

@[expose] def StarAlmostSimple : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D),
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
    ¬ (∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) →
    ¬ Group.IsSolvable (Halpha D hC.alpha) → FaithfulOnBlocks hC.alpha →
    ¬ O4PairData G D →
    derivedSeries (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 1 ≠
      derivedSeries (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 2 →
    AlmostSimpleCase (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))
      (imageClass hC) →
    ∀ x w y : G, ¬ IsStarTriangle hC x w y

section Certs


theorem shape_of_derivedSeries_ne {G : Type} [Group G] [Finite G] {D : Set G}
    (hC : HypothesisC D)
    (hne : derivedSeries (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 1 ≠
      derivedSeries (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 2) :
    (∃ f n : ℕ, 2 ≤ f ∧ (n = 3 ∨ n = 4) ∧
      Nonempty ((Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
        L2Wreath f n)) ∨
    AlmostSimpleCase (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))
      (imageClass hC) := by
  classical
  let X := Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)
  let E : Set X := imageClass hC
  have hHns : ¬ Group.IsSolvable (Halpha D hC.alpha) := by
    intro hHs
    have htop : CFSG.solvableRadical (Halpha D hC.alpha) = ⊤ := by
      have := hHs
      exact top_le_iff.mp (CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical
        (N := ⊤) Subgroup.normal_top inferInstance)
    have hone : ∀ x : X, x = 1 := by
      intro x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      rw [QuotientGroup.eq_one_iff, htop]
      exact Subgroup.mem_top y
    have h1 : derivedSeries X 1 = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [hone x]
      exact Subgroup.one_mem _
    have h2 : derivedSeries X 2 = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [hone x]
      exact Subgroup.one_mem _
    exact hne (by simpa [X] using h1.trans h2.symm)
  have hS : Setup X E := setup_quotient hC hHns
  have hsolv : ∀ N : Subgroup X, N.Normal → Group.IsSolvable N → N = ⊥ := by
    intro N hN hNs
    have hR : CFSG.solvableRadical X = ⊥ := solvableRadical_quotient_H hC
    exact le_bot_iff.mp (hR ▸ CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical
      hN hNs)
  have hdisc : CFSG.Timmesfeld.Connectivity.Disconnected E := by
    by_contra hconn
    exact hne (derivedSeries_one_eq_two_of_not_disconnected hS hconn)
  obtain ⟨H, hHtop, ⟨u, hu, huH⟩, hclosed⟩ :=
    CFSG.Timmesfeld.Bridge.Asc72.exists_subgroup_of_disconnected hS hdisc
  rcases theoremOne X E hS.isClass hS.oddT.1 hS.oddT.2 hS.gen hsolv
      ⟨H, hHtop, ⟨u, hu, huH⟩, hclosed⟩ with hB | ⟨f, n, hf, hn, ⟨φ⟩⟩ | hAS
  · exfalso
    have hcomm : commutator X = ⊤ :=
      CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commutator_eq_top hB
    have h1 : derivedSeries X 1 = ⊤ := by
      rw [derivedSeries_one]
      exact hcomm
    have h2 : derivedSeries X 2 = ⊤ := by
      rw [derivedSeries_succ, h1, ← commutator_def]
      exact hcomm
    exact hne (by simpa [X] using h1.trans h2.symm)
  · exact Or.inl ⟨f, n, hf, hn, ⟨φ⟩⟩
  · exact Or.inr hAS

theorem eightEightStar_of_shapes (h3 : StarWreath 3) (h4 : StarWreath 4)
    (hAS : StarAlmostSimple) : EightEightStar := by
  intro G _ _ D hC hrad hnot hns hF hO4 hne
  rcases shape_of_derivedSeries_ne hC hne with ⟨f, n, hf, hn, ⟨φ⟩⟩ | hA
  · rcases hn with rfl | rfl
    · exact h3 G D hC hrad hnot hns hF hO4 hne f hf ⟨φ⟩
    · exact h4 G D hC hrad hnot hns hF hO4 hne f hf ⟨φ⟩
  · exact hAS G D hC hrad hnot hns hF hO4 hne hA

end Certs

end CFSG.OddTranspositions.PartThree.EightEight
