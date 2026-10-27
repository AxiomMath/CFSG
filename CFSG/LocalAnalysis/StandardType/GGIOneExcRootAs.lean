module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProper

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGEndNodeRootAs (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A As : Subgroup (MulAut L'), IsElemAbelian p A → A < As → IsElemAbelian p As →
      Nat.card As ≤ p * Nat.card A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGNormTwoR ψ A → GGNoTwoBetween A As →
        ∃ a, GGIsEndNode A a ∧ GGNonSmallRule p A a ∧
          ∃ U : Subgroup L', U ≤ LargeEvenLayer (ggFix a) ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
            ∀ a' ∈ A, ∀ u ∈ U, a' u ∈ U

@[expose] def GGEndNodeRootAsInn (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A As : Subgroup (MulAut L'), IsElemAbelian p A → A < As → IsElemAbelian p As →
      Nat.card As ≤ p * Nat.card A →
      (∀ a ∈ As, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGNormTwoR ψ A → GGNoTwoBetween A As →
        ∃ a, GGIsEndNode A a ∧ GGNonSmallRule p A a ∧
          ∃ U : Subgroup L', U ≤ LargeEvenLayer (ggFix a) ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
            ∀ a' ∈ A, ∀ u ∈ U, a' u ∈ U

theorem ggIE_endNodeIOne_of_rootAs_delta {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hroot : GGEndNodeRootAs p r R I) (hdel : GGEndNodeIOneDelta p r R I) :
    GGEndNodeIOne p r R I := by
  intro L' _ _ ψ hψ hker hperf A As hA hAAs hAs hcard hAI hr h3 hcase hnone
  rcases hcase with hα | hδ
  · obtain ⟨a, ⟨haA, ha1, hcomp, hcent⟩, hrule, U, hUJ, hU1, hU2, hUA⟩ :=
      hroot L' ψ hψ hker hperf A As hA hAAs hAs hcard hAI hr h3 hα hnone
    exact ⟨a, ⟨haA, ha1, hcomp, hcent⟩,
      ggCentEnd_of_root haA hcent hAAs.le hnone hUJ hU1 hU2 hUA, hrule⟩
  · exact hdel L' ψ hψ hker hperf A As hA hAAs hAs hcard hAI hr h3 hδ hnone

theorem ggIE_endNodeIOne_of_rootAsInn_cases {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hroot : GGEndNodeRootAsInn p r R I) (hdel : GGEndNodeIOneDelta p r R I)
    (hF : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      ∀ A As : Subgroup (MulAut L'), IsElemAbelian p A → A < As → IsElemAbelian p As →
        Nat.card As ≤ p * Nat.card A →
        (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
        p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGNormTwoR ψ A → GGNoTwoBetween A As →
          ∀ a ∈ As, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) :
    GGEndNodeIOne p r R I := by
  intro L' _ _ ψ hψ hker hperf A As hA hAAs hAs hcard hAI hr h3 hcase hnone
  rcases hcase with hα | hδ
  · have hInn := hF L' ψ hψ hker hperf A As hA hAAs hAs hcard hAI hr h3 hα hnone
    obtain ⟨a, ⟨haA, ha1, hcomp, hcent⟩, hrule, U, hUJ, hU1, hU2, hUA⟩ :=
      hroot L' ψ hψ hker hperf A As hA hAAs hAs hcard hInn hr h3 hα hnone
    exact ⟨a, ⟨haA, ha1, hcomp, hcent⟩,
      ggCentEnd_of_root haA hcent hAAs.le hnone hUJ hU1 hU2 hUA, hrule⟩
  · exact hdel L' ψ hψ hker hperf A As hA hAAs hAs hcard hAI hr h3 hδ hnone

end CFSG.StandardType
