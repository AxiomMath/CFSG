module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultRows

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix

theorem commutator_commutator_fiveReflectionGroup {k : ℕ} (hk : 4 ≤ k) (ε π : Bool) :
    ⁅commutator ↥(fiveReflectionGroup k ε π), commutator ↥(fiveReflectionGroup k ε π)⁆ =
      commutator ↥(fiveReflectionGroup k ε π) := by
  have h1 : ⁅fiveReflectionGroup k ε π, fiveReflectionGroup k ε π⁆ = fiveOmega k ε :=
    commutator_fiveReflectionGroup_eq_fiveOmega hk ε π
  have h2 : (commutator ↥(fiveReflectionGroup k ε π)).map
      (fiveReflectionGroup k ε π).subtype = fiveOmega k ε := by
    rw [← h1]
    exact Subgroup.map_subtype_commutator _
  apply Subgroup.map_injective (fiveReflectionGroup k ε π).subtype_injective
  rw [Subgroup.map_commutator, h2, commutator_fiveOmega hk ε]

theorem fiveInvolutionLiftCover_fiveProjective {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    (hminus : FiveMinusInputs) (hsix : FiveMinusSixInputs) : FiveInvolutionLiftCover k ε π := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' k
  · exact fiveInvolutionLiftCover_of_similar hk ε π (fiveSimilar_odd hk ε hm)
      (modelInvolutionCover_of_spinData (modelSpinData_quadOdd (by omega)))
  · have hn : k + 1 = 2 * (m + 1) := by omega
    cases ε with
    | true =>
      exact fiveInvolutionLiftCover_of_similar hk true π (fiveSimilar_plus hk hn)
        (modelInvolutionCover_of_spinData (modelSpinData_quadPlus (by omega)))
    | false =>
      obtain ⟨b, c, hirr, hsim⟩ := fiveSimilar_minus hk hn
      by_cases h3 : m = 2
      · subst h3
        exact fiveInvolutionLiftCover_of_similar hk false π hsim
          (modelInvolutionCover_of_spinData (hsix b c hirr).2)
      · exact fiveInvolutionLiftCover_of_similar hk false π hsim
          (modelInvolutionCover_of_spinData (hminus (m + 1) b c (by omega) hirr).2)

section Certs

theorem fiveReflection_involution_lift_cover {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    {Γ : Type} [Group Γ] [Finite Γ] (ρ : Γ →* fiveProjective k ε π)
    (hρ : ρ.range = commutator (fiveProjective k ε π)) (hperf : commutator Γ = ⊤)
    (hker : ρ.ker ≤ Subgroup.center Γ) (hcard : Nat.card ρ.ker = 2)
    {ra rb : fiveReflectionGroup k ε π}
    (ha : (ra : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π)
    (hb : (rb : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π)
    (hab : Commute ra rb) (hne : ra ≠ rb)
    (hlift : ∃ x : Γ, ρ x = (QuotientGroup.mk (ra * rb) : fiveProjective k ε π) ∧ x * x = 1) :
    ∃ ψ : Γ ≃* ↥(commutator (fiveReflectionGroup k ε π)),
      ∀ g : Γ, ρ g =
        (QuotientGroup.mk (ψ g : fiveReflectionGroup k ε π) : fiveProjective k ε π) :=
  fiveInvolutionLiftCover_fiveProjective hk ε π fiveMinusInputs_of_certificates
    fiveMinusSixInputs_of_certificates Γ ρ hρ hperf hker hcard ha hb hab hne hlift

end Certs

end CFSG.OddTranspositions.PartThree
