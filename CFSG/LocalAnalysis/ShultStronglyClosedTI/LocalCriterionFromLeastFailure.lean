module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ShultSimpleAssembly
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum

public section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open

theorem local_criterion_of_no_least_failure
    (himp : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (z : G),
      ¬ MinimalInvolutionPointLocalFailure H z)
    (Y : Type) [Group Y] [Finite Y] (H : Subgroup Y) (z : Y)
    (hlocal : InvolutionPointLocalEmbedding H z) (hcentral : InvolutionPointCentralSylow z) :
    fusionStronglyEmbedded (H.subgroupOf (involutionPointHull z)) := by
  induction hn : Nat.card Y using Nat.strong_induction_on generalizing Y with
  | _ n ih =>
    by_contra hfail
    refine himp Y H z ⟨hlocal, hcentral, hfail, ?_⟩
    intro Y' _ _ hcard A a hA ha
    exact ih (Nat.card Y') (hn ▸ hcard) Y' A a hA ha rfl

theorem bounded_criterion_of_no_least_failure
    (himp : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (z : G),
      ¬ MinimalInvolutionPointLocalFailure H z) (n : ℕ) :
    BoundedInvolutionPointCriterion n := by
  intro Y _ _ _ H z hlocal hcentral
  exact local_criterion_of_no_least_failure himp Y H z hlocal hcentral

theorem shult_simple_of_no_least_failure
    (himp : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (z : G),
      ¬ MinimalInvolutionPointLocalFailure H z)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (T : Sylow 2 G) (U : Subgroup G) (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥)
    (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) : fusionIsBenderGroup G :=
  shult_simple_from_bounded_local_criterion G
    (bounded_criterion_of_no_least_failure himp (Nat.card G)) hnonab T U hUT hU hUel hclosed hTI

end CFSG.ShultStronglyClosedTI
