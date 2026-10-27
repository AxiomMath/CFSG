module

public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryCoverOddKernel
public import CFSG.LieType.Chevalley.G2LargeEvenCover
public import CFSG.LieType.Chevalley.TrialityCover

public section

namespace CFSG.RankThree

open CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

theorem even_G2_large_field_perfect_central_kernel_odd {E : Type*} {T : Type} [Group E]
    [Group T] [Finite E] [Finite T] [Group.IsPerfect E] (η : E →* T)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) {f : ℕ} (hf : 3 ≤ f)
    (hT : ChevalleyExceptionalModel T .G2 2 f) : Odd (Nat.card η.ker) := by
  have hL : LieModel T .G2 0 2 f := Or.inr (Or.inl ⟨rfl, by decide, hT⟩)
  exact odd_card_ker_of_two_cover_trivial η hη hC fun θ hθ hθC hθ2 =>
    (CFSG.LieType.Chevalley.G2_large_even_field_central_two_cover_trivial θ hθ hθC hθ2 hf hL).1

theorem nonprime_even_triality_perfect_central_kernel_odd {E : Type*} {T : Type} [Group E]
    [Group T] [Finite E] [Finite T] [Group.IsPerfect E] (η : E →* T)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) {f : ℕ} (hf : 2 ≤ f)
    (hT : ChevalleyExceptionalModel T .trialityD4 2 f) : Odd (Nat.card η.ker) := by
  have hL : LieModel T .trialityD4 0 2 f := Or.inr (Or.inl ⟨rfl, by decide, hT⟩)
  exact odd_card_ker_of_two_cover_trivial η hη hC fun θ hθ hθC hθ2 =>
    (CFSG.LieType.Chevalley.triality_nonprime_even_field_central_two_cover_trivial θ hθ hθC hθ2
      hf hL).1

end CFSG.RankThree
