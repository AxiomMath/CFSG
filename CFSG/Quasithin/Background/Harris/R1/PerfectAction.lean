module

public import CFSG.ClassicalInvolution.RouteD.GapsPerfect

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.ClassicalInvolution.RouteD.Gaps

section Abstract

variable {K N : Type*} [Group K] [Group N]

theorem perfect_fixes_of_card_le_four [Group.IsPerfect K] [Finite N] (θ : K →* MulAut N)
    (Z : Subgroup N) (hZ : ∀ k, ∀ z ∈ Z, θ k z ∈ Z) (hcard : Nat.card Z ≤ 4) :
    ∀ k, ∀ z ∈ Z, θ k z = z := by
  let : MulAction K Z :=
    { smul := fun k z => ⟨θ k z.1, hZ k z.1 z.2⟩
      one_smul := fun z => Subtype.ext (by show θ 1 z.1 = z.1; simp)
      mul_smul := fun k l z => Subtype.ext (by show θ (k * l) z.1 = θ k (θ l z.1); simp) }
  intro k z hz
  have h := perfect_smul_eq_of_card_le_four (L := K) (α := Z) hcard k ⟨z, hz⟩
  exact congrArg Subtype.val h

end Abstract

end CFSG.Quasithin.Background.Harris.R1
