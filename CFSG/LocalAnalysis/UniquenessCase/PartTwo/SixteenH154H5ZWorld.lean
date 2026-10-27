module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

structure s16h_L3World {U : Type} [CommGroup U] (N L : Subgroup (MulAut U)) : Prop where
  elem : ∀ u : U, u * u = 1
  le : L ≤ N
  normal : N ≤ Subgroup.normalizer (L : Set (MulAut U))
  quasi : CFSG.Open.IsQuasisimple ↥L
  sl3 : IsSLn ↥L 3 1
  comm : commSub ⊤ L = ⊤
  sum : ∃ k : ℕ, k ≤ 3 ∧ SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) L ⊤ (fixV L) k
  faithful : ∀ a ∈ N, (∀ u : U, a u * u⁻¹ ∈ fixV L) → a = 1
  trans : ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L, ∃ g ∈ N, I₂ = I₁.map g.toMonoidHom

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
