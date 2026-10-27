module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcUntwisted
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.Families
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.PSp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.PSU
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.POmega

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree (ReeTag)


theorem involQAt_F4 : InvolQAt .F4 := by
  intro S _ _ n p e hp2 h3 _ hS
  obtain ⟨⟨hp, he, -⟩, hm⟩ := hS.chevalleyExceptionalModel (by decide)
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hm
  exact InvolInvertsGood.of_mulEquiv φ.symm (involInvertsGood_F4_G2 hp hp2 he hK h3 (Or.inl rfl))

theorem involQAt_E8 : InvolQAt .E8 := by
  intro S _ _ n p e hp2 h3 _ hS
  obtain ⟨⟨hp, he, -⟩, hm⟩ := hS.chevalleyExceptionalModel (by decide)
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := nonempty_mulEquiv_adjointGroup .E8 hm
  exact InvolInvertsGood.of_mulEquiv φ.symm (involInvertsGood_E8 hp hp2 he hK h3)

theorem involQAt_G2_of
    (hR : ∀ (a : ℕ) (L : Type) [Field L] [Finite L] [CharP L ReeTag.G2.prime], 1 ≤ a →
      Nat.card L = 3 ^ (2 * a + 1) → ∃ x : adjointGroup ReeTag.G2.tag L, orderOf x = 3 ∧
        ReeTag.G2.finiteReeAut L a x = x⁻¹ ∧ IsSpecialGood 3 x) :
    InvolQAt .G2 := by
  intro S _ _ n p e hp2 h3 _ hS
  obtain ⟨⟨hp, he, -⟩, hm⟩ := hS.chevalleyExceptionalModel (by decide)
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm
  refine InvolInvertsGood.of_mulEquiv φ.symm ?_
  rcases eq_or_ne p 3 with rfl | hp3
  · exact involInvertsGood_G2_three hR he hK h3
  · exact involInvertsGood_F4_G2 hp hp2 he hK h3 (Or.inr ⟨rfl, hp3⟩)

theorem w4Lem10_5InvolQ_of_remaining
    (hR : ∀ (a : ℕ) (L : Type) [Field L] [Finite L] [CharP L ReeTag.G2.prime], 1 ≤ a →
      Nat.card L = 3 ^ (2 * a + 1) → ∃ x : adjointGroup ReeTag.G2.tag L, orderOf x = 3 ∧
        ReeTag.G2.finiteReeAut L a x = x⁻¹ ∧ IsSpecialGood 3 x)
    (hE6 : InvolQAt .E6) (hE7 : InvolQAt .E7) (h2E6 : InvolQAt .twistedE6)
    (h3D4 : InvolQAt .trialityD4) : W4Lem10_5InvolQ :=
  w4Lem10_5InvolQ_of involQAt_PSU involQAt_PSp involQAt_POmegaOdd involQAt_POmegaPlus
      involQAt_POmegaMinus (involQAt_G2_of hR) involQAt_F4 hE6 hE7 involQAt_E8 h2E6 h3D4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
