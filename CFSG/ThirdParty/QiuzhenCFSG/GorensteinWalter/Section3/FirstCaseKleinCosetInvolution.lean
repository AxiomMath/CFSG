module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCosetFiberCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CosetInvolutionCount
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Outside-coset involutions and inverted elements

For an involution outside `Ĥ`, the puncture in Fact 1.4 is vacuous: the
representing involution is not itself an element of `Ĥ`.  Thus the number of
involutions in `Ĥ * y` is exactly the cardinality of `I_Ĥ(y)`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

open scoped Pointwise

public theorem firstCase_klein_coset_involution_card_eq
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {y : G}
    (hy : IsInvolution y) (hyH : y ∉ c.Hhat) :
    firstCaseCosetInvolutions c y =
      Nat.card {x : G // x ∈ invertedElements c.Hhat y} := by
  classical
  have hcard := Nat.card_congr
    (involution_coset_fiber_equiv_inverted c.Hhat hy)
  have hset : invertedIn c.Hhat y = invertedElements c.Hhat y :=
    invertedIn_eq_invertedElements c.Hhat y
  let e0 : {i : G // i ∈ invertedIn c.Hhat y ∧ i ≠ y} ≃
      {i : G // i ∈ invertedElements c.Hhat y} := by
    refine {
      toFun := fun i => ⟨i.1, by
        rw [← hset]
        exact i.2.1⟩
      invFun := fun i => ⟨i.1, by
        rw [hset]
        exact i.2, by
          intro h
          exact hyH (by simpa [h] using i.2.1)⟩
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }
  calc
    firstCaseCosetInvolutions c y =
        Nat.card (cosetInvolution_fiber c.Hhat
          (cosetInvolution_proj c.Hhat y)) :=
      firstCase_coset_fiber_card_eq c hy
    _ = Nat.card {i : G // i ∈ invertedIn c.Hhat y ∧ i ≠ y} := by
      rw [cosetInvolution_fiber_eq_involutionFiber]
      exact hcard
    _ = Nat.card {i : G // i ∈ invertedElements c.Hhat y} := Nat.card_congr e0

end CFSG.GorensteinWalter
