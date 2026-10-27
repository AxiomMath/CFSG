module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinOddCoreOrderThree
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinIntersectionOddCoreIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixFull
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-!
The order-three alternative supplied by restriction (6).  If a large
involution coset has its odd-core fibre on `y`, we use the odd-core quotient
directly.  If the fibre is instead on `s * y`, commutation with the selected
involution `s` identifies the two conjugate intersections, so the same
quotient argument applies to `s * y`.
-/

public theorem firstCase_klein_restrictionSix_order_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {y : G} (hy : IsInvolution y) (hyH : y ∉ c.Hhat)
    (hI : 4 ≤ Nat.card {x : G // x ∈ invertedElements c.Hhat y}) :
    ∃ s x : G, IsInvolution s ∧
      s ∈ (c.Hhat ⊓ conjugateSubgroup c.Hhat y) ∧ s * y = y * s ∧
      ((x ∈ oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G) ∧
          x ≠ 1 ∧ orderOf x = 3 ∧
          x ∈ invertedElements
            (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G)) y) ∨
       (x ∈ oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G) ∧
          x ≠ 1 ∧ orderOf x = 3 ∧
          x ∈ invertedElements
            (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G)) (s * y))) := by
  classical
  have hidx := firstCase_klein_restrictionSix_index_eq
    hmin c hfirst hklein hy hyH hI
  have hOidx := firstCase_klein_intersection_oddCore_index_two_of_index_six
    hmin c hfirst hklein hy hyH hidx
  obtain ⟨s, hsI, hsD, hsy, hfib⟩ :=
    firstCase_klein_restrictionSix_oddCore_of_index_two c hy hyH hOidx hI
  rcases hfib with hfy | hfsy
  · obtain ⟨x, hxO, hxne, hxord, hxinv⟩ :=
      firstCase_klein_oddCore_inverted_order_three
        hmin c hfirst hklein hy hyH hidx hfy
    exact ⟨s, x, hsI, hsD, hsy, Or.inl ⟨hxO, hxne, hxord, hxinv⟩⟩
  · let w : G := s * y
    have hsH : s ∈ c.Hhat :=
      (show c.Hhat ⊓ conjugateSubgroup c.Hhat y ≤ c.Hhat from inf_le_left) hsD
    have hwH : w ∉ c.Hhat := by
      intro hw
      apply hyH
      have hyEq : y = s⁻¹ * w := by simp [w]
      rw [hyEq]
      exact c.Hhat.mul_mem (c.Hhat.inv_mem hsH) hw
    have hwI : IsInvolution w := by
      refine ⟨?_, ?_⟩
      · intro hw1
        apply hwH
        simpa [hw1] using c.Hhat.one_mem
      · dsimp [w]
        have hs2 : s * s = 1 := by simpa [pow_two] using hsI.2
        have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
        calc
          (s * y) ^ 2 = s * (y * s) * y := by simp [pow_two, mul_assoc]
          _ = s * (s * y) * y := by rw [hsy]
          _ = (s * s) * (y * y) := by group
          _ = 1 := by rw [hs2, hy2]; simp
    have hconjEq : conjugateSubgroup c.Hhat w =
        conjugateSubgroup c.Hhat y := by
      dsimp [w, conjugateSubgroup]
      rw [hsy]
      exact map_conj_mul_right_eq_of_mem_normalizer y
        ⟨s, Subgroup.le_normalizer hsH⟩
    have hidxW :
        let D := c.Hhat ⊓ conjugateSubgroup c.Hhat w
        let N := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
        (N.subgroupOf D).index = 6 := by
      have hD_eq : c.Hhat ⊓ conjugateSubgroup c.Hhat w =
          c.Hhat ⊓ conjugateSubgroup c.Hhat y := by rw [hconjEq]
      dsimp
      rw [hD_eq]
      exact hidx
    have hfsyW : Nat.card {x : G // x ∈ invertedElements
        (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat w : Subgroup G)) w} ≠ 1 := by
      simpa [hconjEq, w] using hfsy
    obtain ⟨x, hxO, hxne, hxord, hxinv⟩ :=
      firstCase_klein_oddCore_inverted_order_three
        hmin c hfirst hklein hwI hwH hidxW hfsyW
    exact ⟨s, x, hsI, hsD, hsy,
      Or.inr ⟨by simpa [hconjEq] using hxO, hxne, hxord,
        by simpa [hconjEq, w] using hxinv⟩⟩

end CFSG.GorensteinWalter
