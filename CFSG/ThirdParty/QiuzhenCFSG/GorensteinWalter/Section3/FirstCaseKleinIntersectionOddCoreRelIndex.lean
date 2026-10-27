module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinIntersectionOddCoreIndex
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-!
The order-six quotient in restriction (6) has an odd kernel.  Since the
odd core of the intersection has index two, the kernel has relative index
three in that odd core.  Keeping this as a separate theorem avoids
repeating the subgroup-of coercion argument in the element-extraction
module.
-/

public theorem firstCase_klein_intersection_oddCore_relIndex_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {y : G} (hy : IsInvolution y) (hyH : y ∉ c.Hhat)
    (hindex :
      let D := c.Hhat ⊓ conjugateSubgroup c.Hhat y
      let N := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
      (N.subgroupOf D).index = 6) :
    let D := c.Hhat ⊓ conjugateSubgroup c.Hhat y
    let N := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
    let O := oddCoreOf D
    N.relIndex O = 3 := by
  classical
  let D : Subgroup G := c.Hhat ⊓ conjugateSubgroup c.Hhat y
  let N : Subgroup G := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
  let O : Subgroup G := oddCoreOf D
  have hNleD : N ≤ D := inf_le_left
  have hNnormal : (N.subgroupOf D).Normal := by
    have hBnorm : IsNormalIn (twoCoreOf c.Hhat ⊔ c.U) c.Hhat :=
      firstCase_klein_VU_normal_in_Hhat hmin c
    have hDle : D ≤ c.Hhat := inf_le_left
    apply (Subgroup.normal_subgroupOf_iff hNleD).2
    intro n d hn hd
    refine ⟨?_, ?_⟩
    · exact D.mul_mem (D.mul_mem hd (hNleD hn)) (D.inv_mem hd)
    · exact hBnorm.2 d (hDle hd) n
        ((show N ≤ twoCoreOf c.Hhat ⊔ c.U from inf_le_right) hn)
  let : (N.subgroupOf D).Normal := hNnormal
  have hindex' : (N.subgroupOf D).index = 6 := by
    simpa [D, N] using hindex
  have hNodd : Nat.Coprime 2 (Nat.card N) := by
    exact firstCase_klein_intersection_odd_of_index_six
      hmin c hfirst hklein hy hyH hindex
  have hNsubodd : Nat.Coprime 2 (Nat.card (N.subgroupOf D)) := by
    have hcard : Nat.card (N.subgroupOf D) = Nat.card N := by
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe hNleD).toEquiv
    rw [hcard]
    exact hNodd
  have hNsub_le_core : N.subgroupOf D ≤ pPrimeCore 2 (↥D) := by
    exact le_sSup ⟨hNnormal, hNsubodd⟩
  have hmapN : (N.subgroupOf D).map D.subtype = N :=
    Subgroup.map_subgroupOf_eq_of_le hNleD
  have hNleO : N ≤ O := by
    dsimp [O, oddCoreOf]
    rw [← hmapN]
    exact Subgroup.map_mono hNsub_le_core
  have hOleD : O ≤ D := by
    dsimp [O, oddCoreOf]
    exact Subgroup.map_subtype_le (pPrimeCore 2 (↥D))
  have hOindex : (O.subgroupOf D).index = 2 := by
    simpa [D, O] using
      firstCase_klein_intersection_oddCore_index_two_of_index_six
        hmin c hfirst hklein hy hyH hindex
  have hrel := Subgroup.relIndex_mul_relIndex N O D hNleO hOleD
  have hrel' : (N.subgroupOf O).index * (O.subgroupOf D).index =
      (N.subgroupOf D).index := by
    simpa [Subgroup.relIndex] using hrel
  rw [hindex', hOindex] at hrel'
  norm_num at hrel'
  have hthree : (N.subgroupOf O).index = 3 := by omega
  simpa [D, N, O, Subgroup.relIndex] using hthree

end CFSG.GorensteinWalter
