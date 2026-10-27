module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinIntersectionOdd
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseOddCoreIndexTwo
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG
noncomputable section
open scoped Pointwise
namespace CFSG.GorensteinWalter
universe u

public theorem firstCase_klein_intersection_oddCore_index_two_of_index_six
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
    ((oddCoreOf D).subgroupOf D).index = 2 := by
  classical
  let D : Subgroup G := c.Hhat ⊓ conjugateSubgroup c.Hhat y
  let N : Subgroup G := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
  have hNnormal : (N.subgroupOf D).Normal := by
    have hBnorm : IsNormalIn (twoCoreOf c.Hhat ⊔ c.U) c.Hhat :=
      firstCase_klein_VU_normal_in_Hhat hmin c
    have hDle : D ≤ c.Hhat := inf_le_left
    apply (Subgroup.normal_subgroupOf_iff (show N ≤ D from inf_le_left)).2
    intro n d hn hd
    refine ⟨?_, ?_⟩
    · exact D.mul_mem (D.mul_mem hd ((show N ≤ D from inf_le_left) hn)) (D.inv_mem hd)
    · exact hBnorm.2 d (hDle hd) n ((show N ≤ twoCoreOf c.Hhat ⊔ c.U from inf_le_right) hn)
  let : (N.subgroupOf D).Normal := hNnormal
  have hindex' : (N.subgroupOf D).index = 6 := by simpa [D, N] using hindex
  have hNodd : Nat.Coprime 2 (Nat.card N) := by
    exact firstCase_klein_intersection_odd_of_index_six hmin c hfirst hklein hy hyH hindex
  have hPindex : (pPrimeCore 2 (↥D)).index = 2 := by
    apply pPrimeCore_index_two_of_normal_odd_index_six (N := N.subgroupOf D)
      (hNnormal := hNnormal)
    · have hcard : Nat.card (N.subgroupOf D) = Nat.card N := by
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show N ≤ D from inf_le_left)).toEquiv
      rw [hcard]
      exact hNodd
    · exact hindex'
  let O : Subgroup G := oddCoreOf D
  have hOleD : O ≤ D := by
    dsimp [O, oddCoreOf]
    exact Subgroup.map_subtype_le (pPrimeCore 2 (↥D))
  let P : Subgroup (↥D) := pPrimeCore 2 (↥D)
  have hOcard : Nat.card O = Nat.card P := by
    simpa [O, P, oddCoreOf] using
      (Subgroup.card_map_of_injective (K := pPrimeCore 2 (↥D)) D.subtype_injective)
  have hOsubcard : Nat.card (O.subgroupOf D) = Nat.card P := by
    calc
      Nat.card (O.subgroupOf D) = Nat.card O :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOleD).toEquiv
      _ = Nat.card P := hOcard
  have hmulP := P.card_mul_index
  have hmulO := (O.subgroupOf D).card_mul_index
  rw [hPindex] at hmulP
  rw [hOsubcard] at hmulO
  have hidx : (O.subgroupOf D).index = 2 := by
    apply Nat.mul_left_cancel (Nat.card_pos (α := P))
    calc
      Nat.card P * (O.subgroupOf D).index = Nat.card (↥D) := hmulO
      _ = Nat.card P * 2 := hmulP.symm
  have hout : (O.subgroupOf D).index = 2 := hidx
  simpa [D, O] using hout

end CFSG.GorensteinWalter

