module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FittingOddCoreEquality
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4, equation (4): the odd-core half

The fitting subgroup `F` extracted from equation (3) lies in the odd core
`U = O_{2'}(H)`.  Once equation (4) supplies `F ◁ M`, the generic normal
odd-subgroup endpoint identifies `F` as a subgroup of `O_{2'}(M)`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A normal odd subgroup of the fitting subgroup of `U` lies in the odd core
of the maximal subgroup `M`. -/
public theorem secondCase_a7_fitting_le_oddCore
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (F : Subgroup G)
    (hFleFU : F ≤ fittingSubgroupOf c.U)
    (hFnormalM : IsNormalIn F w.M) :
    F ≤ oddCoreOf w.M := by
  have hUodd : Odd (Nat.card (↥c.U)) := by
    change Odd (Nat.card (↥(oddCoreOf c.H)))
    exact odd_card_oddCoreOf c.H
  have hFleU : F ≤ c.U := hFleFU.trans (fittingSubgroupOf_le c.U)
  have hFodd : Odd (Nat.card (↥F)) :=
    Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le hFleU)
  have hFcop : Nat.Coprime 2 (Nat.card (↥F)) :=
    Nat.coprime_two_left.mpr hFodd
  exact le_oddCoreOf_of_normal_of_coprime w.M F hFnormalM.1 hFnormalM hFcop

end CFSG.GorensteinWalter
