module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7EquationEight
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaData
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7UInterMIsPGroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27IndexTwo
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # The odd core is a 3-group in the A7 branch -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the A7 branch of the second case, `U = O(H)` is a `3`-group. -/
public theorem secondCase_a7_U_isPGroup_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    IsPGroup 3 c.U := by
  classical
  obtain ⟨od⟩ := secondCase_a7_omegaData hmin c w d hA7 hmodel
  let X : Subgroup G := c.U ⊓ w.M
  let L : Subgroup G := od.B ⊔ c.FU
  have hBleX : od.B ≤ X := by
    change od.B ≤ c.U ⊓ w.M
    rw [← od.U_inter_M_eq]
    exact le_sup_right
  have hBleU : od.B ≤ c.U := hBleX.trans inf_le_left
  have hXp : IsPGroup 3 X := by
    simpa [X] using
      secondCase_a7_U_inter_M_isPGroup_three hmin c w d hA7 hmodel
  have hBp : IsPGroup 3 od.B := by
    have hBsubp : IsPGroup 3 (od.B.subgroupOf X) :=
      hXp.to_subgroup (od.B.subgroupOf X)
    exact hBsubp.of_equiv (Subgroup.subgroupOfEquivOfLe hBleX)
  have hBnormFU : od.B ≤ Subgroup.normalizer (c.FU : Set G) :=
    hBleU.trans
      (le_normalizer_of_isNormalIn (fittingSubgroupOf_isNormalIn c.U))
  have hLp : IsPGroup 3 L := by
    change IsPGroup 3 (od.B ⊔ c.FU : Subgroup G)
    exact IsPGroup.to_sup_of_normal_right' hBp od.FU_isPGroup hBnormFU
  have hLleU : L ≤ c.U :=
    sup_le hBleU (fittingSubgroupOf_le c.U)
  have hidxLe : L.relIndex c.U ≤ 3 := by
    simpa [L] using secondCase_a7_equation_eight c w d od
  have hUodd : Odd (Nat.card c.U) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  have hidxOdd : Odd (L.relIndex c.U) :=
    Odd.of_dvd_nat hUodd (Subgroup.relIndex_dvd_card L c.U)
  have hidxPos : 0 < L.relIndex c.U := by
    change 0 < (L.subgroupOf c.U).index
    rw [Subgroup.index_eq_card]
    exact Nat.card_pos
  obtain ⟨k, hk⟩ := hidxOdd
  have hidxCases : L.relIndex c.U = 1 ∨ L.relIndex c.U = 3 := by
    omega
  obtain ⟨b, hb⟩ : ∃ b : ℕ, L.relIndex c.U = 3 ^ b := by
    rcases hidxCases with hidx | hidx
    · exact ⟨0, by simpa using hidx⟩
    · exact ⟨1, by simpa using hidx⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hLp
  have hLsubcard : Nat.card (L.subgroupOf c.U) = Nat.card L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLleU).toEquiv
  have hmul := Subgroup.card_mul_index (L.subgroupOf c.U)
  change Nat.card (L.subgroupOf c.U) * L.relIndex c.U =
    Nat.card c.U at hmul
  apply IsPGroup.of_card (n := a + b)
  calc
    Nat.card c.U = Nat.card (L.subgroupOf c.U) * L.relIndex c.U :=
      hmul.symm
    _ = Nat.card L * L.relIndex c.U := by rw [hLsubcard]
    _ = 3 ^ a * 3 ^ b := by rw [ha, hb]
    _ = 3 ^ (a + b) := by rw [pow_add]

end CFSG.GorensteinWalter
