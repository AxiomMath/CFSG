module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7UInterMCard
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4: the A₇ odd-intersection cardinality dichotomy

The ambient A₇ quotient bounds the odd image of `U ∩ M` by `3`.  Since that
image is itself odd and nonempty, its cardinality is therefore exactly `1` or
`3`.  This is a small reusable reduction for the still-open exact-index
argument.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

public theorem secondCase_a7_u_inter_m_quotient_card_eq_one_or_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    Nat.card (((c.U ⊓ w.M).subgroupOf w.M).map
      (QuotientGroup.mk' (pPrimeCore 2 w.M))) = 1 ∨
      Nat.card (((c.U ⊓ w.M).subgroupOf w.M).map
        (QuotientGroup.mk' (pPrimeCore 2 w.M))) = 3 := by
  classical
  let M : Subgroup G := w.M
  let O : Subgroup M := pPrimeCore 2 M
  let q : M →* M ⧸ O := QuotientGroup.mk' O
  let Y : Subgroup M := (c.U ⊓ M).subgroupOf M
  let Ybar : Subgroup (M ⧸ O) := Y.map q
  have hUodd : Odd (Nat.card (↥c.U)) := by
    change Odd (Nat.card (↥(oddCoreOf c.H)))
    exact odd_card_oddCoreOf c.H
  have hYcard : Nat.card Y = Nat.card (↥(c.U ⊓ M)) := by
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := c.U ⊓ M) (K := M) inf_le_right).toEquiv
  have hYodd : Odd (Nat.card Y) := by
    rw [hYcard]
    exact Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le inf_le_left)
  have hYbarodd : Odd (Nat.card Ybar) :=
    Odd.of_dvd_nat hYodd (Subgroup.card_map_dvd Y q)
  have hle : Nat.card Ybar ≤ 3 := by
    have h := secondCase_a7_u_inter_m_quotient_card_le_three
      hmin c w d hA7 hmodel
    simpa [Ybar, Y, q, O, M] using h
  have hpos : 0 < Nat.card Ybar := Nat.card_pos
  rcases hYbarodd with ⟨n, hn⟩
  have hcases : Nat.card Ybar = 1 ∨ Nat.card Ybar = 3 := by
    omega
  simpa [Ybar, Y, q, O, M] using hcases

end CFSG.GorensteinWalter
