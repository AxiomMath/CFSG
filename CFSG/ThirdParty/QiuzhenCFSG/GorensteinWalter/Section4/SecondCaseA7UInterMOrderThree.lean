module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7UInterMCardExactUnconditional
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# An order-three witness in the alternating second-case intersection

The exact quotient-cardinality endpoint for the `A₇` branch gives a concrete
odd element in `U ∩ M` whose image modulo `O₂′(M)` has order three.  This is
the small local witness used by the later `K/B/F` structural transfer.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

public theorem secondCase_a7_u_inter_m_exists_order_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    ∃ x : G, x ∈ c.U ∧ x ∈ w.M ∧ orderOf x = 3 := by
  classical
  let M : Subgroup G := w.M
  let O : Subgroup M := pPrimeCore 2 M
  letI : O.Normal := by
    dsimp [O]
    infer_instance
  let q : M →* M ⧸ O := QuotientGroup.mk' O
  let Y : Subgroup M := (c.U ⊓ M).subgroupOf M
  let Ybar : Subgroup (M ⧸ O) := Y.map q
  have hYcard : Nat.card Ybar = 3 := by
    simpa [Ybar, Y, q, O, M] using
      (secondCase_a7_u_inter_m_quotient_card_eq_three
        hmin c w d hA7 hmodel)
  have hYbar_dvd : Nat.card Ybar ∣ Nat.card Y :=
    Subgroup.card_map_dvd Y q
  have hthreeY : 3 ∣ Nat.card Y := by
    rw [hYcard] at hYbar_dvd
    exact hYbar_dvd
  obtain ⟨y0, hy0ord⟩ :=
    exists_prime_orderOf_dvd_card' (G := Y) 3 hthreeY
  refine ⟨(y0 : G), ?_, ?_, ?_⟩
  · exact (Subgroup.mem_subgroupOf.mp y0.property).1
  · exact (Subgroup.mem_subgroupOf.mp y0.property).2
  · simpa using hy0ord

end CFSG.GorensteinWalter
