module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7UInterMCardCases
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7UInterMCardThree

namespace CFSG
end CFSG
open CFSG

/-!
# Exact order-three endpoint for the odd intersection image

The ambient `A₇` bound gives the dichotomy `1 ∨ 3`.  This module isolates
the remaining purely finite step: a nontrivial image cannot have cardinality
`1`, so it has cardinality exactly `3`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

public theorem secondCase_a7_u_inter_m_quotient_card_eq_three_of_ne_bot
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7)
    (hne : (((c.U ⊓ w.M).subgroupOf w.M).map
      (QuotientGroup.mk' (pPrimeCore 2 w.M))) ≠ ⊥) :
    Nat.card (((c.U ⊓ w.M).subgroupOf w.M).map
      (QuotientGroup.mk' (pPrimeCore 2 w.M))) = 3 := by
  rcases secondCase_a7_u_inter_m_quotient_card_eq_one_or_three
      hmin c w d hA7 hmodel with h1 | h3
  · exfalso
    apply hne
    exact (Subgroup.eq_bot_iff_card (H :=
      ((c.U ⊓ w.M).subgroupOf w.M).map
        (QuotientGroup.mk' (pPrimeCore 2 w.M)))).mpr h1
  · exact h3

end CFSG.GorensteinWalter
