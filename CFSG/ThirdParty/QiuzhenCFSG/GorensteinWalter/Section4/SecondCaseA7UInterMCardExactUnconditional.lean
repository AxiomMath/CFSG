module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7UInterMCardExact
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Unconditional exact order-three endpoint for the odd intersection image
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

public theorem secondCase_a7_u_inter_m_quotient_card_eq_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    Nat.card (((c.U ⊓ w.M).subgroupOf w.M).map
      (QuotientGroup.mk' (pPrimeCore 2 w.M))) = 3 := by
  have hdiv := secondCase_a7_u_inter_m_quotient_card_dvd_three
    hmin c w d hA7 hmodel
  have hle := secondCase_a7_u_inter_m_quotient_card_le_three
    hmin c w d hA7 hmodel
  have hpos : 0 < Nat.card (((c.U ⊓ w.M).subgroupOf w.M).map
      (QuotientGroup.mk' (pPrimeCore 2 w.M))) := Nat.card_pos
  rcases hdiv with ⟨k, hk⟩
  omega

end CFSG.GorensteinWalter
