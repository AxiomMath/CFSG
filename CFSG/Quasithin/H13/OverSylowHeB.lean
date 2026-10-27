
module

public import CFSG.Quasithin.H13.OverSylowHeBBase
import all CFSG.Quasithin.H13.OverSylowHeBBase

public import Certificates.Certificate589204

public section

namespace CFSG.Quasithin.H13.LocDbl.OverHe

open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Sporadic.He (J a b card_J heEquivJ)

theorem heSubO2_J :
    ∀ U : Subgroup J, Nat.card U = 2 ^ 10 * 3 ^ 2 → SubO2Prop (2 ^ 6 * 3) U :=
  Certificates.certificate589204

theorem heSubO2_He :
    ∀ U : Subgroup CFSG.Blueprint.NativeSporadic.He, Nat.card U = 2 ^ 10 * 3 ^ 2 →
      SubO2Prop (2 ^ 6 * 3) U := by
  have key := SubO2Prop.of_equiv_card (Q := CFSG.Blueprint.NativeSporadic.He) (B := ↥J) heSubO2_J
    heEquivJ
  exact key

theorem heSubO2_carrier :
    ∀ (Q : Type) [Group Q] [Finite Q], Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.Carrier .He) →
      ∀ U : Subgroup Q, Nat.card U = 2 ^ 10 * 3 ^ 2 →
        ∃ Y : Subgroup Q, Y ≤ U ∧ (Y.subgroupOf U).Normal ∧ Nat.card Y = 2 ^ 6 * 3 ∧
          Y ≤ oTwoUp U := by
  intro Q _ _ hQ U hU
  obtain ⟨e⟩ := hQ
  exact SubO2Prop.of_equiv_card (B := CFSG.Blueprint.NativeSporadic.He) heSubO2_He e U hU

end CFSG.Quasithin.H13.LocDbl.OverHe
