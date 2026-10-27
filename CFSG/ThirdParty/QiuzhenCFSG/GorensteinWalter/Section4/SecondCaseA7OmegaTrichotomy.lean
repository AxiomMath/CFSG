module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaOrder

namespace CFSG
end CFSG
open CFSG

/-! # The A7 omega trichotomy -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The omega subgroup either equals the equation-(6) subgroup, has order
`27` and properly contains it, or is inverted by the chosen involution. -/
public theorem secondCase_a7_omega_trichotomy
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseA7OmegaData c w d) :
    let QG : Subgroup G := od.Q.map c.FU.subtype
    od.K ⊔ od.F = QG ∨
      (od.K ⊔ od.F < QG ∧ Nat.card QG = 27) ∨
      (¬ od.F ≤ QG ∧
        ∀ x : G, x ∈ QG →
          (od.s : G) * x * (od.s : G)⁻¹ = x⁻¹) := by
  dsimp only
  rcases secondCase_a7_omega_fixed_dichotomy c w d od with hle | hinv
  · by_cases heq : od.K ⊔ od.F = od.Q.map c.FU.subtype
    · exact Or.inl heq
    · right
      left
      have hlt : od.K ⊔ od.F < od.Q.map c.FU.subtype :=
        lt_of_le_of_ne hle heq
      exact ⟨hlt,
        secondCase_a7_omega_card_eq_twenty_seven_of_lt c w d od hlt⟩
  · exact Or.inr (Or.inr hinv)

end CFSG.GorensteinWalter
