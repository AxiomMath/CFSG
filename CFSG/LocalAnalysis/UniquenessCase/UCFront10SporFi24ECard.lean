
module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24ECardBase

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24ERigid
public import CFSG.Sporadic.Fi24.Local
public import CFSG.Sporadic.Fi24.OctadsInputs
public import CFSG.Fischer.NoF25.Octads
public import CFSG.Sporadic.Fi24.OctadAction
public import CFSG.Sporadic.Fi24.OctadData

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

namespace Fi24K

open CFSG.Sporadic.Th CFSG.Sporadic.Fi24 CFSG.Fischer

section Rel

local notation "bP" => @famProd R inferInstance (Fin 24) inferInstance inferInstance bbar bbar_comm

theorem card_fi24EB : Nat.card fi24EB = 4096 :=
  le_antisymm card_fi24EB_le le_card_fi24EB

end Rel

section E

theorem card_fi24E : Nat.card fi24E = 2 ^ 11 := by
  have hrel : JR.relIndex fi24EB = 2 := by
    have hd : JR.relIndex fi24EB ∣ 2 := index_JR ▸ Subgroup.relIndex_dvd_index_of_normal JR fi24EB
    have h1 : JR.relIndex fi24EB ≠ 1 := fun h =>
      bbar_not_mem_JR 0 (Subgroup.relIndex_eq_one.1 h (Subgroup.subset_closure ⟨0, rfl⟩))
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact absurd h h1
    · exact h
  have hcard := Subgroup.card_mul_index (JR.subgroupOf fi24EB)
  have e1 : Nat.card (JR.subgroupOf fi24EB) = Nat.card fi24E := by
    rw [← Subgroup.card_map_of_injective (f := fi24EB.subtype) Subtype.val_injective,
      Subgroup.subgroupOf_map_subtype, ← map_fi24E,
      Subgroup.card_map_of_injective jR_injective]
  rw [e1, ← Subgroup.relIndex, hrel, card_fi24EB] at hcard
  omega

end E

end Fi24K

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
