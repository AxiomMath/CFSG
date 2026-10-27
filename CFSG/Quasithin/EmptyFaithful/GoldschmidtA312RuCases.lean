module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBasic

public section

namespace CFSG.Quasithin.A312Ru

open CFSG.Quasithin CFSG.QuasithinUnique.Vol2Native.A312L

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem not_isSolvable_join {T B : Subgroup Γ} (hB : B ∈ lFamily T) :
    ¬ Group.IsSolvable ↥(B ⊔ T) := by
  have hB' : B ∈ cComp (B ⊔ T) := hB
  exact fun hs => not_isSolvable_of_mem_cComp hB'
    (Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (le_of_mem_cComp hB' : B ≤ B ⊔ T))
      (Subgroup.inclusion_injective _))

theorem nonabelian_of_simple {S : Type} [Group S] [IsSimpleGroup S]
    (h : ¬ (Nat.card S).Prime) : ∃ a b : S, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have : IsMulCommutative S := ⟨⟨hcon⟩⟩
  exact h (Group.is_simple_iff_prime_card.mp inferInstance)

end CFSG.Quasithin.A312Ru
