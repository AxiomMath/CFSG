module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24T
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.NoOffender
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporK105In
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporMathieu

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

namespace Fi24K

open Subgroup CFSG.Blueprint CFSG.Sporadic.Fi24
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem isElemAbelian_fi24E :
    CFSG.Open.IsElemAbelian 2 fi24E := by
  refine ⟨⟨⟨fun a b => Subtype.ext (jR_injective ?_)⟩⟩, fi24E_sq⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
  exact fi24EB_mul_comm (mem_fi24E_iff.1 a.2) (mem_fi24E_iff.1 b.2)

section Rank


theorem card_le_of_not_le_fi24E {A : Subgroup CFSG.Sporadic.Fi24.J} (hAT : A ≤ fi24T)
    (hA : CFSG.Open.IsElemAbelian 2 A) (hAE : ¬ A ≤ fi24E) : Nat.card A ≤ 2 ^ 10 := by
  have h := noOffender_of_m24Out m24Out_fi24E (hAT.trans fi24T_le_normalizer) hA.2
    (fun a ha b hb => hA.comm ha hb) hAE
  have hle : (A ⊓ fi24E) ⊓ A ≤ fi24E ⊓ centralizer (A : Set J) := fun x hx =>
    mem_inf.2 ⟨(mem_inf.1 (mem_inf.1 hx).1).2,
      mem_centralizer_iff.2 fun a ha => hA.comm ha (mem_inf.1 hx).2⟩
  calc Nat.card A = (A ⊓ fi24E).relIndex A * Nat.card ↥((A ⊓ fi24E) ⊓ A) :=
        (relIndex_mul_card _ _).symm
    _ ≤ (A ⊓ fi24E).relIndex A * Nat.card ↥(fi24E ⊓ centralizer (A : Set J)) :=
        Nat.mul_le_mul_left _ (card_le_of_le hle)
    _ ≤ 2 ^ 10 := h

theorem thompsonJ_fi24T : CFSG.Quasithin.thompsonJ fi24T = fi24E := by
  have hmax : CFSG.Quasithin.IsMaxElemAbelian fi24T fi24E := by
    refine ⟨fi24E_le_fi24T, isElemAbelian_fi24E, fun B hBT hB => ?_⟩
    by_cases hBE : B ≤ fi24E
    · exact card_le_of_le hBE
    · rw [card_fi24E]
      exact (card_le_of_not_le_fi24E hBT hB hBE).trans (by norm_num)
  refine le_antisymm (iSup₂_le fun A hA => ?_) (le_iSup₂_of_le fi24E hmax le_rfl)
  by_contra hAE
  have h1 := card_le_of_not_le_fi24E hA.1 hA.2.1 hAE
  have h2 := hA.2.2 fi24E fi24E_le_fi24T isElemAbelian_fi24E
  rw [card_fi24E] at h2
  have h3 : (2 : ℕ) ^ 10 < 2 ^ 11 := by norm_num
  omega

theorem k105In_normalizer_thompsonJ :
    K105In (normalizer (CFSG.Quasithin.thompsonJ fi24T : Set CFSG.Sporadic.Fi24.J)) fi24T := by
  rw [thompsonJ_fi24T]
  obtain ⟨e⟩ := quotient_fi24E
  refine k105In_of_quotient (L := ↥NativeSporadic.M24) isSylowTwoOf_fi24T fi24T_le_normalizer
    (fi24E.subgroupOf (normalizer (fi24E : Set J))) ?_ e
    fun S H hS hSH hHs h3 =>
      k105SporAt_M24 ↥NativeSporadic.M24 ⟨MulEquiv.refl _⟩ S H hS hSH hHs h3
  rw [subgroupOf_map_subtype]
  exact inf_le_left.trans fi24E_le_fi24T

end Rank

end Fi24K

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
