module

public import CFSG.Monster.Existence.DLevel
public import CFSG.Monster.B.TwoA.Triality.PermMain

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA

@[expose] def swapPerm : Equiv.Perm (Fin 24) where
  toFun := ![1, 0, 2, 20, 10, 18, 5, 12, 11, 16, 7, 15, 22, 21, 23, 3, 14, 19, 9, 4, 13, 8, 6, 17]
  invFun := ![1, 0, 2, 15, 19, 6, 22, 10, 21, 18, 4, 8, 7, 20, 16, 11, 9, 23, 5, 17, 3, 13, 12, 14]
  left_inv := by decide
  right_inv := by decide

private theorem swapPerm_basis : ∀ i, Code.B i ∘ ⇑swapPerm ∈ C := by decide +kernel

private theorem swapPerm_basis' : ∀ i, Code.B i ∘ ⇑swapPerm⁻¹ ∈ C := by decide +kernel

theorem swapPerm_mem : swapPerm ∈ AutPerm := mem_AutPerm_of_basis swapPerm_basis swapPerm_basis'

@[expose] def swapAut : AutPerm := ⟨swapPerm, swapPerm_mem⟩

theorem fixesPair01_swapAut : FixesPair01 swapAut := Or.inr ⟨rfl, rfl⟩

theorem gLift_swap_conj_uStar :
    gLift swapAut * uStar * (gLift swapAut)⁻¹ = uStar * tStar := by
  rw [uStar_mul_tStar]
  change gLift swapAut * rhoEquiv (DQ (deltaPair 0 2)) * (gLift swapAut)⁻¹ =
    rhoEquiv (DQ (deltaPair 1 2))
  rw [gLift_conj_DQ, permD_deltaPair]
  rfl

theorem mem_Cgen_of_commute_uStar
    (hE : Subgroup.centralizer (FE : Set MGriess) ≤ GmatGriess)
    (hH : ∀ g ∈ Gmat, g * tStar = tStar * g → g ∈ Cgen)
    {c : SpaceB ≃ₗ[ℚ] SpaceB} (hc : c ∈ CfullA) (hcu : c * uStar = uStar * c) : c ∈ Cgen := by
  have hct : c * tStar = tStar * c := commute_tStar_of_mem_CfullA hc
  have hm : (⟨c, hc.1⟩ : MGriess) ∈ Subgroup.centralizer (FE : Set MGriess) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rcases mem_FE.1 hh with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · exact Subtype.ext hct.symm
    · exact Subtype.ext hcu.symm
    · apply Subtype.ext
      show tStar * uStar * c = c * (tStar * uStar)
      rw [mul_assoc, ← hcu, ← mul_assoc, ← hct, mul_assoc]
  exact hH c (Subgroup.mem_subgroupOf.1 (hE hm)) hct

theorem mem_Cgen_of_conj_uA
    (hE : Subgroup.centralizer (FE : Set MGriess) ≤ GmatGriess)
    (hH : ∀ g ∈ Gmat, g * tStar = tStar * g → g ∈ Cgen)
    (c : CfullA) (hc : c * uA * c⁻¹ = uA ∨ c * uA * c⁻¹ = uA * tStarA) :
    (c : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Cgen := by
  rcases hc with h | h
  · have h' : (c : SpaceB ≃ₗ[ℚ] SpaceB) * uStar * (c : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ = uStar :=
      congrArg Subtype.val h
    refine mem_Cgen_of_commute_uStar hE hH c.2 ?_
    calc (c : SpaceB ≃ₗ[ℚ] SpaceB) * uStar
        = (c : SpaceB ≃ₗ[ℚ] SpaceB) * uStar * (c : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ *
          (c : SpaceB ≃ₗ[ℚ] SpaceB) := by group
      _ = uStar * c := by rw [h']
  · have h' : (c : SpaceB ≃ₗ[ℚ] SpaceB) * uStar * (c : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ = uStar * tStar :=
      congrArg Subtype.val h
    obtain ⟨g, hgC, hg⟩ : ∃ g ∈ Cgen, g * uStar * g⁻¹ = uStar * tStar :=
      ⟨_, gLift_mem_Cgen fixesPair01_swapAut, gLift_swap_conj_uStar⟩
    have hd : g⁻¹ * (c : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Cgen := by
      refine mem_Cgen_of_commute_uStar hE hH
        (CfullA.mul_mem (CfullA.inv_mem (Cgen_le_CfullA hgC)) c.2) ?_
      calc g⁻¹ * (c : SpaceB ≃ₗ[ℚ] SpaceB) * uStar
          = g⁻¹ * ((c : SpaceB ≃ₗ[ℚ] SpaceB) * uStar * (c : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹) *
            (c : SpaceB ≃ₗ[ℚ] SpaceB) := by group
        _ = g⁻¹ * (g * uStar * g⁻¹) * (c : SpaceB ≃ₗ[ℚ] SpaceB) := by
          rw [h', hg]
        _ = uStar * (g⁻¹ * (c : SpaceB ≃ₗ[ℚ] SpaceB)) := by group
    have := Cgen.mul_mem hgC hd
    rwa [mul_inv_cancel_left] at this

end CFSG.Monster.Existence
