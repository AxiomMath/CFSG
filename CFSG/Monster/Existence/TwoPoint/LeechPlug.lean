module

public import CFSG.Monster.Existence.TwoPoint.LeechLong
public import CFSG.Monster.Existence.TwoPoint.CoPairDefs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG CFSG.Monster CFSG.Monster.SpinLattice CFSG.Monster.Griess CFSG.Monster.VisCert
  CFSG.Monster.B.Short CFSG.Monster.B

theorem coW1_mem_shortSet : coW1 ∈ shortSet := ⟨ellVec 0, coW1_mem_minVecs, coW1_eq_classOf.symm⟩

theorem coW2_mem_shortSet : coW2 ∈ shortSet := ⟨ellVec 12, coW2_mem_minVecs, coW2_eq_classOf.symm⟩

theorem v0_add_coW2_mem_shortSet : Co2.v0 + coW2 ∈ shortSet :=
  ⟨ellVec 13, ellVec13_mem_minVecs, coW2_add_v0_eq.symm⟩

theorem leech_fourA_shape_coW1 :
    ∃ α β : MGriess, IsConj tGriess α ∧ IsConj tGriess β ∧ orderOf (α * β) = 4 ∧
      (α * β) ^ 2 = xGriess ∧
      ∃ (N : Subgroup ↥(cent2 α β)) (_ : N.Normal), IsExtraspecialPGroup 2 N ∧
        Nat.card N = 2 ^ 23 ∧ Nonempty (↥(cent2 α β) ⧸ N ≃* ↥(Kstab Co2.v0 ⊓ Kstab coW1)) :=
  leech_fourA_shape coW1 coW1_mem_shortSet bL_v0_coW1

theorem leech_longTriangle_shape_coW2 :
    ∃ α β γ : MGriess, IsLongTriangle tGriess {α, β, γ} ∧ α * β * γ = xGriess ∧
      ∃ (N : Subgroup ↥(pointStab ({α, β, γ} : Set MGriess))) (_ : N.Normal)
        (N₀ : Subgroup ↥(pointStab ({α, β, γ} : Set MGriess))) (_ : N₀.Normal), N₀ ≤ N ∧
        IsElementaryAbelian 2 N₀ ∧ Nat.card N₀ = 2 ^ 3 ∧
        IsElementaryAbelian 2 (N ⧸ N₀.subgroupOf N) ∧ Nat.card N = 2 ^ (3 + 20) ∧
        Nonempty (↥(pointStab ({α, β, γ} : Set MGriess)) ⧸ N ≃* ↥(Kstab Co2.v0 ⊓ Kstab coW2)) :=
  leech_longTriangle_shape coW2 coW2_mem_shortSet v0_add_coW2_mem_shortSet

theorem leech_longTriangle_pCore_coW2
    (hX : ∀ P : Subgroup ↥(Kstab Co2.v0 ⊓ Kstab coW2), P.Normal → IsPGroup 2 P → P = ⊥) :
    ∃ α β γ : MGriess, IsLongTriangle tGriess {α, β, γ} ∧ α * β * γ = xGriess ∧
      ∃ (N : Subgroup ↥(pointStab ({α, β, γ} : Set MGriess))) (_ : N.Normal)
        (N₀ : Subgroup ↥(pointStab ({α, β, γ} : Set MGriess))) (_ : N₀.Normal), N₀ ≤ N ∧
        IsElementaryAbelian 2 N₀ ∧ Nat.card N₀ = 2 ^ 3 ∧
        IsElementaryAbelian 2 (N ⧸ N₀.subgroupOf N) ∧ Nat.card N = 2 ^ (3 + 20) ∧
        Nonempty (↥(pointStab ({α, β, γ} : Set MGriess)) ⧸ N ≃* ↥(Kstab Co2.v0 ⊓ Kstab coW2)) ∧
        pCore 2 ↥(pointStab ({α, β, γ} : Set MGriess)) = N :=
  leech_longTriangle_pCore coW2 coW2_mem_shortSet v0_add_coW2_mem_shortSet hX

end CFSG.Monster.Existence
