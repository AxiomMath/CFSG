module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin.RonanE42

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3
open scoped commutatorElement

section TwoQuot

variable {Q : Type*} [Group Q] [Finite Q]

theorem isComponent_toGW' {Γ : Type*} [Group Γ] {L : Subgroup Γ} (hL : CFSG.IsComponent L) :
    CFSG.GorensteinWalter.IsComponentOf L ⊤ := by
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.1.2.1
  exact ⟨le_top, hL.2.subgroupOf,
    (QuotientGroup.mk_surjective (s := Subgroup.center ↥L)).nontrivial,
    Group.isPerfect_def.mp hL.1.1, hL.1.2.1⟩

theorem isComponent_commute_of_ne' {Γ : Type*} [Group Γ] [Finite Γ] {L₁ L₂ : Subgroup Γ}
    (h₁ : CFSG.IsComponent L₁) (h₂ : CFSG.IsComponent L₂) (hne : L₁ ≠ L₂) {a b : Γ}
    (ha : a ∈ L₁) (hb : b ∈ L₂) : a * b = b * a := by
  have h := CFSG.GorensteinWalter.component_commute_of_ne (isComponent_toGW' h₁)
    (isComponent_toGW' h₂) hne
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  exact ((Subgroup.mem_centralizer_iff.mp (h ha)) b hb).symm

end TwoQuot

end CFSG.Quasithin.RonanE42
