module

public import CFSG.Monster.B.TwoA.Amalgam.CoverCount
public import CFSG.Monster.B.TwoA.Amalgam.CentralKernel

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.CosetBuilding

theorem chamberCS_adj_iff
    (i : Fin Tag.F4.rank) (c d : Chamber) :
    chamberCS.adj i c d ↔ chamberAdj i c d := Iff.rfl

abbrev coverRho :
    Eam →* chamberCS.typeAut := chamberRho chamberCS chamberCS_adj_iff

abbrev coverH :
    Subgroup chamberCS.typeAut := coverRho.range

abbrev coverHt :
    Subgroup (chamberCS.LiftPair baseChamber) :=
  chamberCS.liftSubgroup baseChamber coverH

abbrev coverK :
    Subgroup (chamberCS.LiftPair baseChamber) := chamberCS.pi2 baseChamber

theorem short_F4_universal_building_cover :
    (∃ δ : chamberCS.Cover baseChamber → chamberCS.Cover baseChamber → WeylGroup .F4,
      IsWeylDistanceBuilding (coxeterSystem .F4) δ ∧
      (∀ (i : Fin Tag.F4.rank) (A B : chamberCS.Cover baseChamber),
        (chamberCS.universalCover baseChamber).adj i A B ↔
          δ A B = 1 ∨ δ A B = (coxeterSystem .F4).simple i) ∧
      ∀ (i : Fin Tag.F4.rank) (A : chamberCS.Cover baseChamber),
        (panel (coxeterSystem .F4) δ i A).encard = if (i : ℕ) < 2 then 3 else 5) ∧
    (∀ (i : Fin Tag.F4.rank) (A : chamberCS.Cover baseChamber),
      ((chamberCS.universalCover baseChamber).residue {i} A).encard =
        if (i : ℕ) < 2 then 3 else 5) ∧
    Finite (chamberCS.Cover baseChamber) ∧
    Nat.card (chamberCS.Cover baseChamber) = 371231385525 ∧
    (∀ (g : Eam) (c : Chamber), ((coverRho g : chamberCS.typeAut) : Equiv.Perm Chamber) c =
      chamberMul c g⁻¹) ∧
    coverRho.ker = Subgroup.zpowers cE' ∧ Nat.card (Subgroup.zpowers cE') = 2 ∧
    Nonempty (Eam ⧸ Subgroup.zpowers cE' ≃* coverH) ∧
    Finite coverHt ∧ Finite coverK ∧ Odd (Nat.card coverK) ∧
    Nonempty (coverHt ⧸ coverK.subgroupOf coverHt ≃* coverH) ∧
    Nat.card coverHt = 153064959367549707878400 ∧
    Nat.card Bam = 824633720832 ∧
    Nat.card Eam * Nat.card coverK = 306129918735099415756800 ∧
    ((Pc 0).subgroupOf Eam).index * Nat.card coverK = 3968055 := by
  obtain ⟨-, hc, hker, -⟩ := short_F4_chamber_action_central_kernel
  exact universal_building_cover_of chamberCS chamberCS_adj_iff chamberCS_connected
    chamberCS_hpanel chamberCS_hres2 chamberCS_hres3 chamberCS_encard_panel (Pc_eq_iSup_Qam 0)
    mem_residue_chamberCS_iff hker hc

end CFSG.Monster.B.TwoA.Amalgam
