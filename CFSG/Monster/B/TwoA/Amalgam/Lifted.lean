module

public import CFSG.Monster.B.TwoA.Amalgam.Cover
public import CFSG.Monster.B.TwoA.Amalgam.LiftedMain

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.CosetBuilding

theorem short_F4_lifted_parabolic_stabilizers
    (a : chamberCS.Cover baseChamber)
    (ha : chamberCS.coverProj baseChamber a = baseChamber) :
    (∀ i : Fin 4, IsResidueIso (chamberCS.universalCover baseChamber) chamberCS
        (chamberCS.coverProj baseChamber) (typesOff i) a ∧
      chamberCS.residue (typesOff i) baseChamber =
        chamberOf '' ((Pc i).subgroupOf Eam : Set Eam)) ∧
    (∀ i : Fin 4, ∃ e : liftParabolic chamberCS chamberCS_adj_iff a i ≃*
        (Pc i).subgroupOf Eam ⧸ cIn ((Pc i).subgroupOf Eam),
      ∀ z g, e z = QuotientGroup.mk g ↔
        chamberCS.liftProj baseChamber (z : chamberCS.LiftPair baseChamber) = coverRho g) ∧
    (∃ e : liftBorel chamberCS chamberCS_adj_iff a ≃*
        Bam.subgroupOf Eam ⧸ cIn (Bam.subgroupOf Eam),
      ∀ z g, e z = QuotientGroup.mk g ↔
        chamberCS.liftProj baseChamber (z : chamberCS.LiftPair baseChamber) = coverRho g) ∧
    (∀ i j : Fin 4, i ≠ j →
      ∃ e : ↥(liftParabolic chamberCS chamberCS_adj_iff a i ⊓
          liftParabolic chamberCS chamberCS_adj_iff a j) ≃*
          (Pc i ⊓ Pc j).subgroupOf Eam ⧸ cIn ((Pc i ⊓ Pc j).subgroupOf Eam),
        ∀ z g, e z = QuotientGroup.mk g ↔
          chamberCS.liftProj baseChamber (z : chamberCS.LiftPair baseChamber) = coverRho g) ∧
    (∀ l : Fin 4,
      ∃ e : ↥(⨅ (i : Fin 4) (_ : i ≠ l), liftParabolic chamberCS chamberCS_adj_iff a i) ≃*
          (Qam l).subgroupOf Eam ⧸ cIn ((Qam l).subgroupOf Eam),
        ∀ z g, e z = QuotientGroup.mk g ↔
          chamberCS.liftProj baseChamber (z : chamberCS.LiftPair baseChamber) = coverRho g) ∧
    (⨅ i : Fin 4, liftParabolic chamberCS chamberCS_adj_iff a i) =
      liftBorel chamberCS chamberCS_adj_iff a ∧
    (∃ θ : liftParabolic chamberCS chamberCS_adj_iff a 0 →* Unitary.SigmaU6,
      Function.Surjective θ ∧
      (∀ (z : liftParabolic chamberCS chamberCS_adj_iff a 0) (g : Pc 0),
        chamberCS.liftProj baseChamber (z : chamberCS.LiftPair baseChamber) =
          coverRho (Subgroup.inclusion (Pc_le_Eam 0) g) → θ z = rhoP1 g) ∧
      (∀ z, θ z = 1 ↔ ∃ n : Eam, (n : Dfull) ∈ Nc 0 ∧
        chamberCS.liftProj baseChamber (z : chamberCS.LiftPair baseChamber) = coverRho n) ∧
      (∀ z, θ z = 1 →
        (z : chamberCS.LiftPair baseChamber) ∈ liftBorel chamberCS chamberCS_adj_iff a) ∧
      ∃ e : ↥(θ.ker.map (liftParabolic chamberCS chamberCS_adj_iff a 0).subtype) ≃*
          (Nc 0).subgroupOf Eam ⧸ cIn ((Nc 0).subgroupOf Eam),
        ∀ z g, e z = QuotientGroup.mk g ↔
          chamberCS.liftProj baseChamber (z : chamberCS.LiftPair baseChamber) = coverRho g) ∧
    (∃ θ : liftParabolic chamberCS chamberCS_adj_iff a 3 →*
        TauCeti.QuadraticMap.orthogonalGroup qForm,
      Function.Surjective θ ∧
      (∀ (z : liftParabolic chamberCS chamberCS_adj_iff a 3) (g : P4),
        chamberCS.liftProj baseChamber (z : chamberCS.LiftPair baseChamber) =
          coverRho (Subgroup.inclusion (Pc_le_Eam 3 : P4 ≤ Eam) g) → θ z = p4Proj g) ∧
      (∀ z, θ z = 1 ↔ ∃ n : Eam, (n : Dfull) ∈ Lgrp ∧
        chamberCS.liftProj baseChamber (z : chamberCS.LiftPair baseChamber) = coverRho n) ∧
      (∀ z, θ z = 1 →
        (z : chamberCS.LiftPair baseChamber) ∈ liftBorel chamberCS chamberCS_adj_iff a) ∧
      ∃ e : ↥(θ.ker.map (liftParabolic chamberCS chamberCS_adj_iff a 3).subtype) ≃*
          Lgrp.subgroupOf Eam ⧸ cIn (Lgrp.subgroupOf Eam),
        ∀ z g, e z = QuotientGroup.mk g ↔
          chamberCS.liftProj baseChamber (z : chamberCS.LiftPair baseChamber) = coverRho g) := by
  exact lifted_parabolic_stabilizers_of (X := chamberCS) (hX := chamberCS_adj_iff)
    chamberCS_connected chamberCS_hpanel chamberCS_hres2 chamberCS_hres3 chamberCS_encard_panel
    mem_residue_chamberCS_iff Pc_eq_iSup_Qam short_F4_chamber_action_central_kernel.2.2.1 a ha

end CFSG.Monster.B.TwoA.Amalgam
