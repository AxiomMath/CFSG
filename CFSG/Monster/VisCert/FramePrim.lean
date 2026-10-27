module

public import CFSG.Monster.VisCert.FrameOrbit

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.VisCert

open CFSG.Monster CFSG.Monster.SpinLattice CFSG.Monster.Visible

theorem visible_frame_primitivity
    (hstab : ∀ u ∈ Hvis, u • twoΩCls = twoΩCls ↔ u ∈ Nvis) :
    MulAction.IsPreprimitive Hvis deltaSub ∧
    ∀ j : Fin 5, (∀ g ∈ ambientWords[(j : ℕ)]!, g < 15) ∧
      tAmb j = wordGL ambientWords[(j : ℕ)]! ∧ tAmb j • twoΩCls = frameRep j.succ ∧
      Nvis ⊔ Subgroup.zpowers (tAmb j) = Hvis :=
  ⟨isPreprimitive frameDelta_eq_iUnion hstab, fun j => ⟨(ambient_spec j).1, rfl, tAmb_smul j,
    fusionGroup_eq_Hvis frameDelta_eq_iUnion hstab j⟩⟩

theorem orbit_fusionGroup_eq (j : Fin 5) :
    MulAction.orbit (↥(Nvis ⊔ Subgroup.zpowers (tAmb j))) twoΩCls = frameDelta :=
  orbit_fusionGroup frameDelta_eq_iUnion j

theorem isPretransitive_Hvis_deltaSub :
    MulAction.IsPretransitive Hvis deltaSub :=
  isPretransitive frameDelta_eq_iUnion

end CFSG.Monster.VisCert
