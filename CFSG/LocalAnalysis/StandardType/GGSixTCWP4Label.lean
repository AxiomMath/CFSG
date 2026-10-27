module

public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly (LargeEvenLabel LargeEvenInLambda2 LargeEvenMarking LargeEvenHalfSplit)

theorem exists_labelIso_of_marking (hRig : GGLabelRigidInput) {Y : Type} [Group Y]
    {L : Subgroup Y} {Pr : LargeEvenLabel → Prop}
    (hmark : LargeEvenMarking ↥L fun lab _ _ _ _ _ => Pr lab) {lab : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 lab) (hlab : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L)) :
    ∃ lab', GGLabelIso lab lab' ∧ Pr lab' := by
  obtain ⟨lab', hΛ', hlab', R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hmark
  exact ⟨lab', hRig _ _ _ hΛ hΛ' hlab hlab', hP⟩

end CFSG.StandardType.TableCRes

end
