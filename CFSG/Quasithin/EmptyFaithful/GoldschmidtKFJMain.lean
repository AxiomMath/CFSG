module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFJInv
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFSevenFin
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFResidue

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.ComponentClassification CFSG.ComponentClassification.J2Cover
  CFSG.LocalAnalysis.ComponentInitial

theorem nonsolv_of_isSporadic_J2
    {L₂ : Type} [Group L₂] [Finite L₂] (h : IsSporadic .J2 (L₂ ⧸ Subgroup.center L₂))
    (u : MulAut L₂) (hu : u * u = 1) : ¬ Group.IsSolvable ↥(SBd18.fixedSub u) := by
  obtain ⟨e0⟩ := h
  apply not_isSolvable_fixedSub_of_quotient
  apply not_isSolvable_fixedSub_of_autTransfer (e0.trans nativeEquivP)
  apply not_isSolvable_fixedSub_of_sq_P
  rw [← map_mul, ← map_mul, hu, map_one, map_one]

theorem input15338NonsolvJ_native :
    Input15338NonsolvJ := by
  intro L₂ _ _ _ h u hu
  rcases h with h | h
  · exact nonsolv_of_isSporadic_J2 h u hu
  · exact nonsolv_of_isPSL_three_seven h u hu

end CFSG.Quasithin.SBd19F
