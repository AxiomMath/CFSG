module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.SemisimplePermDeg

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem.Nonsolvable

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {H : Type*} [Group H] [Finite H]

theorem deg_eq_permDeg_of_isSimpleGroup (J : Type*) [Group J] [Finite J] [IsSimpleGroup J]
    (hnc : ¬ IsMulCommutative J) : deg J = permDeg J := by
  have hrad : CFSG.solvableRadical J = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.solvableRadical J) with h | h
    · exact h
    · exfalso
      have hs : Group.IsSolvable (CFSG.solvableRadical J) := isSolvable_solvableRadical
      rw [h] at hs
      have : Group.IsSolvable J := isSolvable_of_mulEquiv (Subgroup.topEquiv (G := J))
      exact hnc (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr this))
  exact permDeg_congr
    ((QuotientGroup.quotientMulEquivOfEq hrad).trans QuotientGroup.quotientBot)

theorem deg_eq_sum_components (hK : oStar H = ⊤) :
    deg H = ∑ᶠ (J : Subgroup (H ⧸ CFSG.solvableRadical H))
      (_ : J ∈ lcalOf (H ⧸ CFSG.solvableRadical H)), deg J := by
  have hlayer : CFSG.layer (H ⧸ CFSG.solvableRadical H) = ⊤ := by
    have h := hK
    rw [oStar_eq_comap_layer] at h
    have h' := congrArg (Subgroup.map (QuotientGroup.mk' (CFSG.solvableRadical H))) h
    rwa [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h'
  have hss : IsSemisimple (⊤ : Subgroup (H ⧸ CFSG.solvableRadical H)) := by
    have h := isSemisimple_layer (solvableRadical_quotient (G := H))
    rwa [hlayer] at h
  have h1 : deg H = permDeg (H ⧸ CFSG.solvableRadical H) := rfl
  rw [h1, permDeg_eq_sum_lcalOf hss]
  refine finsum_congr fun J => finsum_congr fun hJ => ?_
  obtain ⟨-, hs, hnc⟩ := hJ
  exact (deg_eq_permDeg_of_isSimpleGroup J hnc).symm

end CFSG.SignalizerFunctorTheorem.McBride.Near
