module

public import CFSG.Quasithin.Background.G11Basic
public import CFSG.Quasithin.EmptyFaithful.SzN28S8Mod
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLinearBinary

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN29

open CFSG.Quasithin.G11

theorem isPerfect_linearEquiv {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    (hU : 3 ≤ Module.finrank (ZMod 2) U) : Group.IsPerfect (U ≃ₗ[ZMod 2] U) := by
  have hfin : Module.Finite (ZMod 2) U := Module.finite_of_finrank_pos (by omega)
  let n := Module.finrank (ZMod 2) U
  let b : Module.Basis (Fin n) (ZMod 2) U := Module.finBasisOfFinrankEq (ZMod 2) U rfl
  let e : GL (Fin n) (ZMod 2) ≃* (U ≃ₗ[ZMod 2] U) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) U)
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le hU
  exact Group.IsPerfect.ofSurjective
    (f := ((CFSG.QuasithinUnique.Setup.Family.slEquivGL n).trans e).toMonoidHom)
    (MulEquiv.surjective _)

theorem not_isSolvable_linearEquiv {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    (hU : 3 ≤ Module.finrank (ZMod 2) U) : ¬ Group.IsSolvable (U ≃ₗ[ZMod 2] U) := by
  intro hs
  have hperf := isPerfect_linearEquiv hU
  have hfin : Module.Finite (ZMod 2) U := Module.finite_of_finrank_pos (by omega)
  have hnt : Nontrivial (U ≃ₗ[ZMod 2] U) := by
    have hpos : 0 < Module.finrank (ZMod 2) U := by omega
    obtain ⟨u, hu⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
    obtain ⟨g, hg⟩ := SzN28.exists_linearEquiv_moves (by omega) hu
    exact ⟨⟨g, 1, fun h => hg (by rw [h]; rfl)⟩⟩
  obtain ⟨k, hk⟩ := hs.solvable
  rw [Group.IsPerfect.derivedSeries_eq_top] at hk
  exact top_ne_bot hk

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem false_of_solvable_autAll {K : Subgroup (GLV V)} {U : Submodule (ZMod 2) V}
    (hK : Group.IsSolvable ↥K) (hI : Invariant K U) (hall : AutAll K U)
    (hU : 3 ≤ Module.finrank (ZMod 2) U) : False := by
  have hsurj : Function.Surjective (restrictHom K U hI) := by
    intro g
    obtain ⟨k, hk, hkg⟩ := hall g
    refine ⟨⟨k, hk⟩, ?_⟩
    ext i
    exact hkg i
  have : Group.IsSolvable (U ≃ₗ[ZMod 2] U) := Group.isSolvable_of_surjective hsurj
  exact not_isSolvable_linearEquiv hU this

end CFSG.Quasithin.SzN29
