module

public import CFSG.Sporadic.FischerOddCore.Fi22AlmostSimple
public import CFSG.GroupTheory.LocalCores.Components

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer

theorem center_fi22P :
    Subgroup.center fi22P = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h : (z : Equiv.Perm (Fin 3510)) ∈
      Subgroup.centralizer (fi22P : Set (Equiv.Perm (Fin 3510))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)
  rw [fi22P_centralizer, Subgroup.mem_bot] at h
  exact Subgroup.mem_bot.2 (Subtype.ext h)

theorem CTUC_Fi22_generalized_Fitting_involution_centralizer_odd_core_trivial
    {X : Type*}
    [Group X] [Finite X] (_hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (hJ : Nonempty (CFSG.generalizedFitting X ≃* Blueprint.NativeSporadic.Fi22)) (t : X)
    (ht : orderOf t = 2) : CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set X)) = ⊥ := by
  have : (CFSG.generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  have hZ : Subgroup.center (CFSG.generalizedFitting X) = ⊥ :=
    center_eq_bot_of_mulEquiv (hJ.some.trans fi22PermEquiv) center_fi22P
  exact CTUC_Fi22_almost_simple_involution_centralizer_odd_core_trivial _ hJ
    (centralizer_generalizedFitting_eq_bot_of_center hZ) t ht

end CFSG.Sporadic.FischerOddCore
