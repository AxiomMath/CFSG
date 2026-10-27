module

public import CFSG.Sporadic.Schreier.J4SOdd1771
public import CFSG.Sporadic.Schreier.J4SOdd276

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4

theorem CTU_J4_full_group_inner_involution_odd_core
    {X : Type*} [Group X] [Finite X]
    (hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (hnab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a)
    (ψ : CFSG.generalizedFitting X ≃* J) (t : CFSG.generalizedFitting X)
    (ht : orderOf (t : X) = 2) :
    CFSG.oddCore (Subgroup.centralizer ({(t : X)} : Set X)) = ⊥ := by
  have ho : orderOf (ψ t) = 2 := by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact ht
  obtain ⟨-, g, hg⟩ := CTU_J4_every_inner_involution_conjugate_into_local_binary_subgroup _ ho
  rcases hg with hg | hg
  · have h := @eq_conj_form J (Subgroup.toGroup J) _ _ _ hg
    exact (CTU_J4_full_group_local_1771_orbit_involution_odd_core hF hnab ψ t
      ⟨g, 1, K.one_mem, h⟩).2
  · have h := @eq_conj_form J (Subgroup.toGroup J) _ _ _ hg
    exact (CTU_J4_full_group_local_276_orbit_involution_odd_core hF hnab ψ t
      ⟨g, 1, K.one_mem, h⟩).2

end CFSG.Sporadic.J4Schreier
