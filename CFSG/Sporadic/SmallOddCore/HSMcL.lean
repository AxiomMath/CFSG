module

public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.Sporadic.SmallOddCore.McLAut

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Blueprint

theorem ctuc_hs_mcl_almost_simple_involution_centralizer_odd_core_trivial
    {X : Type*} [Group X]
    [Finite X] (S : Subgroup X) [S.Normal]
    (hS : Nonempty (S ≃* NativeSporadic.HS) ∨ Nonempty (S ≃* NativeSporadic.McL))
    (hC : centralizer (S : Set X) = ⊥) (t : X) (ht : orderOf t = 2) :
    CFSG.oddCore ↥(centralizer ({t} : Set X)) = ⊥ := by
  rcases hS with hS | hS
  · exact hs_almost_simple_odd_core S hS hC t ht
  · exact mcl_almost_simple_odd_core S hS hC t ht

theorem ctu_catalog_hs_mcl_almost_simple_odd_core_vanishing
    {X : Type*} [Group X] [Finite X]
    (hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (hJ : Nonempty (CFSG.generalizedFitting X ≃* NativeSporadic.HS) ∨
      Nonempty (CFSG.generalizedFitting X ≃* NativeSporadic.McL))
    (z : X) (hz : orderOf z = 2) : CFSG.oddCore ↥(centralizer ({z} : Set X)) = ⊥ := by
  have : (CFSG.generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  have hnab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a := by
    rcases hJ with hJ | hJ
    · obtain ⟨ψ⟩ := hJ
      obtain ⟨a, b, hab⟩ := hs_not_comm
      refine ⟨ψ.symm a, ψ.symm b, fun h => hab ?_⟩
      have := congrArg ψ h
      simpa only [map_mul, MulEquiv.apply_symm_apply] using this
    · obtain ⟨ψ⟩ := hJ
      obtain ⟨a, b, hab⟩ := mcl_not_comm
      refine ⟨ψ.symm a, ψ.symm b, fun h => hab ?_⟩
      have := congrArg ψ h
      simpa only [map_mul, MulEquiv.apply_symm_apply] using this
  exact ctuc_hs_mcl_almost_simple_involution_centralizer_odd_core_trivial _ hJ
    (centralizer_generalizedFitting_eq_bot hF hnab) z hz

end CFSG.Sporadic.SmallOddCore
