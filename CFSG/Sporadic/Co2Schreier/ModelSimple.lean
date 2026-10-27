module

public import CFSG.Sporadic.Co2Schreier.OddCore
public import CFSG.Sporadic.Co2Schreier.FullAut
public import CFSG.Sporadic.FischerOddCore.Fi23AlmostSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUSporadic

public noncomputable section

namespace CFSG.Sporadic.Co2Schreier

theorem CTUC_Co2_model_simple_generalized_fitting_centralizer_exclusion
    {X : Type*} [Group X]
    [Finite X] (hs : IsSimpleGroup (CFSG.generalizedFitting X))
    (hnc : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a)
    (e : CFSG.generalizedFitting X ≃* CFSG.Blueprint.NativeSporadic.Co2) :
    CFSG.generalizedFitting X = ⊤ ∧ ∀ a : X, orderOf a = 2 →
      CFSG.oddCore ↥(Subgroup.centralizer ({a} : Set X)) = ⊥ := by
  have hZF : Subgroup.center (CFSG.generalizedFitting X) = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center (CFSG.generalizedFitting X)) with
      h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have ha : a ∈ Subgroup.center (CFSG.generalizedFitting X) := h ▸ Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.1 ha b).symm
  have hZ : Subgroup.center CFSG.Blueprint.NativeSporadic.Co2 = ⊥ :=
    CFSG.Sporadic.FischerOddCore.center_eq_bot_of_mulEquiv e.symm hZF
  exact CFSG.Sporadic.FischerOddCore.generalized_fitting_of_inner hZ
    (CTUC_Co2_full_automorphisms_inner_model _ (MulEquiv.refl _))
    (fun t ht => CTUC_Co2_all_involution_centralizers_odd_core_free_Co2 t ht) ⟨e⟩

theorem sporadicOddCoreFree_Co2 :
    CFSG.ComponentClassification.CatalogueU.SporadicOddCoreFree .Co2 :=
  fun _ _ _ hF hnc ⟨e⟩ t ht =>
    (CTUC_Co2_model_simple_generalized_fitting_centralizer_exclusion hF hnc e).2 t ht

end CFSG.Sporadic.Co2Schreier
