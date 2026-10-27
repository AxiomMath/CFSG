module

public import CFSG.Sporadic.ThSchreier.InnerInvolution
public import CFSG.Sporadic.Th.Max3.AllConjFinal
public import CFSG.Milestones.CLS_involution_centralizers_characteristic_two_transfer

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Assembly.Dichotomy

theorem thInv_props
    {u : J} (hu : orderOf u = 2) :
    dichotomyCharP 2 (Subgroup.centralizer {u}) ∧ CFSG.oddCore (Subgroup.centralizer {u}) = ⊥ :=
  charP_oddCore_J centralizer_a_eq_M_kernel all_involutions_conjugate hu

theorem invProps_transfer {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    (e : G ≃* G')
    (h : ∀ u : G, orderOf u = 2 → dichotomyCharP 2 (Subgroup.centralizer {u}) ∧
      CFSG.oddCore (Subgroup.centralizer {u}) = ⊥) :
    ∀ u : G', orderOf u = 2 → dichotomyCharP 2 (Subgroup.centralizer {u}) ∧
      CFSG.oddCore (Subgroup.centralizer {u}) = ⊥ := by
  intro u hu
  have hv : orderOf (e.symm u) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hu
  have f := centralizerEquiv e (e.symm u)
  rw [e.apply_symm_apply] at f
  obtain ⟨h1, h2⟩ := h _ hv
  exact ⟨charP_of_equiv f h1, oddCore_eq_bot_of_equiv f h2⟩

theorem finite_J :

    Finite J := Nat.finite_of_card_ne_zero (by rw [natCard_J]; norm_num)

theorem finite_Th :
    Finite Blueprint.NativeSporadic.Th :=
  @Finite.of_equiv _ _ finite_J thEquivJ.symm.toEquiv

theorem thInv_props_all :
    ∀ u : J, orderOf u = 2 →
    dichotomyCharP 2 (Subgroup.centralizer {u}) ∧ CFSG.oddCore (Subgroup.centralizer {u}) = ⊥ :=
  fun _ hu => thInv_props hu

theorem thInv_props_Th :
    ∀ u : Blueprint.NativeSporadic.Th, orderOf u = 2 →
    dichotomyCharP 2 (Subgroup.centralizer {u}) ∧ CFSG.oddCore (Subgroup.centralizer {u}) = ⊥ :=
  @invProps_transfer J Blueprint.NativeSporadic.Th _ Units.instGroup finite_J finite_Th
    thEquivJ.symm thInv_props_all

theorem thInv_props_of_equiv
    {K : Type*} [Group K] [Finite K]
    (e : K ≃* Blueprint.NativeSporadic.Th) {u : K} (hu : orderOf u = 2) :
    dichotomyCharP 2 (Subgroup.centralizer {u}) ∧ CFSG.oddCore (Subgroup.centralizer {u}) = ⊥ := by
  have h : ∀ v : K, orderOf v = 2 → dichotomyCharP 2 (Subgroup.centralizer {v}) ∧
      CFSG.oddCore (Subgroup.centralizer {v}) = ⊥ :=
    @invProps_transfer Blueprint.NativeSporadic.Th K Units.instGroup _ finite_Th _ e.symm
      thInv_props_Th
  exact h u hu

theorem ctuc_Th_inner_involution_centralizers_characteristic_two :
    (∀ u : J, orderOf u = 2 → dichotomyCharP 2 (Subgroup.centralizer {u}) ∧
      CFSG.oddCore (Subgroup.centralizer {u}) = ⊥) ∧ CFSG.Assembly.IsCharTwoType J ∧
    ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* Blueprint.NativeSporadic.Th) →
      (∀ u : K, orderOf u = 2 → dichotomyCharP 2 (Subgroup.centralizer {u}) ∧
        CFSG.oddCore (Subgroup.centralizer {u}) = ⊥) ∧ CFSG.Assembly.IsCharTwoType K := by
  have hfinJ : Finite J := finite_J
  refine ⟨fun u hu => thInv_props hu,
    CFSG.Milestones.cls_involution_centralizers_characteristic_two_transfer J
      fun t ht => (thInv_props ht).1, fun K _ _ ⟨e⟩ => ?_⟩
  exact ⟨fun u hu => thInv_props_of_equiv e hu,
    CFSG.Milestones.cls_involution_centralizers_characteristic_two_transfer K
      fun t ht => (thInv_props_of_equiv e ht).1⟩

end CFSG.Sporadic.ThSchreier
