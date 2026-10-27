module

public import CFSG.Sporadic.HeldB.OuterFixed
public import CFSG.Sporadic.HeldB.InnerClass

public noncomputable section

namespace CFSG.Sporadic.HeldB

open CFSG.ComponentClassification.FixedCommutingProduct

theorem ctbh_all_involution_automorphism_fixed_p_components
    {S : Type*} [Group S]
    (hS : Nonempty (S ≃* Blueprint.NativeSporadic.He)) (α : MulAut S) (hα : orderOf α = 2)
    (L : Subgroup (fixedSubgroup α)) (hL : CFSG.IsPComponent 2 L) : CFSG.IsQuasisimple L :=
  fixed_pComponent_quasisimple_of_cases heP_center_eq_bot
    (fun t ht => by
      rw [oddCore_eq_pPrimeCore_two']
      exact ctbhi_held_inner_involution_centralizers_odd_core.2 t ht)
    (fun β hβ hinn => ctbh_outer_involution_fixed_p_components (Or.inl ⟨MulEquiv.refl heP⟩) β hβ
      hinn) (hS.some.trans heEquivP) α hα L hL

end CFSG.Sporadic.HeldB
