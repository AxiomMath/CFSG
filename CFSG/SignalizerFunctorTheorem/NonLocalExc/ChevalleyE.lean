module

public import CFSG.SignalizerFunctorTheorem.NonLocalExc.HeisChevalley

public section

namespace CFSG.SignalizerFunctorTheorem.NonLocalExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SignalizerFunctorTheorem.CatalogBridge

variable {K : Type} [Field K] [Finite K]

theorem nonLocalized_E6
    (σ : K ≃+* K) :
    NonLocalized ((fixedFieldImage .E6 σ).subgroupOf (adjointGroup .E6 K)) :=
  nonLocalized_E (Or.inl rfl) heisFacts_E6
    (Finset.card_pos.1 (by rw [card_heisS_E6]; decide)) rank_add_rootCount_lt_E6 σ
    (isSimpleGroup_adjointGroup_of_quasisimple
      (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 _))

theorem nonLocalized_E7
    (σ : K ≃+* K) :
    NonLocalized ((fixedFieldImage .E7 σ).subgroupOf (adjointGroup .E7 K)) :=
  nonLocalized_E (Or.inr (Or.inl rfl)) heisFacts_E7
    (Finset.card_pos.1 (by rw [card_heisS_E7]; decide)) rank_add_rootCount_lt_E7 σ
    (isSimpleGroup_adjointGroup_of_quasisimple
      (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 _))

theorem nonLocalized_E8
    (σ : K ≃+* K) :
    NonLocalized ((fixedFieldImage .E8 σ).subgroupOf (adjointGroup .E8 K)) :=
  nonLocalized_E (Or.inr (Or.inr rfl)) heisFacts_E8
    (Finset.card_pos.1 (by rw [card_heisS_E8]; decide)) rank_add_rootCount_lt_E8 σ
    (isSimpleGroup_adjointGroup_of_quasisimple
      (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 _))

end CFSG.SignalizerFunctorTheorem.NonLocalExc
