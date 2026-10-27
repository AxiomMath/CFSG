module

public import CFSG.Quasithin.Background.D1Statement

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type*} [Group G]

@[expose] def D15ConclAS [Finite G] (G₁ G₂ T V : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  ¬ V ≤ pCoreOf 2 G₂ ∨
  (qInt G₁ V hV ≤ 1 ∧ IsFFInt G₁ V hV) ∨
  IsDualFFInt G₁ V hV ∨
  (qInt G₁ V hV ≤ 2 ∧ (∀ x ∈ conjClosure V G₂, ∀ y ∈ conjClosure V G₂, x * y = y * x) ∧
    ∃ c : ℕ, 2 ≤ c ∧ IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) c) ∨
  (((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂).subgroupOf G₂).Normal ∧ IsElemAbelian 2 (conjClosure V G₂) ∧
    IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) 1 ∧
    ⁅conjClosure V G₂, twoResidual G₂⁆ ≤ centerOf (pCoreOf 2 G₂) ∧
    twoResidual G₂ = ⁅twoResidual G₂, thompsonJ (pCoreOf 2 G₁)⁆ ∧
    thompsonJ (pCoreOf 2 G₁) = thompsonJ T)

@[expose] def InputD15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (G₁ G₂ T V M₂ : Subgroup G) (h : D11Hyp G₁ G₂ T V M₂),
    D15ConclAS G₁ G₂ T V h.reduced.2.2.1

end CFSG.Quasithin.EmptyFaithfulMultiple
