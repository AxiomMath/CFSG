module

public import CFSG.Quasithin.EmptyFaithful.S153Plus
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.EmptyFaithful.S153YCases

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

structure Ctx153 (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ : Subgroup G) (t : G) : Prop where
  hyp : Hyp153 G T Mc M
  decomp : Decomp153 T M V₁ V₂ t

section Vocabulary

variable {G : Type} [Group G]

abbrev ZS153 (T M V₁ : Subgroup G) : Subgroup G :=
  VZ T M ⊓ Subgroup.centralizer (Sgp153 T V₁ : Set G)

@[expose] def IsTotSingular153 (T M V₁ V₂ A : Subgroup G) : Prop :=
  A ≤ VZ T M ∧ A ⊓ V₁ = ⊥ ∧ A ⊓ V₂ = ⊥

@[expose] def IsHTM153 (T M H : Subgroup G) : Prop := InH T H ∧ ¬ H ≤ M

variable [Finite G]

@[expose] def Case157One (T Mc M : Subgroup G) : Prop :=
  pCoreOf 2 (Y153 Mc M) = Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) ∧
    IsElemAbelianOfRank 3 2 (OTwoQuot (Y153 Mc M))

@[expose] def Case157Two (T Mc M : Subgroup G) : Prop :=
  IsPOnePlusTwo 3 (OTwoQuot (Y153 Mc M)) ∧
    O2Z (Y153 Mc M) = Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G)

end Vocabulary

end CFSG.Quasithin
