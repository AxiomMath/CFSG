module

public import CFSG.Quasithin.Background.TwoReduced

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type*} [Group G]

@[expose] def omegaOneOf (X : Subgroup G) : Subgroup G := Subgroup.closure {x | x ∈ X ∧ x ^ 2 = 1}

@[expose] def omegaOneCenterOf (X : Subgroup G) : Subgroup G := omegaOneOf (centerOf X)

theorem omegaOneCenterOf_eq (T : Subgroup G) :
    omegaOneCenterOf T = quasithinOmegaOneCenter T := rfl

@[expose] def IsMaxElemAbelian (H A : Subgroup G) : Prop :=
  A ≤ H ∧ IsElemAbelian 2 A ∧
    ∀ B : Subgroup G, B ≤ H → IsElemAbelian 2 B → Nat.card B ≤ Nat.card A

@[expose] def thompsonJ (H : Subgroup G) : Subgroup G :=
  ⨆ (A : Subgroup G) (_ : IsMaxElemAbelian H A), A

@[expose] def baum (H : Subgroup G) : Subgroup G :=
  H ⊓ Subgroup.centralizer (omegaOneCenterOf (thompsonJ H) : Set G)

@[expose] def IsFFOffender (H V A : Subgroup G) : Prop :=
  IsMaxElemAbelian H A ∧ ¬ A ≤ Subgroup.centralizer (V : Set G)

@[expose] noncomputable def conjAct (V : Subgroup G) :
    Subgroup.normalizer (V : Set G) →* MulAut V :=
  (V.normalizerMonoidHom).comp (Subgroup.inclusion le_rfl)

@[expose] noncomputable def autOn (H V : Subgroup G) : Subgroup (MulAut V) :=
  ((H.subgroupOf (Subgroup.normalizer (V : Set G))).map (conjAct V))

@[expose] def CGS (S : Subgroup G) : Subgroup G :=
  ⨆ (C : Subgroup G) (_ : C ≤ S) (_ : C ≠ ⊥) (_ : (C.subgroupOf S).Characteristic),
    Subgroup.normalizer (C : Set G)

end CFSG.Quasithin
