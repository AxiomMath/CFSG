module

public import CFSG.Quasithin.EmptyFaithful.S153EInputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

section JStructure

variable {G : Type} [Group G] [Finite G]

abbrev Jgp153 (T M V₁ Mc : Subgroup G) (y : G) : Subgroup G :=
  UH153 T M V₁ Mc ⊔ conjSubgroup (UH153 T M V₁ Mc) y

structure JStruct56 (T Mc M V₁ : Subgroup G) (N₁ : Subgroup (MulAut ↥(VZ T M))) (y : G) : Prop where
  V0_eq : V0gp153 T Mc M V₁ N₁ =
    quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y
  V0_card : Nat.card ↥(quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y) = 4
  nat : ∃ r : ℕ, IsSumOfNatSL2ModulesN153 r (Jgp153 T M V₁ Mc y) (pCoreOf 2 (Jgp153 T M V₁ Mc y))
    (pCoreOf 2 (Jgp153 T M V₁ Mc y)) (Egp153 T M V₁ Mc y)
  R_eq : pCoreOf 2 (Jgp153 T M V₁ Mc y) = Fgp153 T M V₁ Mc y ⊔ Xgp153 T M V₁ Mc y
  R_cent : pCoreOf 2 (Jgp153 T M V₁ Mc y) = Jgp153 T M V₁ Mc y ⊓
    Subgroup.centralizer ((quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y : Subgroup G) : Set G)
  E_comm : ⁅Egp153 T M V₁ Mc y, Jgp153 T M V₁ Mc y⁆ ≤
    quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y
  normal_E : Subgroup.normalizer
      ((quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y : Subgroup G) : Set G) ≤
    Subgroup.normalizer ((Egp153 T M V₁ Mc y : Subgroup G) : Set G)

end JStructure

@[expose] def Input15356J : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ : Subgroup G) (t : G)
    (cx : Ctx15350 T Mc M V₁ V₂ t) (N₁ N₂ : Subgroup (MulAut ↥(VZ T M))) (g : G) (s : ℕ),
    Chain15355 cx N₁ N₂ g s → ∀ y : G,
      (y ∈ Yi153 T Mc M V₁ N₁ ∧ y ∉ pCoreOf 2 (Yi153 T Mc M V₁ N₁)) →
        JStruct56 T Mc M V₁ N₁ y

end CFSG.Quasithin
