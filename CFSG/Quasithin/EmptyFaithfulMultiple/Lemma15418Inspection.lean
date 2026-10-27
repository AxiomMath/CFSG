module

public import CFSG.Quasithin.Background.F6Solvable
public import CFSG.LocalAnalysis.QuasithinUnique.BenderInterfaces

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

structure InspectionData15418 {G : Type} [Group G] [Finite G] (I G₁ G₂ S T Z : Subgroup G) :
    Prop where
  sqtk : CFSG.SectionRank.IsSQTKCat ↥I
  triple : F6.IsGoldschmidtTripleIn I G₁ G₂
  inf_eq : G₁ ⊓ G₂ = S
  pCoreOf_ne : pCoreOf 2 G₁ ≠ pCoreOf 2 G₂
  oddCoreIn_eq_bot : oddCoreIn I = ⊥
  le : Z ≤ S
  card : Nat.card Z = 4
  sq_eq_one : ∀ z ∈ Z, z ^ 2 = 1
  charTwo_centralizer : ∀ z ∈ Z, z ≠ 1 → CharTwo (I ⊓ Subgroup.centralizer ({z} : Set G))
  centralizer_eq : I ⊓ Subgroup.centralizer (Z : Set G) = S
  component : ∀ L : Subgroup G, IsComponentIn L I → ∀ z ∈ Z, z ≠ 1 →
    ⁅L, Subgroup.zpowers z⁆ = L
  thompson₁ : ⁅oTwoUpper G₁, thompsonJ S⁆ = oTwoUpper G₁
  thompson₂ : ⁅oTwoUpper G₂, thompsonJ S⁆ = oTwoUpper G₂
  isPGroup : IsPGroup 2 T
  le_T : S ≤ T
  relIndex_eq_two : S.relIndex T = 2
  le_normalizer : T ≤ Subgroup.normalizer (G₁ : Set G)
  omegaOneCenter_le : quasithinOmegaOneCenter T ≤ Z
  rank : ∃ A : Subgroup G, A ≤ S ∧ IsElemAbelian 2 A ∧ Nat.card A = 2 ^ 5

@[expose] def Inspection15418 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I G₁ G₂ S T Z : Subgroup G),
    InspectionData15418 I G₁ G₂ S T Z → ⁅S, S⁆ ≤ pCoreOf 2 I

end CFSG.Quasithin.EmptyFaithfulMultiple
