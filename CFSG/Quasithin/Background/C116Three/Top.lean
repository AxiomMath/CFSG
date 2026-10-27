module

public import CFSG.Quasithin.Background.C116Three.Swap
public import CFSG.Quasithin.EmptyFaithful.S151S4F

public section

namespace CFSG.Quasithin.C116Three

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

@[expose] def FixedVector3Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T V L : Subgroup G), CharTwo H → IsTwoReducedIn H V →
    IsSylowTwoOf T H → IsSQTKTC H → L ∈ cComp H →
    (∃ (Q : Type) (_ : Group Q) (φ : ↥L →* Q), Function.Surjective φ ∧
      φ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf L ∧ CFSG.IsQuasisimple Q) →
    ¬ ⁅L, thompsonJ T⁆ ≤ Subgroup.centralizer (V : Set G) →
    ¬ T ≤ Subgroup.normalizer (L : Set G) →
      ∃ u ∈ V, (∃ l ∈ L, l * u ≠ u * l) ∧ (∀ j ∈ thompsonJ T, j * u = u * j) ∧
        ∀ x ∈ T, x ∉ Subgroup.normalizer (L : Set G) →
          ∀ l ∈ L, (x * l * x⁻¹) * u = u * (x * l * x⁻¹)

theorem le_of_isTwoReducedIn {G : Type} [Group G] [Finite G] {H T V : Subgroup G}
    (hV : IsTwoReducedIn H V) (hT : IsSylowTwoOf T H) : V ≤ T :=
  (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hV.1 hV.2.1
    (B2F.isPGroup_of_isElemAbelian hV.2.2.1)).trans (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hT)

theorem theoremC116Three_of_fixedVector (h : FixedVector3Statement) : TheoremC116Three := by
  intro G _ _ H T V L hH hV hT hSQ hL hq hnJ
  by_cases hTN : T ≤ Subgroup.normalizer (L : Set G)
  · exact (C1GN.baum_le T).trans hTN
  · exact baum_le_normalizer_of_fixedVector hV.2.2.1 (le_of_isTwoReducedIn hV hT)
      (h G H T V L hH hV hT hSQ hL hq hnJ hTN)

end CFSG.Quasithin.C116Three
