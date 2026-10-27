module

public import CFSG.Open.SignalizerFunctorTheoremMilestoneDefs
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.KGroup
import CFSG.SignalizerFunctorTheorem.McBride.Final

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem signalizer_functor_theorem_of_catalogHypothesisA
    (G : Type) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (hCat : CatalogHypothesisA p) (k : ℕ) (hk : 1 ≤ k)
    (A : Subgroup G) (hA : IsElemAbelian p A) (hrank : p ^ (k + 2) ≤ Nat.card A)
    (Θ : Subgroup G → Subgroup G)
    (hcent : ∀ S ∈ signalizerFunctorEk p k A, Θ S ≤ Subgroup.centralizer (S : Set G))
    (hcop : ∀ S ∈ signalizerFunctorEk p k A, Nat.Coprime p (Nat.card (Θ S)))
    (hinv : ∀ S ∈ signalizerFunctorEk p k A, A ≤ Subgroup.normalizer (Θ S : Set G))
    (hbal : ∀ S ∈ signalizerFunctorEk p k A, ∀ S' ∈ signalizerFunctorEk p k A,
      Θ S ⊓ Subgroup.centralizer (S' : Set G) ≤ Θ S')
    (hK : ∀ S ∈ signalizerFunctorEk p k A, CFSG.SectionRank.IsKGroupCat ↥(Θ S)) :
    let W : Subgroup G := ⨆ (S : Subgroup G) (_ : S ∈ signalizerFunctorEk p k A), Θ S
    (Nat.Coprime p (Nat.card W) ∧ A ≤ Subgroup.normalizer (W : Set G)) ∧
    (∀ S ∈ signalizerFunctorEk p k A, W ⊓ Subgroup.centralizer (S : Set G) = Θ S) ∧
    (∀ Y : Subgroup G, A ≤ Subgroup.normalizer (Y : Set G) →
      (∀ S ∈ signalizerFunctorEk p k A, Y ⊓ Subgroup.centralizer (S : Set G) ≤ Θ S) →
      Y ≤ W) ∧
    ((∀ S ∈ signalizerFunctorEk p k A, Group.IsSolvable (Θ S)) → Group.IsSolvable W) :=
  CFSG.SignalizerFunctorTheorem.signalizer_functor_theorem_of_rankOne
    CFSG.SignalizerFunctorTheorem.solvableRankOneTheorem
    CFSG.SignalizerFunctorTheorem.McBride.mcBrideRankOneTheorem
    G p hp k hk A hA hrank Θ hcent hcop hinv hbal
    fun S hS => hypothesisB_of_isKGroupCat hp hCat (hcop S hS) (hK S hS)

end CFSG.SignalizerFunctorTheorem.CatalogBridge
