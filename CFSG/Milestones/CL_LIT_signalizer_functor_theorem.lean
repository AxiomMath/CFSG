module

public import CFSG.Open.SignalizerFunctorTheoremMilestoneDefs
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
import CFSG.SignalizerFunctorTheorem.SolvableTheorem
import CFSG.SignalizerFunctorTheorem.CatalogBridge.Final
import CFSG.RankThree.PartOne.SPOR.OuterSimple
import CFSG.SignalizerFunctorTheorem.NonLocalExc.Chevalley
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

universe u v w

namespace CFSG.Open

theorem _root_.CFSG.Milestones.cl_lit_signalizer_functor_theorem_1
    (G : Type) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : 1 ≤ k)
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
  CFSG.SignalizerFunctorTheorem.CatalogBridge.signalizer_functor_theorem_catalog
    ⟨CFSG.RankThree.PartOne.SPOR.sporadicHS_outer_le_two,
      CFSG.RankThree.PartOne.SPOR.sporadicOuterOrderLeTwoSimple_holds,
      CFSG.SignalizerFunctorTheorem.NonLocalExc.subfieldNonLocalizedChevalley⟩
    G p hp k hk A hA hrank Θ hcent hcop hinv hbal hK

end CFSG.Open

namespace CFSG.Open

theorem _root_.CFSG.Milestones.cl_lit_signalizer_functor_theorem_2
    (G : Type) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime)
    (A : Subgroup G) (hA : IsMulCommutative A) (hexp : ∀ a ∈ A, a ^ p = 1)
    (hrank : p ^ 3 ∣ Nat.card A)
    (θ : G → Subgroup G) (hθ : IsSolvableSignalizerFunctor p A θ) :
    let W : Subgroup G := ⨆ (a : G) (_ : a ∈ A) (_ : a ≠ 1), θ a
    Nat.Coprime p (Nat.card W) ∧ Group.IsSolvable W ∧
      ∀ a ∈ A, a ≠ 1 → θ a = W ⊓ Subgroup.centralizer {a} :=
  CFSG.SignalizerFunctorTheorem.glauberman_solvable_signalizer_functor G p hp A hA hexp hrank θ hθ

end CFSG.Open
