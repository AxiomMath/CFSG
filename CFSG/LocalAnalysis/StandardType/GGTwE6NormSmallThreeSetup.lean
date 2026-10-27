module

public import CFSG.LocalAnalysis.StandardType.GGTwE6NormSmallThreeFrame
import CFSG.LocalAnalysis.StandardType.GGTwE6NormSmallThreeData

public section

namespace CFSG.StandardType.TwE6NormThree

open CFSG.Assembly


theorem exists_endNode_data {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1)
    {X : Subgroup (MulAut (TwE6Delta.RecipeR K n))} (hX : IsElemAbelian 3 X)
    (hXI : (X : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n)
    (hX4 : 3 ^ 4 ≤ Nat.card X)
    (hXU : ∃ U : Subgroup (TwE6Delta.RecipeR K n), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ φ ∈ X, ∀ u ∈ U, φ u ∈ U)
    {x : MulAut (TwE6Delta.RecipeR K n)} (hx : x ∈ X) (hx1 : x ≠ 1)
    (hcomp : IsComponentOf (LargeEvenLayer (ggFix x)) (ggFix x))
    (hend : ∀ y ∈ X, (∀ j ∈ LargeEvenLayer (ggFix x), y j = j) ↔ y ∈ Subgroup.zpowers x) :
    ∃ (Y : Subgroup (MulAut (TwE6Delta.RecipeR K n))) (ι : Type)
      (r s : ι → TwE6Delta.RecipeR K n) (u : TwE6Delta.RecipeR K n)
      (F : Subgroup (TwE6Delta.RecipeR K n)),
      IsElemAbelian 3 Y ∧ X ≤ Y ∧ (∀ i, MulAut.conj (s i) ∈ Y) ∧
      (∀ i, ∀ y ∈ Y, ∃ k : ℕ,
        MulAut.conj (r i) * y * (MulAut.conj (r i))⁻¹ = MulAut.conj (s i) ^ k * y) ∧
      (∀ i, r i * s i * (r i)⁻¹ = (s i)⁻¹) ∧
      u * u = 1 ∧ u ≠ 1 ∧ (∀ φ ∈ X, φ u = u) ∧
      F ≤ Subgroup.closure (Set.range s) ∧ F ≤ LargeEvenLayer (ggFix x) ∧
      (∀ f ∈ F, f * u = u * f) ∧ 3 ^ 3 ≤ Nat.card F := by
  obtain ⟨emb, ζ, α, Ψ, hemb, hζ, hα, hΨ, hr, hs, hXd, hcount⟩ :=
    exists_endNode_frame hn hK h3 hX hXI hX4 hXU hx hx1 hcomp fun y hy => (hend y hy).1
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  exact exists_endNode_data_of_frame hX hemb hζ hα hΨ hr hs hXd hcount

end CFSG.StandardType.TwE6NormThree

end
