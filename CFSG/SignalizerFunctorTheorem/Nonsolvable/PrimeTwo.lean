module

public import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.SignalizerFunctorTheorem.Solvable.SmallPrimes
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.Reduction

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem

theorem isSolvable_of_coprime_two {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (h : Nat.Coprime 2 (Nat.card H)) : Group.IsSolvable H :=
  CFSG.Milestones.odd_order_solvable (Nat.coprime_two_left.mp h)

theorem mcBrideCompletenessAt_two : McBrideCompletenessAt 2 := fun G _ _ A hA hlarge Θ hΘ _ =>
  (Solvable.solvableRankOneTheoremAt_of_le_three 2 Nat.prime_two (by norm_num) G A hA hlarge Θ hΘ
    fun S hS => isSolvable_of_coprime_two _ (hΘ.coprime S hS)).1

theorem faithfulSectionExclusionAt_two : FaithfulSectionExclusionAt 2 := by
  intro G _ _ A _ _ Θ _ _ hW K L hKW _ _ _ _ _ hnc
  exfalso
  have : Group.IsSolvable (completion 2 1 A Θ) := isSolvable_of_coprime_two _ hW.1
  have : Group.IsSolvable K :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKW)
  obtain ⟨x, y, hxy⟩ := hnc
  exact hxy (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance x y)

theorem mcBrideRankOneTheoremAt_two : McBrideRankOneTheoremAt 2 :=
  mcBrideRankOneTheoremAt_of 2 Nat.prime_two mcBrideCompletenessAt_two faithfulSectionExclusionAt_two

theorem signalizer_functor_theorem_two
    (G : Type) [Group G] [Finite G] (k : ℕ) (hk : 1 ≤ k)
    (A : Subgroup G) (hA : IsElemAbelian 2 A) (hrank : 2 ^ (k + 2) ≤ Nat.card A)
    (Θ : Subgroup G → Subgroup G)
    (hcent : ∀ S ∈ signalizerFunctorEk 2 k A, Θ S ≤ Subgroup.centralizer (S : Set G))
    (hcop : ∀ S ∈ signalizerFunctorEk 2 k A, Nat.Coprime 2 (Nat.card (Θ S)))
    (hinv : ∀ S ∈ signalizerFunctorEk 2 k A, A ≤ Subgroup.normalizer (Θ S : Set G))
    (hbal : ∀ S ∈ signalizerFunctorEk 2 k A, ∀ S' ∈ signalizerFunctorEk 2 k A,
      Θ S ⊓ Subgroup.centralizer (S' : Set G) ≤ Θ S')
    (hK : ∀ S ∈ signalizerFunctorEk 2 k A, signalizerMcBrideHypothesisB 2 (Θ S)) :
    let W : Subgroup G := ⨆ (S : Subgroup G) (_ : S ∈ signalizerFunctorEk 2 k A), Θ S
    (Nat.Coprime 2 (Nat.card W) ∧ A ≤ Subgroup.normalizer (W : Set G)) ∧
    (∀ S ∈ signalizerFunctorEk 2 k A, W ⊓ Subgroup.centralizer (S : Set G) = Θ S) ∧
    (∀ Y : Subgroup G, A ≤ Subgroup.normalizer (Y : Set G) →
      (∀ S ∈ signalizerFunctorEk 2 k A, Y ⊓ Subgroup.centralizer (S : Set G) ≤ Θ S) →
      Y ≤ W) ∧
    ((∀ S ∈ signalizerFunctorEk 2 k A, Group.IsSolvable (Θ S)) → Group.IsSolvable W) :=
  signalizer_functor_theorem_of_rankOneAt G 2 Nat.prime_two
    (Solvable.solvableRankOneTheoremAt_of_le_three 2 Nat.prime_two (by norm_num))
    mcBrideRankOneTheoremAt_two k hk A hA hrank Θ hcent hcop hinv hbal hK

end CFSG.SignalizerFunctorTheorem
