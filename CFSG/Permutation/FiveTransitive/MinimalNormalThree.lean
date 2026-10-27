module

public import CFSG.Permutation.FiveTransitive.NormalInheritsThree
public import CFSG.Permutation.FiveTransitive.MinimalNormalSimple

public section

namespace CFSG

namespace FiveTransitive.MinimalNormalThree

private theorem three_of_explicit_five
    (G X : Type*) [Group G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcard : 6 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i)
    (N : Subgroup G) [N.Normal] [Nontrivial N] :
    MulAction.IsMultiplyPretransitive N X 3 := by
  apply NormalInheritsThree.three_of_five G X hcard _ N
  rw [MulAction.isMultiplyPretransitive_iff]
  intro a b
  obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
  exact ⟨g, Function.Embedding.ext hg⟩

theorem existsUnique_nonabelian_simple_three_transitive_minimal_normal
    (G X : Type*) [Group G] [Finite G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : 6 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    ∃! N : Subgroup G, ∃ hN : N.Normal,
      N ≠ ⊥ ∧
      (∀ K : Subgroup G, K.Normal → K ≤ N → K = ⊥ ∨ K = N) ∧
      IsSimpleGroup N ∧ ¬ IsMulCommutative N ∧
      Function.Injective (@MulAut.conjNormal G _ N hN) ∧
      MulAction.IsMultiplyPretransitive N X 3 := by
  obtain ⟨N, ⟨hNnormal, hNne, hNmin, hNsimple, hNnonabelian, hNinjective⟩, hunique⟩ :=
    MinimalNormalSimple.existsUnique_nonabelian_simple_minimal_normal G X (by omega) h5
  let _ : N.Normal := hNnormal
  let _ : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hNne
  refine ⟨N, ⟨hNnormal, hNne, hNmin, hNsimple, hNnonabelian, hNinjective, ?_⟩, ?_⟩
  · exact three_of_explicit_five G X hcard h5 N
  · intro M hM
    obtain ⟨hMnormal, hMne, hMmin, hMsimple, hMnonabelian, hMinjective, _⟩ := hM
    exact hunique M ⟨hMnormal, hMne, hMmin, hMsimple, hMnonabelian, hMinjective⟩

end FiveTransitive.MinimalNormalThree

end CFSG
