module

public import CFSG.Permutation.FiveTransitive.NormalInheritsTwo
public import CFSG.Permutation.FiveTransitive.PerfectCharacteristicSimpleTwo
public import CFSG.Permutation.FiveTransitive.MinimalNormalCharacteristicSimple
public import CFSG.Permutation.FiveTransitive.MinimalNormalAutomorphism

public section

namespace CFSG

namespace FiveTransitive.MinimalNormalSimple

private theorem isSimpleGroup_of_minimal_normal
    (G X : Type*) [Group G] [Finite G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : 5 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i)
    (N : Subgroup G) [N.Normal] [Nontrivial N]
    (hmin : ∀ K : Subgroup G, K.Normal → K ≤ N → K = ⊥ ∨ K = N) :
    IsSimpleGroup N := by
  let _ : Group.IsPerfect N :=
    MinimalNormalAutomorphism.isPerfect_of_five_transitive_minimal_normal
      G X hcard h5 N (N.nontrivial_iff_ne_bot.mp inferInstance) hmin
  apply PerfectCharacteristicSimpleTwo.isSimpleGroup_of_perfect_characteristically_simple_two
    N X (by omega)
      (NormalInheritsTwo.isMultiplyPretransitive_two_of_five_transitive_normal G X hcard h5 N)
  intro H hH
  let _ : H.Characteristic := hH
  exact MinimalNormalCharacteristicSimple.characteristic_eq_bot_or_top_of_minimal_normal
    G N hmin H

theorem existsUnique_nonabelian_simple_minimal_normal
    (G X : Type*) [Group G] [Finite G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : 5 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    ∃! N : Subgroup G, ∃ hN : N.Normal,
      N ≠ ⊥ ∧
      (∀ K : Subgroup G, K.Normal → K ≤ N → K = ⊥ ∨ K = N) ∧
      IsSimpleGroup N ∧ ¬ IsMulCommutative N ∧
      Function.Injective (@MulAut.conjNormal G _ N hN) := by
  obtain ⟨N, ⟨hNnormal, hNne, hNmin⟩, hunique⟩ :=
    NormalSubgroupStructure.existsUnique_minimal_nontrivial_normal G X hcard h5
  let _ : N.Normal := hNnormal
  let _ : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hNne
  let _ : Group.IsPerfect N :=
    MinimalNormalAutomorphism.isPerfect_of_five_transitive_minimal_normal
      G X hcard h5 N hNne hNmin
  refine ⟨N, ⟨hNnormal, hNne, hNmin, ?_, ?_, ?_⟩, ?_⟩
  · exact isSimpleGroup_of_minimal_normal G X hcard h5 N hNmin
  · exact Group.IsPerfect.not_isMulCommutative N
  · exact MinimalNormalAutomorphism.injective_conjNormal_of_five_transitive_normal
      G X hcard h5 N
  · intro M hM
    obtain ⟨hMnormal, hMne, hMmin, _⟩ := hM
    exact hunique M ⟨hMnormal, hMne, hMmin⟩

end FiveTransitive.MinimalNormalSimple

end CFSG
