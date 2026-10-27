module

public import CFSG.Permutation.FiveTransitive.MinimalNormalThree
public import CFSG.Permutation.FiveTransitive.NormalFourOrSharpThree
public import CFSG.Permutation.FiveTransitive.SharpThreeNormalObstruction

public section

namespace CFSG

namespace FiveTransitive.MinimalNormalFour

theorem four_of_normal_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : 6 ≤ Fintype.card X)
    (h5 : MulAction.IsMultiplyPretransitive P X 5)
    (hnotAlt : ¬ alternatingGroup X ≤ P)
    (N : Subgroup P) [N.Normal] [Nontrivial N] :
    MulAction.IsMultiplyPretransitive N X 4 := by
  rcases NormalFourOrSharpThree.four_or_card_eq_three_descFactorial
    P X hcard h5 N with h4 | hsharp
  · exact h4
  · have h3 := NormalInheritsThree.three_of_five P X hcard h5 N
    have htop := SharpThreeNormalObstruction.eq_top_of_normal_sharp_three
      X P hcard h5 N h3 hsharp
    exact (hnotAlt (htop ▸ le_top)).elim

theorem existsUnique_nonabelian_simple_four_transitive_minimal_normal
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : 6 ≤ Fintype.card X)
    (h5 : MulAction.IsMultiplyPretransitive P X 5)
    (hnotAlt : ¬ alternatingGroup X ≤ P) :
    ∃! N : Subgroup P, ∃ hN : N.Normal,
      N ≠ ⊥ ∧
      (∀ K : Subgroup P, K.Normal → K ≤ N → K = ⊥ ∨ K = N) ∧
      IsSimpleGroup N ∧ ¬ IsMulCommutative N ∧
      Function.Injective (@MulAut.conjNormal P _ N hN) ∧
      MulAction.IsMultiplyPretransitive N X 3 ∧
      MulAction.IsMultiplyPretransitive N X 4 := by
  have h5explicit : ∀ a b : Fin 5 → X,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g, hg⟩ := (MulAction.isMultiplyPretransitive_iff.mp h5) ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨g, fun i => DFunLike.congr_fun hg i⟩
  obtain ⟨N, ⟨hNnormal, hNne, hNmin, hNsimple, hNnonabelian, hNinjective, hN3⟩, hunique⟩ :=
    MinimalNormalThree.existsUnique_nonabelian_simple_three_transitive_minimal_normal P X hcard h5explicit
  let _ : N.Normal := hNnormal
  let _ : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hNne
  refine ⟨N, ⟨hNnormal, hNne, hNmin, hNsimple, hNnonabelian, hNinjective, hN3, ?_⟩, ?_⟩
  · exact four_of_normal_of_not_alternating X P hcard h5 hnotAlt N
  · intro M hM
    obtain ⟨hMnormal, hMne, hMmin, hMsimple, hMnonabelian, hMinjective, hM3, _⟩ := hM
    exact hunique M ⟨hMnormal, hMne, hMmin, hMsimple, hMnonabelian, hMinjective, hM3⟩

end FiveTransitive.MinimalNormalFour

end CFSG
