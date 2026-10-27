module

public import CFSG.Permutation.FiveTransitive.NormalSubgroupStructure
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG

namespace FiveTransitive.MinimalNormalAutomorphism

open scoped commutatorElement

private theorem isPerfect_of_minimal_normal
    (G : Type*) [Group G]
    (habelian : ∀ A : Subgroup G, A.Normal → IsMulCommutative A → A = ⊥)
    (N : Subgroup G) [N.Normal] (hne : N ≠ ⊥)
    (hmin : ∀ K : Subgroup G, K.Normal → K ≤ N → K = ⊥ ∨ K = N) :
    Group.IsPerfect N := by
  apply Subgroup.isPerfect_iff.mpr
  rcases hmin ⁅N, N⁆ inferInstance (Subgroup.commutator_le_left N N) with hbot | htop
  · have hcomm : IsMulCommutative N :=
      Subgroup.le_centralizer_iff_isMulCommutative.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
    exact (hne (habelian N inferInstance hcomm)).elim
  · exact htop

private theorem ker_conjNormal_eq_centralizer
    (G : Type*) [Group G] (N : Subgroup G) [N.Normal] :
    (MulAut.conjNormal (H := N)).ker = Subgroup.centralizer (N : Set G) := by
  ext g
  constructor
  · intro hg
    change MulAut.conjNormal (H := N) g = 1 at hg
    apply Subgroup.mem_centralizer_iff.mpr
    intro n hn
    have hconj := congrArg (fun e : MulAut N => ((e ⟨n, hn⟩ : N) : G)) hg
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at hconj
    exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
  · intro hg
    change MulAut.conjNormal (H := N) g = 1
    apply MulEquiv.ext
    intro n
    apply Subtype.ext
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    apply mul_inv_eq_iff_eq_mul.mpr
    exact (Subgroup.mem_centralizer_iff.mp hg (n : G) n.property).symm

private theorem injective_conjNormal_of_centralizer_eq_bot
    (G : Type*) [Group G] (N : Subgroup G) [N.Normal]
    (hcentralizer : Subgroup.centralizer (N : Set G) = ⊥) :
    Function.Injective (MulAut.conjNormal (H := N)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  exact (ker_conjNormal_eq_centralizer G N).trans hcentralizer

theorem isPerfect_of_five_transitive_minimal_normal
    (G X : Type*) [Group G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : 5 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i)
    (N : Subgroup G) [N.Normal] (hne : N ≠ ⊥)
    (hmin : ∀ K : Subgroup G, K.Normal → K ≤ N → K = ⊥ ∨ K = N) :
    Group.IsPerfect N := by
  apply isPerfect_of_minimal_normal G ?_ N hne hmin
  intro A hAnormal hAcomm
  let _ : A.Normal := hAnormal
  let _ : IsMulCommutative A := hAcomm
  by_contra hAne
  let _ : Nontrivial A := A.nontrivial_iff_ne_bot.mpr hAne
  exact AbelianNormalObstruction.false_of_commutative_nontrivial_normal_subgroup
    G X hcard h5 A

theorem injective_conjNormal_of_five_transitive_normal
    (G X : Type*) [Group G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : 5 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i)
    (N : Subgroup G) [N.Normal] [Nontrivial N] :
    Function.Injective (MulAut.conjNormal (H := N)) :=
  injective_conjNormal_of_centralizer_eq_bot G N
    (NormalSubgroupStructure.centralizer_eq_bot_of_nontrivial_normal G X hcard h5 N)

end FiveTransitive.MinimalNormalAutomorphism

end CFSG
