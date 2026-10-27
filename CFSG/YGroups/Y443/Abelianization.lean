module

public import CFSG.YGroups.Y443.Basic
public import CFSG.YGroups.Y443.OddInvolutionDiagram

public section

namespace CFSG.YGroups

open CFSG.Open (MonsterY443 MonsterY443Gen MonsterY443Adj monsterY443Rels)

noncomputable def y443Parity : MonsterY443 →* Multiplicative (ZMod 2) :=
  PresentedGroup.toGroup (f := fun _ : MonsterY443Gen => Multiplicative.ofAdd (1 : ZMod 2)) (by
    rintro r (((⟨s, rfl⟩ | ⟨s, t, _, rfl⟩) | ⟨s, t, _, _, rfl⟩) | rfl)
    · rw [map_pow, FreeGroup.lift_apply_of]
      decide
    · rw [map_pow, map_mul, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
      decide
    · rw [map_pow, map_mul, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
      decide
    · simp only [CFSG.Open.monsterY443SpiderWord, CFSG.Open.monsterY443Node, map_pow, map_mul,
        FreeGroup.lift_apply_of]
      decide)

@[simp] theorem y443Parity_of (g : MonsterY443Gen) :
    y443Parity (PresentedGroup.of g) = Multiplicative.ofAdd 1 :=
  PresentedGroup.toGroup.of _

theorem y443Parity_surjective : Function.Surjective y443Parity := by
  intro x
  have h : x = 1 ∨ x = Multiplicative.ofAdd 1 := by revert x; decide
  rcases h with rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact ⟨PresentedGroup.of none, y443Parity_of none⟩

namespace Y443

theorem of_eq_of_gen (g : MonsterY443Gen) :
    Abelianization.of (PresentedGroup.of g : MonsterY443) =
      Abelianization.of (PresentedGroup.of none) := by
  have hadj : ∀ s t : MonsterY443Gen, MonsterY443Adj s t →
      Abelianization.of (PresentedGroup.of s : MonsterY443) =
        Abelianization.of (PresentedGroup.of t) := by
    intro s t h
    refine OddInvolutionDiagram.eq_of_pow_odd ?_ ?_ (by decide : Odd 3) ?_
    · rw [← map_mul, gen_mul_self, map_one]
    · rw [← map_mul, gen_mul_self, map_one]
    · rw [← map_mul, ← map_pow, gen_pair_adj h, map_one]
  have hreach := (SimpleGraph.reachable_iff_reflTransGen none g).1
    (graph_connected.preconnected none g)
  induction hreach with
  | refl => rfl
  | tail _ hb ih => exact (hadj _ _ hb).symm.trans ih

theorem abelianization_form (g : MonsterY443) :
    Abelianization.of g = 1 ∨ Abelianization.of g = Abelianization.of (PresentedGroup.of none) := by
  have hsq : Abelianization.of (PresentedGroup.of none : MonsterY443) *
      Abelianization.of (PresentedGroup.of none) = 1 := by
    rw [← map_mul, gen_mul_self, map_one]
  have hg : g ∈ Subgroup.closure
      (Set.range (PresentedGroup.of : MonsterY443Gen → MonsterY443)) := by
    rw [PresentedGroup.closure_range_of]
    trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    exact Or.inr (of_eq_of_gen s)
  | one => exact Or.inl (map_one _)
  | mul x y _ _ hx hy =>
    rw [map_mul]
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
    · exact Or.inl (one_mul 1)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · exact Or.inl hsq
  | inv x _ hx =>
    rw [map_inv]
    rcases hx with hx | hx <;> rw [hx]
    · exact Or.inl inv_one
    · exact Or.inr (inv_eq_of_mul_eq_one_right hsq)

end Y443

theorem y443Parity_ker : y443Parity.ker = commutator MonsterY443 := by
  refine le_antisymm ?_ (Abelianization.commutator_subset_ker y443Parity)
  intro g hg
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]
  rcases Y443.abelianization_form g with h | h
  · exact h
  · exfalso
    have h1 := congrArg (Abelianization.lift y443Parity) h
    rw [Abelianization.lift_apply_of, Abelianization.lift_apply_of, MonoidHom.mem_ker.1 hg,
      y443Parity_of] at h1
    exact absurd h1.symm (by decide)

theorem y443_commutator_index : (commutator MonsterY443).index = 2 := by
  rw [← y443Parity_ker, Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _
    y443Parity_surjective, Subgroup.card_top, Nat.card_eq_fintype_card]
  rfl

theorem y443_abelianization_equiv :
    Nonempty (Abelianization MonsterY443 ≃* Multiplicative (ZMod 2)) := by
  refine ⟨MulEquiv.ofBijective (Abelianization.lift y443Parity) ⟨?_, ?_⟩⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hg : g ∈ y443Parity.ker := hx
    rw [y443Parity_ker, ← Abelianization.ker_of] at hg
    exact hg
  · intro y
    obtain ⟨g, rfl⟩ := y443Parity_surjective y
    exact ⟨Abelianization.of g, Abelianization.lift_apply_of _ _⟩

theorem y443_abelianization :
    Function.Surjective y443Parity ∧ y443Parity.ker = commutator MonsterY443 ∧
      (commutator MonsterY443).index = 2 ∧
      Nonempty (Abelianization MonsterY443 ≃* Multiplicative (ZMod 2)) :=
  ⟨y443Parity_surjective, y443Parity_ker, y443_commutator_index, y443_abelianization_equiv⟩

end CFSG.YGroups
