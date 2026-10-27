module

public import CFSG.Permutation.FiveTransitive.OrbitBounds
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG

namespace FiveTransitive.SmallSupportSeven

open MulAction Subgroup
open Equiv

theorem formPerm_map_eq_viaEmbedding
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (l : List α) :
    List.formPerm (l.map e) =
      (List.formPerm l).viaEmbedding e := by
  classical
  induction l with
  | nil =>
      change 1 = Equiv.Perm.viaEmbeddingHom e 1
      rw [map_one]
  | cons x l ih =>
      cases l with
      | nil =>
          change 1 = Equiv.Perm.viaEmbeddingHom e 1
          rw [map_one]
      | cons y l =>
          change
            Equiv.swap (e x) (e y) *
                List.formPerm (List.map e (y :: l)) =
              Equiv.Perm.viaEmbeddingHom e
                (Equiv.swap x y *
                  List.formPerm (y :: l))
          rw [map_mul,
            Equiv.Perm.viaEmbeddingHom_apply, ih]
          congr 1
          ext z
          by_cases hz : z ∈ Set.range e
          · obtain ⟨a, rfl⟩ := hz
            rw [Equiv.Perm.viaEmbedding_apply]
            exact e.injective.swap_apply x y a
          · rw [Equiv.Perm.viaEmbedding_apply_of_notMem
              (Equiv.swap x y) e z hz]
            have hzx : z ≠ e x := by
              intro h
              exact hz ⟨x, h.symm⟩
            have hzy : z ≠ e y := by
              intro h
              exact hz ⟨y, h.symm⟩
            simp [Equiv.swap_apply_def, hzx, hzy]

private theorem support_viaEmbedding
    {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (g : Equiv.Perm α) :
    (g.viaEmbedding e).support =
      g.support.map e := by
  classical
  ext x
  by_cases hx : x ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hx
    simp [Equiv.Perm.mem_support,
      Equiv.Perm.viaEmbedding_apply, e.injective.eq_iff]
  · have hnotMap : x ∉ g.support.map e := by
      intro h
      obtain ⟨a, _ha, hax⟩ := Finset.mem_map.mp h
      exact hx ⟨a, hax⟩
    simp only [hnotMap, iff_false,
      Equiv.Perm.mem_support]
    intro hne
    exact hne
      (Equiv.Perm.viaEmbedding_apply_of_notMem g e x hx)

theorem support_card_viaEmbedding
    {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (g : Equiv.Perm α) :
    (g.viaEmbedding e).support.card = g.support.card := by
  rw [support_viaEmbedding, Finset.card_map]

@[expose] def sevenCycle8 : Equiv.Perm (Fin 8) :=
  List.formPerm [0, 1, 2, 3, 4, 5, 6]

@[expose] def sevenCycle10 : Equiv.Perm (Fin 10) :=
  List.formPerm [0, 1, 2, 3, 4, 5, 6]

@[expose] def comparisonCycle10 (x y z : Fin 10) :
    Equiv.Perm (Fin 10) :=
  List.formPerm [0, 1, 2, 3, x, y, z]

theorem small_mem_closure_viaEmbedding
    {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (g h : Equiv.Perm α)
    (hsmall :
      ∃ w ∈ Subgroup.closure
          ({g, h} : Set (Equiv.Perm α)),
        w ≠ 1 ∧ w.support.card ≤ 5) :
    ∃ w ∈ Subgroup.closure
        ({g.viaEmbedding e, h.viaEmbedding e} :
          Set (Equiv.Perm β)),
      w ≠ 1 ∧ w.support.card ≤ 5 := by
  classical
  obtain ⟨w, hw, hwNe, hwcard⟩ := hsmall
  let φ := Equiv.Perm.viaEmbeddingHom e
  let K :=
    Subgroup.closure
      ({g.viaEmbedding e, h.viaEmbedding e} :
        Set (Equiv.Perm β))
  have hle :
      Subgroup.closure ({g, h} : Set (Equiv.Perm α)) ≤
        K.comap φ := by
    rw [Subgroup.closure_le]
    intro u hu
    rcases hu with rfl | rfl
    · exact
        Subgroup.subset_closure
          (Set.mem_insert _ _)
    · exact
        Subgroup.subset_closure
          (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  refine ⟨φ w, hle hw, ?_, ?_⟩
  · intro hone
    apply hwNe
    apply Equiv.Perm.viaEmbeddingHom_injective e
    simpa only [map_one] using hone
  · simpa [φ, Equiv.Perm.viaEmbeddingHom_apply,
      support_card_viaEmbedding] using hwcard

end FiveTransitive.SmallSupportSeven

end CFSG
