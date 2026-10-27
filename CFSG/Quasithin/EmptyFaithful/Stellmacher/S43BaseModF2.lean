module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.H1Orth

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43

open Equiv CFSG.Quasithin.F53Mod

@[expose] def m17qa : Perm (Fin 5) := swap 0 1 * swap 2 3

@[expose] def m17qb : Perm (Fin 5) := swap 0 2 * swap 2 4

@[expose] def m17A : alternatingGroup (Fin 5) :=
  ⟨m17qa, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def m17B : alternatingGroup (Fin 5) :=
  ⟨m17qb, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def m17rels : List (List Bool) :=
  [[false, false], (List.replicate 3 [true]).flatten, (List.replicate 5 [false, true]).flatten]

theorem m17rels_one : ∀ l ∈ m17rels, wordG m17A m17B l = 1 := by decide +kernel

@[irreducible] def m17altF : Finset (Perm (Fin 5)) := wordSet [m17qa, m17qb] 10

theorem m17_alt_wordSet : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → σ ∈ m17altF := by
  unfold m17altF
  decide +kernel

theorem m17altF_closure : ∀ σ ∈ m17altF, σ ∈ Subgroup.closure {g | g ∈ [m17qa, m17qb]} := by
  unfold m17altF
  exact wordSet_subset_closure [m17qa, m17qb] 10

theorem m17_closure : Subgroup.closure ({m17A, m17B} : Set (alternatingGroup (Fin 5))) = ⊤ := by
  refine eq_top_iff.mpr fun g _ => ?_
  have e : (alternatingGroup (Fin 5)).subtype '' ({m17A, m17B} : Set (alternatingGroup (Fin 5))) =
      {g | g ∈ [m17qa, m17qb]} := by
    rw [Set.image_pair]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, List.mem_cons, List.not_mem_nil,
      or_false, Set.mem_ofPred_eq]
    exact Iff.rfl
  have h1 := m17altF_closure g.1 (m17_alt_wordSet g.1 (Equiv.Perm.mem_alternatingGroup.mp g.2))
  rw [← e, ← MonoidHom.map_closure] at h1
  obtain ⟨h, hh, hg⟩ := Subgroup.mem_map.mp h1
  have : h = g := Subtype.ext hg
  rwa [this] at hh

@[expose] def m17act : alternatingGroup (Fin 5) →* MulAut nat.W :=
  nat.act.comp (alternatingGroup (Fin 5)).subtype

@[expose] def m17wa : List Bool :=
  [true, false, true, true, false, true, false, true, true, false, true]

@[expose] def m17Eqv (x y : nat.W) : Prop :=
  wordV m17act m17A m17B x y m17wa = nat.act (swap 0 2) x ∧
  wordV m17act m17A m17B x y [true, true] = nat.act (swap 0 2) y ∧
  wordV m17act m17A m17B x y m17wa = nat.act (swap 1 3) x ∧
  wordV m17act m17A m17B x y [true] = nat.act (swap 1 3) y

instance (x y : nat.W) : Decidable (m17Eqv x y) := by unfold m17Eqv; infer_instance

@[expose] def m17Cob (x y : nat.W) : Prop :=
  ∃ u : nat.W, m17act m17A u * u⁻¹ = x ∧ m17act m17B u * u⁻¹ = y

instance (x y : nat.W) : Decidable (m17Cob x y) := by unfold m17Cob; infer_instance

theorem m17_conj_a : ((wordG m17A m17B m17wa : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
    swap 0 2 * m17qa * (swap 0 2)⁻¹ ∧
    ((wordG m17A m17B m17wa : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
    swap 1 3 * m17qa * (swap 1 3)⁻¹ := by
  decide +kernel

theorem m17_conj_b : ((wordG m17A m17B [true, true] : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
    swap 0 2 * m17qb * (swap 0 2)⁻¹ ∧
    ((wordG m17A m17B [true] : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
    swap 1 3 * m17qb * (swap 1 3)⁻¹ := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem m17_check : ∀ x y : nat.W, (∀ l ∈ m17rels, wordV m17act m17A m17B x y l = 1) →
    m17Eqv x y → ∀ x' y' : nat.W, (∀ l ∈ m17rels, wordV m17act m17A m17B x' y' l = 1) →
    m17Eqv x' y' → ¬ m17Cob x y → ¬ m17Cob x' y' → m17Cob (x * x') (y * y') := by
  decide +kernel

end CFSG.Quasithin.F53.Stellmacher.S43
