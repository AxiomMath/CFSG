module

public import CFSG.Monster.B.E6.StdF4Orders

public section

namespace CFSG.Monster.B.E6.StdF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.Monster.B.Classical Matrix

@[expose] def fibY : Fin 5 → Fin 6 → ℤ :=
  ![![1, 2, 2, 3, 2, 1], ![1, 1, 2, 3, 2, 1], ![1, 0, 1, 1, 1, 1], ![0, -1, 0, 0, 0, 0],
    ![-1, -2, -2, -3, -2, -1]]

@[expose] def fibYL (d : Fin 5) : Fin TwistTag.E6.tag.rank → ℤ := fibY d

@[expose] def fibWord : Fin 5 → List (Fin 4) :=
  ![[], [0], [0, 1, 2, 1, 0], [0, 1, 2, 3, 1, 2, 1, 0],
    [0, 1, 2, 3, 1, 2, 0, 1, 2, 3, 0, 1, 2, 1, 0]]

@[expose] def fibExp : Fin 5 → ℕ := ![21, 20, 15, 10, 0]

@[expose] def fibIF : Fin 5 → Finset (Fin 4) := ![{1, 2, 3}, {2, 3}, {1, 2}, {2, 3}, {1, 2, 3}]

theorem foldr_fibWord : ∀ d : Fin 5, (fibWord d).foldr E6Folded.r E6Folded.θ = fibY d := by
  decide

theorem wsmul_fibWord
    (d : Fin 5) : wsmul (ncs.wordProd (fibWord d)) E6Folded.θ = fibY d := by
  rw [wsmul_wordProd, foldr_fibWord]

theorem form_fibY : ∀ d : Fin 5, E6Folded.form E6Folded.θ (fibY d) = repLevel d := by decide

theorem level_fibWord
    (d : Fin 5) : level (ncs.wordProd (fibWord d)) = repLevel d := by
  rw [level, wsmul_fibWord, form_fibY]

@[expose] def fibForm (d : Fin 5) (α : Fin TwistTag.E6.tag.rank → ℤ) : ℤ :=
  α ⬝ᵥ (TwistTag.E6.tag.symmetrizedCartan *ᵥ fibYL d)

@[expose] def fibRoots (d : Fin 5) : Set (Fin TwistTag.E6.tag.rank → ℤ) :=
  {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α ∧ 0 < α (i6 1) ∧ 0 ≤ fibForm d α}

@[expose] def fibOrbits (d : Fin 5) : Finset (Finset (Fin TwistTag.E6.tag.rank → ℤ)) :=
  posOrbits.filter fun O => ∀ α ∈ O, 0 < α (i6 1) ∧ 0 ≤ fibForm d α

theorem prod_fibOrbits : ∀ d : Fin 5,
    ∏ O ∈ fibOrbits d, (if O.card = 1 then 2 else 4) = 2 ^ fibExp d := by
  decide +kernel

@[expose] def rootList : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  (List.finRange 72).map fun k => (e6Root k : Fin TwistTag.E6.tag.rank → ℤ)

theorem mem_rootList
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α) :
    α ∈ rootList := by
  obtain ⟨k, hk⟩ := exists_e6Root_eq hα
  exact List.mem_map.2 ⟨k, List.mem_finRange k, hk⟩

theorem isRoot_of_mem_rootList
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : α ∈ rootList) :
    IsRoot TwistTag.E6.tag α := by
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hα
  exact isRoot_e6Root k

theorem fib_levi_check : ∀ d : Fin 5, ∀ α ∈ rootList, 0 < height α → α (i6 1) = 0 →
    0 ≤ fibForm d α := by
  decide +kernel

theorem fib_perm_check : ∀ d : Fin 5, ∀ α ∈ rootList,
    permLattice TwistTag.E6.perm α (i6 1) = α (i6 1) ∧
      fibForm d (permLattice TwistTag.E6.perm α) = fibForm d α := by
  decide +kernel

theorem fib_torus_check : ∀ d : Fin 5,
    ∑ j, Tag.E6.cartan (i6 2) j * fibYL d j = 0 ∧ ∑ j, Tag.E6.cartan (i6 4) j * fibYL d j = 0 := by
  decide +kernel

theorem fib_refl_check : ∀ d : Fin 5, ∀ i ∈ fibIF d, E6Folded.r i (fibY d) = fibY d := by
  decide +kernel

theorem fibY_root_check : ∀ d : Fin 5, fibYL d ∈ rootList := by
  decide +kernel

theorem isRoot_fibYL (d : Fin 5) : IsRoot TwistTag.E6.tag (fibYL d) :=
  isRoot_of_mem_rootList (fibY_root_check d)

end CFSG.Monster.B.E6.StdF4
