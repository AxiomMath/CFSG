module

public import CFSG.RankThree.PartOne.KD4T.Emb
public import CFSG.LieType.Steinberg.Minuscule.CertInputs
public import CFSG.RankThree.PartOne.KD4T.Certs

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
open CFSG.RankThree.PartOne.KD4T (E6Sub e6Idx)

@[expose] def m27List : List (List ℤ) :=
  [[2, 2, 3, 4, 3, 2, 1], [1, 2, 3, 4, 3, 2, 1], [1, 2, 2, 4, 3, 2, 1], [1, 2, 2, 3, 3, 2, 1],
   [1, 1, 2, 3, 3, 2, 1], [1, 2, 2, 3, 2, 2, 1], [1, 1, 2, 3, 2, 2, 1], [1, 2, 2, 3, 2, 1, 1],
   [1, 1, 2, 2, 2, 2, 1], [1, 1, 2, 3, 2, 1, 1], [1, 1, 1, 2, 2, 2, 1], [1, 1, 2, 2, 2, 1, 1],
   [0, 1, 1, 2, 2, 2, 1], [1, 1, 1, 2, 2, 1, 1], [1, 1, 2, 2, 1, 1, 1], [0, 1, 1, 2, 2, 1, 1],
   [1, 1, 1, 2, 1, 1, 1], [0, 1, 1, 2, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1], [0, 1, 1, 1, 1, 1, 1],
   [1, 0, 1, 1, 1, 1, 1], [0, 0, 1, 1, 1, 1, 1], [0, 1, 0, 1, 1, 1, 1], [0, 0, 0, 1, 1, 1, 1],
   [0, 0, 0, 0, 1, 1, 1], [0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 0, 1]]

@[expose] def m27RootN (τ : Tag) (a : ℕ) : Fin τ.rank → ℤ :=
  fun i => (m27List.getD a []).getD i 0

@[expose] def m27Root (τ : Tag) (a : Fin e6Data.d) : Fin τ.rank → ℤ := m27RootN τ a

@[expose] def e6wt (a j : ℕ) : ℤ := ((e6Data.weights.getD a 0 / 4 ^ j % 4 : ℕ) : ℤ) - 1

theorem e6wt_eq (a : ℕ) (j : Fin Tag.E6.rank) : e6wt a j = e6Data.wt a j := rfl

section Checks

variable {τ : Tag}

theorem m27_isRoot_E7 : ∀ a : Fin e6Data.d, IsRoot Tag.E7 (m27Root Tag.E7 a) := by
  intro a
  rw [isRoot_iff_mem_artifactRoots]
  revert a
  decide +kernel

theorem m27_isRoot_E8 : ∀ a : Fin e6Data.d, IsRoot Tag.E8 (m27Root Tag.E8 a) := by
  intro a
  rw [isRoot_iff_mem_artifactRoots]
  revert a
  decide +kernel

theorem m27_isRoot (hτ : τ = .E7 ∨ τ = .E8) (a : Fin e6Data.d) : IsRoot τ (m27Root τ a) := by
  rcases hτ with rfl | rfl
  · exact m27_isRoot_E7 a
  · exact m27_isRoot_E8 a

theorem m27_pairing_E7 : ∀ a : Fin e6Data.d, ∀ j : Fin Tag.E6.rank,
    (∑ i, Tag.E7.cartan (e6Idx j) i * m27Root Tag.E7 a i) = e6wt a j.val := by
  decide +kernel

theorem m27_pairing_E8 : ∀ a : Fin e6Data.d, ∀ j : Fin Tag.E6.rank,
    (∑ i, Tag.E8.cartan (e6Idx j) i * m27Root Tag.E8 a i) = e6wt a j.val := by
  decide +kernel

theorem m27_pairing (hτ : τ = .E7 ∨ τ = .E8) [E6Sub τ] (a : Fin e6Data.d) (j : Fin Tag.E6.rank) :
    (∑ i, τ.cartan (e6Idx j) i * m27Root τ a i) = e6wt a j.val := by
  rcases hτ with rfl | rfl
  · exact m27_pairing_E7 a j
  · exact m27_pairing_E8 a j

theorem e6Data_weyl_lt : ∀ a : Fin e6Data.d, ∀ j : Fin Tag.E6.rank, e6Data.weyl a j < 27 := by
  decide +kernel

theorem m27_add_single_E7 : ∀ a : Fin e6Data.d, ∀ j : Fin Tag.E6.rank, e6wt a j.val = -1 →
    m27RootN Tag.E7 (e6Data.weyl a j) = m27Root Tag.E7 a + Pi.single (e6Idx j) 1 := by
  decide +kernel

theorem m27_add_single_E8 : ∀ a : Fin e6Data.d, ∀ j : Fin Tag.E6.rank, e6wt a j.val = -1 →
    m27RootN Tag.E8 (e6Data.weyl a j) = m27Root Tag.E8 a + Pi.single (e6Idx j) 1 := by
  decide +kernel

theorem m27_sub_single_E7 : ∀ a : Fin e6Data.d, ∀ j : Fin Tag.E6.rank, e6wt a j.val = 1 →
    m27RootN Tag.E7 (e6Data.weyl a j) = m27Root Tag.E7 a - Pi.single (e6Idx j) 1 := by
  decide +kernel

theorem m27_sub_single_E8 : ∀ a : Fin e6Data.d, ∀ j : Fin Tag.E6.rank, e6wt a j.val = 1 →
    m27RootN Tag.E8 (e6Data.weyl a j) = m27Root Tag.E8 a - Pi.single (e6Idx j) 1 := by
  decide +kernel

theorem m27_ne_single_E7 : ∀ a : Fin e6Data.d, ∀ j : Fin Tag.E6.rank,
    m27Root Tag.E7 a ≠ Pi.single (e6Idx j) 1 ∧ m27Root Tag.E7 a ≠ -Pi.single (e6Idx j) 1 := by
  decide +kernel

theorem m27_ne_single_E8 : ∀ a : Fin e6Data.d, ∀ j : Fin Tag.E6.rank,
    m27Root Tag.E8 a ≠ Pi.single (e6Idx j) 1 ∧ m27Root Tag.E8 a ≠ -Pi.single (e6Idx j) 1 := by
  decide +kernel

theorem m27_ne_single (hτ : τ = .E7 ∨ τ = .E8) [E6Sub τ] (a : Fin e6Data.d) (j : Fin Tag.E6.rank) :
    m27Root τ a ≠ Pi.single (e6Idx j) 1 ∧ m27Root τ a ≠ -Pi.single (e6Idx j) 1 := by
  rcases hτ with rfl | rfl
  · exact m27_ne_single_E7 a j
  · exact m27_ne_single_E8 a j

theorem m27_not_add_E7 : ∀ a : Fin e6Data.d, ∀ j : Fin Tag.E6.rank, e6wt a j.val ≠ -1 →
    List.ofFn (m27Root Tag.E7 a + Pi.single (e6Idx j) 1) ∉ Tag.E7.artifactRoots := by
  decide +kernel

theorem m27_not_add_E8 : ∀ a : Fin e6Data.d, ∀ j : Fin Tag.E6.rank, e6wt a j.val ≠ -1 →
    List.ofFn (m27Root Tag.E8 a + Pi.single (e6Idx j) 1) ∉ Tag.E8.artifactRoots := by
  decide +kernel

theorem m27_not_add (hτ : τ = .E7 ∨ τ = .E8) [E6Sub τ] (a : Fin e6Data.d)
    (j : Fin Tag.E6.rank) (h : e6wt a j.val ≠ -1) :
    ¬ IsRoot τ (m27Root τ a + Pi.single (e6Idx j) 1) := by
  rw [isRoot_iff_mem_artifactRoots]
  rcases hτ with rfl | rfl
  · exact m27_not_add_E7 a j h
  · exact m27_not_add_E8 a j h

theorem m27_not_sub_E7 : ∀ a : Fin e6Data.d, ∀ j : Fin Tag.E6.rank, e6wt a j.val ≠ 1 →
    List.ofFn (m27Root Tag.E7 a - Pi.single (e6Idx j) 1) ∉ Tag.E7.artifactRoots := by
  decide +kernel

theorem m27_not_sub_E8 : ∀ a : Fin e6Data.d, ∀ j : Fin Tag.E6.rank, e6wt a j.val ≠ 1 →
    List.ofFn (m27Root Tag.E8 a - Pi.single (e6Idx j) 1) ∉ Tag.E8.artifactRoots := by
  decide +kernel

theorem m27_not_sub (hτ : τ = .E7 ∨ τ = .E8) [E6Sub τ] (a : Fin e6Data.d)
    (j : Fin Tag.E6.rank) (h : e6wt a j.val ≠ 1) :
    ¬ IsRoot τ (m27Root τ a - Pi.single (e6Idx j) 1) := by
  rw [isRoot_iff_mem_artifactRoots]
  rcases hτ with rfl | rfl
  · exact m27_not_sub_E7 a j h
  · exact m27_not_sub_E8 a j h

theorem m27Root_injective_E7 : Function.Injective (m27Root Tag.E7) := by
  decide +kernel

theorem m27Root_injective_E8 : Function.Injective (m27Root Tag.E8) := by
  decide +kernel

theorem m27Root_injective (hτ : τ = .E7 ∨ τ = .E8) : Function.Injective (m27Root τ) := by
  rcases hτ with rfl | rfl
  · exact m27Root_injective_E7
  · exact m27Root_injective_E8

end Checks

end CFSG.RankThree.PartOne.KE6
