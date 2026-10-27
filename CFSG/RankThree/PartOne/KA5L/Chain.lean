module

public import CFSG.RankThree.PartOne.KE.A5Interface
public import CFSG.RankThree.PartOne.KE.E7A2NativeModule

public noncomputable section

namespace CFSG.RankThree.PartOne.KA5L

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.E6 (chainRoot)
open CFSG.RankThree.PartOne.KE

@[expose] def a5chain : Fin 5 → Fin Tag.E7.rank :=
  ![e7Index 1, e7Index 3, e7Index 4, e7Index 5, e7Index 6]

@[expose] def a5Root (a b : Fin 6) : Fin Tag.E7.rank → ℤ := chainRoot a5chain a b

theorem a5Root_swap (a b : Fin 6) : a5Root b a = -a5Root a b :=
  CFSG.RankThree.E6.chainRoot_swap _ _ _

theorem a5Root_add : ∀ a b c : Fin 6, a5Root a b + a5Root b c = a5Root a c := by
  decide +kernel

theorem a5Root_succ : ∀ c : Fin 5, a5Root c.castSucc c.succ = Pi.single (a5chain c) 1 := by
  decide +kernel

theorem a5Root_succ_swap : ∀ c : Fin 5, a5Root c.succ c.castSucc = -Pi.single (a5chain c) 1 := by
  decide +kernel

theorem exists_e7RootVec_a5Root :
    ∀ a b : Fin 6, a ≠ b → ∃ m : Fin 126, e7RootVec m = a5Root a b := by
  decide +kernel

theorem isRoot_a5Root {a b : Fin 6} (h : a ≠ b) :
    IsRoot Tag.E7 (a5Root a b) := by
  obtain ⟨m, hm⟩ := exists_e7RootVec_a5Root a b h
  rw [← hm]
  exact isRoot_e7RootVec m

theorem a5Root_outside : ∀ a b : Fin 6, ∀ i : Fin 7,
    ¬(i = 1 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) → a5Root a b (e7Index i) = 0 := by
  decide +kernel

theorem a5Root_mem_parabolicRoots {a b : Fin 6} (h : a ≠ b) :
    a5Root a b ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7) := by
  refine ⟨isRoot_a5Root h, fun i hi => ?_⟩
  have hi' : ¬(i.val ∈ ({1, 3, 4, 5, 6} : Set ℕ)) := hi
  have h7 : i.val < 7 := i.2
  have := a5Root_outside a b ⟨i.val, h7⟩ (by
    rintro (h1 | h1 | h1 | h1 | h1) <;> apply hi' <;> simp [Fin.ext_iff] at h1 <;> simp [h1])
  exact this

theorem mem_a5Nodes_iff (j : Fin Tag.E7.rank) :
    j ∈ a5Nodes Tag.E7 ↔ (j.val = 1 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5 ∨ j.val = 6) := by
  simp [a5Nodes]

theorem exists_a5chain_of_mem {j : Fin Tag.E7.rank} (hj : j ∈ a5Nodes Tag.E7) :
    ∃ c : Fin 5, a5chain c = j := by
  have h : ∀ j : Fin 7, (j.val = 1 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5 ∨ j.val = 6) →
      ∃ c : Fin 5, a5chain c = e7Index j := by
    decide
  exact h ⟨j.val, j.2⟩ ((mem_a5Nodes_iff j).1 hj)

theorem a5chain_mem (c : Fin 5) : a5chain c ∈ a5Nodes Tag.E7 := by
  rw [mem_a5Nodes_iff]
  fin_cases c <;> simp [a5chain, e7Index]

theorem reflect_a5chain : ∀ (c : Fin 5) (a b : Fin 6),
    reflect Tag.E7 (a5chain c) (a5Root a b) =
      a5Root (Equiv.swap c.castSucc c.succ a) (Equiv.swap c.castSucc c.succ b) := by
  decide +kernel

theorem exists_perm_of_mem_parabolicWeylGroup {u : WeylGroup Tag.E7}
    (hu : u ∈ parabolicWeylGroup Tag.E7 (a5Nodes Tag.E7)) :
    ∃ π : Equiv.Perm (Fin 6), ∀ a b : Fin 6, u • a5Root a b = a5Root (π a) (π b) := by
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := exists_a5chain_of_mem hj
    exact ⟨Equiv.swap c.castSucc c.succ, fun a b => by
      rw [simple_smul]
      exact reflect_a5chain c a b⟩
  | one => exact ⟨1, fun a b => by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨π, hπ⟩ := hx
    obtain ⟨π', hπ'⟩ := hy
    exact ⟨π * π', fun a b => by rw [mul_smul, hπ', hπ]; rfl⟩
  | inv x _ hx =>
    obtain ⟨π, hπ⟩ := hx
    refine ⟨π⁻¹, fun a b => ?_⟩
    rw [inv_smul_eq_iff, hπ]
    simp

theorem exists_perm_neg_of_mem_parabolicWeylGroup {u : WeylGroup Tag.E7}
    (hu : u ∈ parabolicWeylGroup Tag.E7 (a5Nodes Tag.E7)) :
    ∃ π : Equiv.Perm (Fin 6), ∀ a b : Fin 6, u • (-a5Root a b) = a5Root (π b) (π a) := by
  obtain ⟨π, hπ⟩ := exists_perm_of_mem_parabolicWeylGroup hu
  refine ⟨π, fun a b => ?_⟩
  rw [smul_neg, hπ, a5Root_swap (π a) (π b)]

end CFSG.RankThree.PartOne.KA5L
