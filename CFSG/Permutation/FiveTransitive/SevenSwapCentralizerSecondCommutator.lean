module

public import CFSG.Permutation.FiveTransitive.SwapSecondCommutatorFourPoints

public section

namespace CFSG

open scoped commutatorElement

namespace FiveTransitive.SevenSwapCentralizerSecondCommutator

private theorem of_fixed_embedding
    {F : Type*} [Fintype F] [DecidableEq F]
    (t : Equiv.Perm F) (e : Fin 4 ↪ Function.fixedPoints t) :
    ∃ d : commutator (Subgroup.centralizer ({t} : Set (Equiv.Perm F))),
      d ∈ commutator (commutator (Subgroup.centralizer ({t} : Set (Equiv.Perm F)))) ∧
      orderOf (d.val : Equiv.Perm F) = 2 ∧ (d.val : Equiv.Perm F).support.card = 4 ∧
      Nat.card (Function.fixedPoints (d.val : Equiv.Perm F)) = Nat.card F - 4 := by
  let C := Subgroup.centralizer ({t} : Set (Equiv.Perm F))
  let e' : Fin 4 ↪ F := e.trans (Function.Embedding.subtype _)
  have hs (i j : Fin 4) : Equiv.swap (e' i) (e' j) ∈ C := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    symm
    rw [Equiv.mul_swap_eq_swap_mul]
    have hi : t (e' i) = e' i := (e i).property
    have hj : t (e' j) = e' j := (e j).property
    rw [hi, hj]
  let s : C := ⟨Equiv.swap (e' 0) (e' 1), hs 0 1⟩
  let a : C := ⟨Equiv.swap (e' 0) (e' 2), hs 0 2⟩
  let b : C := ⟨Equiv.swap (e' 0) (e' 3), hs 0 3⟩
  let D := commutator C
  let u : D := ⟨⁅s, a⁆,
    Subgroup.commutator_mem_commutator (Subgroup.mem_top s) (Subgroup.mem_top a)⟩
  let v : D := ⟨⁅s, b⁆,
    Subgroup.commutator_mem_commutator (Subgroup.mem_top s) (Subgroup.mem_top b)⟩
  let d : D := ⁅u, v⁆
  have hd : (d.val : Equiv.Perm F) = Equiv.swap (e' 0) (e' 1) * Equiv.swap (e' 2) (e' 3) := by
    change ⁅⁅Equiv.swap (e' 0) (e' 1), Equiv.swap (e' 0) (e' 2)⁆,
      ⁅Equiv.swap (e' 0) (e' 1), Equiv.swap (e' 0) (e' 3)⁆⁆ = _
    exact SwapSecondCommutatorFourPoints.identity e'
  have hmem : d ∈ commutator D :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top u) (Subgroup.mem_top v)
  obtain ⟨h2, h4, hfix⟩ := SwapCommutatorFourPoints.shape e'
  refine ⟨d, hmem, ?_, ?_, ?_⟩
  · simpa only [hd] using h2
  · simpa only [hd] using h4
  · simpa only [hd] using hfix

theorem exists_double_swap
    {F : Type*} [Fintype F] [DecidableEq F]
    (hseven : Nat.card F = 7) (t : Equiv.Perm F) (ht : t.IsSwap) :
    ∃ d : commutator (Subgroup.centralizer ({t} : Set (Equiv.Perm F))),
      d ∈ commutator (commutator (Subgroup.centralizer ({t} : Set (Equiv.Perm F)))) ∧
      orderOf (d.val : Equiv.Perm F) = 2 ∧
      Nat.card (Function.fixedPoints (d.val : Equiv.Perm F)) = 3 ∧
      (d.val : Equiv.Perm F).support.card = 4 := by
  have hfix : Fintype.card (Function.fixedPoints t) = 5 := by
    rw [t.card_fixedPoints, t.sum_cycleType, Equiv.Perm.card_support_eq_two.mpr ht,
      ← Nat.card_eq_fintype_card, hseven]
  obtain ⟨e⟩ : Nonempty (Fin 4 ↪ Function.fixedPoints t) :=
    Function.Embedding.nonempty_of_card_le (by simp [hfix])
  obtain ⟨d, hd, h2, h4, hfixed⟩ := of_fixed_embedding t e
  refine ⟨d, hd, h2, ?_, h4⟩
  rw [hfixed, hseven]

end FiveTransitive.SevenSwapCentralizerSecondCommutator

end CFSG
