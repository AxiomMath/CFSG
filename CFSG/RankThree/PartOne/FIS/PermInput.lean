module

public import CFSG.RankThree.PartOne.FIS.SymLocal
public import CFSG.RankThree.PartOne.FIS.PermFacts

public section

namespace CFSG.RankThree.PartOne.FIS

open Equiv Equiv.Perm

theorem permInput {n : ℕ} (h3 : 3 ≤ n) (h5 : n ≤ 5) : PermInput n where
  eq_swaps := fun hinv hconj hgen hord => PermFacts.eq_swaps_of_closed h3 h5 hinv hconj hgen hord
  no_three := fun ha hb hc hab hac hbc h1 h2 h3' =>
    PermFacts.no_three_commuting h5 ha hb hc hab hac hbc h1 h2 h3'
  distinguish := fun h4 _ _ ha hd hnc => PermFacts.exists_distinguishing_swap h4 h5 ha hd hnc
  star_char := fun hB hne hnc hinv => PermFacts.star_char h3 hB hne hnc hinv
  star_inj := fun h => PermFacts.star_injective h3 h
  stab := fun p _ h => PermFacts.mem_closure_swaps_fixing p h
  ncard := PermFacts.ncard_isSwap n
  noncomm_three := fun hn _ _ ha hb hab => by
    subst hn
    exact PermFacts.swap_noncomm_three ha hb hab

theorem perm_eq_one_of_commute_swaps {n : ℕ} (h3 : 3 ≤ n) {σ : Perm (Fin n)}
    (h : ∀ τ : Perm (Fin n), τ.IsSwap → σ * τ = τ * σ) : σ = 1 := by
  refine Equiv.ext fun i => ?_
  by_contra hne
  rw [Perm.one_apply] at hne
  obtain ⟨k, hki, hkσ⟩ := PermFacts.exists_third h3 i (σ i)
  have hc := congrArg (fun f : Perm (Fin n) => f i) (h (swap i k) ⟨i, k, hki.symm, rfl⟩)
  simp only [Perm.mul_apply, swap_apply_left] at hc
  rw [swap_apply_of_ne_of_ne hne hkσ.symm] at hc
  exact hki (σ.injective hc)

end CFSG.RankThree.PartOne.FIS
