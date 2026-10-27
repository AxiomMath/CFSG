module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmallI

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry Equiv Equiv.Perm
open CFSG.CGT.PushingUpLit.BHS (exists_notMem_finset)

variable {n : ℕ}

private theorem altHeart_add_self' (y : altHeart n) : y + y = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [← QuotientAddGroup.mk_add]
  have : x + x = 0 :=
    Subtype.ext (funext fun _ => (show ∀ c : ZMod 2, c + c = 0 by decide) _)
  rw [this, QuotientAddGroup.mk_zero]

private theorem pairEW_add_pairEW (c a b : Fin n) :
    (pairEW c a : evenWeight n) + pairEW c b = pairEW a b := by
  refine Subtype.ext (funext fun p => ?_)
  simp only [AddMemClass.coe_add, Pi.add_apply, pairEW_apply]
  exact (show ∀ A B C : ZMod 2, A + B + (A + C) = B + C by decide) _ _ _

theorem eq_one_or_isSwap_of_altAct (hn : 6 ≤ n) {σ : Perm (Fin n)} {z : altHeart n}
    (h : ∀ u : altHeart n, altAct σ u = u ∨ altAct σ u = u + z) : σ = 1 ∨ σ.IsSwap := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hσ1, hσs⟩ := hcon
  have hn5 : 5 ≤ n := by omega
  have hz : ∀ p q : Fin n, pairEW (σ p) (σ q) ≠ pairEW p q →
      (pairEW (σ p) (σ q) : altHeart n) = (pairEW p q : altHeart n) + z := by
    intro p q hne
    rcases h (pairEW p q : altHeart n) with h1 | h1
    · rw [altAct_mk, evenWeightPerm_pairEW, mk_pairEW_eq_iff hn5] at h1
      exact absurd h1 hne
    · rwa [altAct_mk, evenWeightPerm_pairEW] at h1
  by_cases hsq : σ * σ = 1
  ·
    have hσσ : ∀ x, σ (σ x) = x := fun x => by
      simpa using congrArg (fun g : Perm (Fin n) => g x) hsq
    obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
      by_contra hcon'
      exact hσ1 (Equiv.ext fun x => by
        by_contra hx
        exact hcon' ⟨x, hx⟩)
    obtain ⟨j, hj⟩ : ∃ j, σ i = j := ⟨_, rfl⟩
    have hji : σ j = i := by rw [← hj, hσσ]
    have hij : i ≠ j := fun e => hi (hj.trans e.symm)
    obtain ⟨k, hki, hkj, hk⟩ : ∃ k, k ≠ i ∧ k ≠ j ∧ σ k ≠ k := by
      by_contra hcon'
      refine hσs ⟨i, j, hij, Equiv.ext fun x => ?_⟩
      by_cases hxi : x = i
      · rw [hxi, hj, swap_apply_left]
      by_cases hxj : x = j
      · rw [hxj, hji, swap_apply_right]
      rw [swap_apply_of_ne_of_ne hxi hxj]
      by_contra hx
      exact hcon' ⟨x, hxi, hxj, hx⟩
    obtain ⟨l, hl⟩ : ∃ l, σ k = l := ⟨_, rfl⟩
    have hlk : σ l = k := by rw [← hl, hσσ]
    have hlk' : l ≠ k := fun e => hk (hl.trans e)
    have hlj : l ≠ j := fun e => hki (by rw [← hlk, e, hji])
    obtain ⟨m, hm⟩ := exists_notMem_finset (s := ({i, j, k, l} : Finset (Fin n))) (by
      have := Finset.card_le_four (a := i) (b := j) (c := k) (d := l)
      omega)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    obtain ⟨hmi, hmj, hmk, hml⟩ := hm
    obtain ⟨p, hp⟩ : ∃ p, σ m = p := ⟨_, rfl⟩
    have hpm : σ p = m := by rw [← hp, hσσ]
    have hjp : j ≠ p := fun e => hmi (by rw [← hpm, ← e, hji])
    have hlp : l ≠ p := fun e => hmk (by rw [← hpm, ← e, hlk])
    have hA := hz i k (by
      rw [hj, hl, Ne, pairEW_eq_iff (Ne.symm hlj)]
      rintro (⟨h1, _⟩ | ⟨h1, _⟩)
      · exact hij h1.symm
      · exact hkj h1.symm)
    have hB := hz i m (by
      rw [hj, hp, Ne, pairEW_eq_iff hjp]
      rintro (⟨h1, _⟩ | ⟨h1, _⟩)
      · exact hij h1.symm
      · exact hmj h1.symm)
    rw [hj, hl] at hA
    rw [hj, hp] at hB
    have hC : (pairEW l p : altHeart n) = (pairEW k m : altHeart n) := by
      have e1 : (pairEW l p : altHeart n) =
          (pairEW j l : altHeart n) + (pairEW j p : altHeart n) := by
        rw [← QuotientAddGroup.mk_add, pairEW_add_pairEW]
      have e2 : (pairEW k m : altHeart n) =
          (pairEW i k : altHeart n) + (pairEW i m : altHeart n) := by
        rw [← QuotientAddGroup.mk_add, pairEW_add_pairEW]
      rw [e1, e2, hA, hB,
        show ((pairEW i k : altHeart n) + z) + ((pairEW i m : altHeart n) + z) =
          ((pairEW i k : altHeart n) + (pairEW i m : altHeart n)) + (z + z) by abel,
        altHeart_add_self', add_zero]
    rw [mk_pairEW_eq_iff hn5, pairEW_eq_iff hlp] at hC
    rcases hC with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hlk' h1
    · exact hml h1.symm
  ·
    obtain ⟨i, hi⟩ : ∃ i, σ (σ i) ≠ i := by
      by_contra hcon'
      exact hsq (Equiv.ext fun x => by
        by_contra hx
        exact hcon' ⟨x, hx⟩)
    obtain ⟨j, hj⟩ : ∃ j, σ i = j := ⟨_, rfl⟩
    obtain ⟨k, hk⟩ : ∃ k, σ j = k := ⟨_, rfl⟩
    rw [hj, hk] at hi
    have hij : i ≠ j := by
      intro hij'
      subst hij'
      exact hi (hk.symm.trans hj)
    have hjk : j ≠ k := fun e => hij (σ.injective (hj.trans (e.trans hk.symm)))
    have hik : i ≠ k := fun e => hi e.symm
    have hkσ : k ≠ σ k := fun e => hjk (σ.injective (hk.trans e))
    have hσkj : σ k ≠ j := fun e => hik (σ.injective (e.trans hj.symm)).symm
    have hQ := hz i j (by
      rw [hj, hk, Ne, pairEW_eq_iff hjk]
      rintro (⟨h1, _⟩ | ⟨_, h2⟩)
      · exact hij h1.symm
      · exact hik h2.symm)
    have hP := hz j k (by
      rw [hk, Ne, pairEW_eq_iff hkσ]
      rintro (⟨h1, _⟩ | ⟨_, h2⟩)
      · exact hjk h1.symm
      · exact hσkj h2)
    rw [hj, hk] at hQ
    rw [hk] at hP
    have hR : (pairEW k (σ k) : altHeart n) = (pairEW i j : altHeart n) := by
      rw [hP, hQ, add_assoc, altHeart_add_self', add_zero]
    rw [mk_pairEW_eq_iff hn5, pairEW_eq_iff hkσ] at hR
    rcases hR with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hik h1.symm
    · exact hjk h1.symm

theorem eq_pairEW_of_swap (hn : 5 ≤ n) {a b : Fin n} (hab : a ≠ b) {z : altHeart n}
    (h : ∀ u : altHeart n, altAct (swap a b) u = u ∨ altAct (swap a b) u = u + z) :
    z = (pairEW a b : altHeart n) := by
  classical
  obtain ⟨c, hc⟩ := exists_notMem_finset (s := ({a, b} : Finset (Fin n)))
    (lt_of_le_of_lt Finset.card_le_two (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  obtain ⟨hca, hcb⟩ := hc
  rcases h (pairEW c a : altHeart n) with hu | hu
  · exfalso
    rw [altAct_mk, evenWeightPerm_pairEW, swap_apply_of_ne_of_ne hca hcb, swap_apply_left,
      mk_pairEW_eq_iff hn, pairEW_eq_iff hcb] at hu
    rcases hu with ⟨_, h1⟩ | ⟨h1, _⟩
    · exact hab h1.symm
    · exact hca h1
  · rw [altAct_mk, evenWeightPerm_pairEW, swap_apply_of_ne_of_ne hca hcb,
      swap_apply_left] at hu
    calc z = 0 + z := (zero_add z).symm
      _ = ((pairEW c a : altHeart n) + (pairEW c a : altHeart n)) + z := by
        rw [altHeart_add_self']
      _ = (pairEW c a : altHeart n) + ((pairEW c a : altHeart n) + z) := add_assoc _ _ _
      _ = (pairEW c a : altHeart n) + (pairEW c b : altHeart n) := by rw [← hu]
      _ = (pairEW a b : altHeart n) := by
        rw [← QuotientAddGroup.mk_add, pairEW_add_pairEW]

end CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall
