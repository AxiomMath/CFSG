module

public import CFSG.GroupTheory.SwapCommute
import CFSG.ClassicalInvolution.Generic.TypeA

public section

namespace CFSG.StandardType.QTwo

private theorem qTwoDegFrame_path_aux {Ω : Type*} [DecidableEq Ω] :
    ∀ {n : ℕ}, 2 ≤ n → ∀ (t : ℕ → Equiv.Perm Ω),
      (∀ i < n, (t i).IsSwap) →
      (∀ i, i + 1 < n → ¬ Commute (t i) (t (i + 1))) →
      (∀ i j, i + 2 ≤ j → j < n → Commute (t i) (t j) ∧ t i ≠ t j) →
      ∃ p : ℕ → Ω, (∀ i ≤ n, ∀ j ≤ n, p i = p j → i = j) ∧
        ∀ i < n, t i = Equiv.swap (p i) (p (i + 1)) := by
  intro n hn
  refine Nat.le_induction (m := 2) ?base ?step n hn
  · intro t hsw hadj hfar
    obtain ⟨a, b, hab, h0⟩ := hsw 0 (by norm_num)
    obtain ⟨c, d, hcd, h1⟩ := hsw 1 (by norm_num)
    have hnc : ¬ Commute (Equiv.swap a b) (Equiv.swap c d) := by
      have h := hadj 0 (by norm_num)
      rwa [h0, h1] at h
    obtain ⟨i, j, k, hij, hjk, hik, e1, e2⟩ :=
      CFSG.GroupTheory.exists_swap_swap_of_not_commute hab hcd hnc
    let p : ℕ → Ω := fun m => if m = 0 then i else if m = 1 then j else k
    have hp0 : p 0 = i := by simp [p]
    have hp1 : p 1 = j := by simp [p]
    have hp2 : p 2 = k := by simp [p]
    refine ⟨p, ?_, ?_⟩
    · intro x hx y hy hxy
      interval_cases x <;> interval_cases y <;> simp_all [hp0, hp1, hp2]
    · intro m hm
      interval_cases m
      · rw [h0, e1]; simp [hp0, hp1]
      · rw [h1, e2]; simp [hp1, hp2]
  · intro j hj ih t hsw hadj hfar
    have hsw' : ∀ i < j, (t i).IsSwap := fun i hi => hsw i (by omega)
    have hadj' : ∀ i, i + 1 < j → ¬ Commute (t i) (t (i + 1)) :=
      fun i hi => hadj i (by omega)
    have hfar' : ∀ i l, i + 2 ≤ l → l < j → Commute (t i) (t l) ∧ t i ≠ t l :=
      fun i l hil hl => hfar i l hil (by omega)
    obtain ⟨p, hpdist, hpt⟩ := ih t hsw' hadj' hfar'
    have htj_swap : (t j).IsSwap := hsw j (by omega)
    have hnc : ¬ Commute (t (j - 1)) (t j) := by
      have h := hadj (j - 1) (by omega)
      rwa [show j - 1 + 1 = j from by omega] at h
    have hpt_j1 : t (j - 1) = Equiv.swap (p (j - 1)) (p j) := by
      have h := hpt (j - 1) (by omega)
      rwa [show j - 1 + 1 = j from by omega] at h
    have hpt_j2 : t (j - 2) = Equiv.swap (p (j - 2)) (p (j - 1)) := by
      have h := hpt (j - 2) (by omega)
      rwa [show j - 2 + 1 = j - 1 from by omega] at h
    have hdisj : Equiv.Perm.Disjoint (t (j - 2)) (t j) := by
      have hs2 : (t (j - 2)).IsSwap := hsw (j - 2) (by omega)
      have hc := hfar (j - 2) j (by omega) (by omega)
      exact (CFSG.ClassicalInvolution.Generic.commute_swaps_iff_disjoint hs2 htj_swap
        hc.2).1 hc.1
    have hfix : ∀ i < j, t j (p i) = p i := by
      intro i hi
      rcases Nat.lt_or_ge i (j - 1) with hlt | hge
      · have hc := hfar i j (by omega) (by omega)
        have hs : (t i).IsSwap := hsw i (by omega)
        have hd : Equiv.Perm.Disjoint (t i) (t j) :=
          (CFSG.ClassicalInvolution.Generic.commute_swaps_iff_disjoint hs htj_swap hc.2).1
            hc.1
        have hmove : t i (p i) ≠ p i := by
          rw [hpt i (by omega), Equiv.swap_apply_left]
          exact fun h => Nat.succ_ne_self i (hpdist (i + 1) (by omega) i (by omega) h)
        rcases hd (p i) with h | h
        · exact absurd h hmove
        · exact h
      · have hi' : i = j - 1 := by omega
        subst hi'
        rcases hdisj (p (j - 1)) with h | h
        · have hp : p (j - 2) = p (j - 1) := by
            rw [hpt_j2, Equiv.swap_apply_right] at h
            exact h
          exact absurd (hpdist (j - 2) (by omega) (j - 1) (by omega) hp) (by omega)
        · exact h
    have htpj : t j (p j) ≠ p j := by
      intro hfixpj
      have hdisj' : Equiv.Perm.Disjoint (t (j - 1)) (t j) := by
        rw [Equiv.Perm.disjoint_iff_eq_or_eq]
        intro x
        by_cases hx : x = p (j - 1)
        · right
          subst hx
          exact hfix (j - 1) (by omega)
        · by_cases hx2 : x = p j
          · right
            subst hx2
            exact hfixpj
          · left
            rw [hpt_j1]
            exact Equiv.swap_apply_of_ne_of_ne hx hx2
      exact hnc hdisj'.commute
    have htne : t j = Equiv.swap (p j) (t j (p j)) :=
      CFSG.ClassicalInvolution.Generic.swap_eq_swap_of_moved htj_swap htpj
    let d : Ω := t j (p j)
    let p' : ℕ → Ω := Function.update p (j + 1) d
    have hp'_d : p' (j + 1) = d := by simp [p']
    have hp'_ne : ∀ k, k ≠ j + 1 → p' k = p k := fun k hk => by
      simp only [p', Function.update_of_ne hk]
    have hd_ne : ∀ i ≤ j, d ≠ p i := by
      intro i hi hdi
      rcases eq_or_lt_of_le hi with rfl | hlt
      · exact htpj hdi
      · have hfixi : t j (p i) = p i := hfix i hlt
        have hpji : p j = p i := (t j).injective (by rw [hfixi]; exact hdi)
        exact absurd (hpdist j (by omega) i (by omega) hpji) (by omega)
    refine ⟨p', ?_, ?_⟩
    · intro i hi l hl hil
      by_cases hin : i = j + 1
      · subst hin
        by_cases hln : l = j + 1
        · subst hln; rfl
        · rw [hp'_d, hp'_ne l hln] at hil
          exact absurd hil (hd_ne l (by omega))
      · rw [hp'_ne i hin] at hil
        by_cases hln : l = j + 1
        · subst hln
          rw [hp'_d] at hil
          exact absurd hil.symm (hd_ne i (by omega))
        · rw [hp'_ne l hln] at hil
          exact hpdist i (by omega) l (by omega) hil
    · intro m hm
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hm) with hlt | heq
      · rw [hpt m hlt, hp'_ne m (by omega), hp'_ne (m + 1) (by omega)]
      · rw [heq, htne, hp'_ne j (by omega), hp'_d]

theorem qTwoDegFrame_path_labelling {Ω : Type*} [DecidableEq Ω] {n : ℕ} (hn : 1 ≤ n)
    (t : ℕ → Equiv.Perm Ω) (hsw : ∀ i < n, (t i).IsSwap)
    (hadj : ∀ i, i + 1 < n → ¬ Commute (t i) (t (i + 1)))
    (hfar : ∀ i j, i + 2 ≤ j → j < n → Commute (t i) (t j) ∧ t i ≠ t j) :
    ∃ p : ℕ → Ω, (∀ i ≤ n, ∀ j ≤ n, p i = p j → i = j) ∧
      ∀ i < n, t i = Equiv.swap (p i) (p (i + 1)) := by
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · interval_cases n
    obtain ⟨a, b, hab, h0⟩ := hsw 0 (by omega)
    let p : ℕ → Ω := fun m => if m = 0 then a else b
    have hp0 : p 0 = a := by simp [p]
    have hp1 : p 1 = b := by simp [p]
    refine ⟨p, ?_, ?_⟩
    · intro i hi j hj hij
      interval_cases i <;> interval_cases j <;> simp_all [hp0, hp1]
    · intro m hm
      interval_cases m
      rw [h0]; simp [hp0, hp1]
  · exact qTwoDegFrame_path_aux hge t hsw hadj hfar

end CFSG.StandardType.QTwo

end
