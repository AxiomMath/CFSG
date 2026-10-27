module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H18

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

variable {n : ℕ}

@[expose] def stdE (n M : ℕ) : AddSubgroup (Fin n → ZMod 2) where
  carrier := {v | ∀ i : Fin n, M ≤ (i : ℕ) → v i = 0}
  add_mem' := fun ha hb i hi => by rw [Pi.add_apply, ha i hi, hb i hi, add_zero]
  zero_mem' := fun _ _ => rfl
  neg_mem' := fun {a} ha i hi => by
    show (-a) i = 0
    have h0 : a i = 0 := ha i hi
    simp only [Pi.neg_apply, h0]
    decide

theorem single_mem_stdE {M : ℕ} {j : Fin n} (hj : (j : ℕ) < M) :
    Pi.single j (1 : ZMod 2) ∈ stdE n M := fun i hi => by
  have hij : i ≠ j := by
    rintro rfl
    omega
  simp [hij]

theorem add_add_cancel_vec (a b : Fin n → ZMod 2) : a + b + a = b := by
  rw [add_comm a b, add_assoc, add_self_vec, add_zero]

theorem stdE_mono {M M' : ℕ} (h : M ≤ M') : stdE n M ≤ stdE n M' :=
  fun _ hv i hi => hv i (h.trans hi)

theorem stdE_le_of_single {M : ℕ} {W : AddSubgroup (Fin n → ZMod 2)}
    (hW : ∀ j : Fin n, (j : ℕ) < M → Pi.single j (1 : ZMod 2) ∈ W) : stdE n M ≤ W := by
  intro v hv
  have h : v = ∑ j : Fin n, v j • Pi.single j (1 : ZMod 2) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [h]
  refine AddSubgroup.sum_mem _ fun j _ => ?_
  by_cases hj : (j : ℕ) < M
  · rcases zmod2_cases (v j) with h0 | h1
    · rw [h0, zero_smul]
      exact W.zero_mem
    · rw [h1, one_smul]
      exact hW j hj
  · rw [hv j (not_lt.mp hj), zero_smul]
    exact W.zero_mem

theorem eq_stdE_of_invariant {W : AddSubgroup (Fin n → ZMod 2)}
    (hW : ∀ (i j : Fin n) (h : (i : ℕ) + 1 = j), ∀ w ∈ W,
      trvE i j (by intro e; subst e; omega) • w ∈ W) :
    ∃ M ≤ n, W = stdE n M := by
  classical
  have hex : ∃ M, W ≤ stdE n M := ⟨n, fun w _ i hi => absurd i.2 (not_lt.mpr hi)⟩
  set M := Nat.find hex with hM
  have hMW : W ≤ stdE n M := Nat.find_spec hex
  have hMn : M ≤ n := Nat.find_min' hex fun w _ i hi => absurd i.2 (not_lt.mpr hi)
  refine ⟨M, hMn, le_antisymm hMW ?_⟩
  rcases Nat.eq_zero_or_pos M with h0 | hpos
  · rw [h0]
    intro v hv
    have : v = 0 := funext fun i => hv i (Nat.zero_le _)
    rw [this]
    exact W.zero_mem
  have hmin := Nat.find_min hex (show M - 1 < M by omega)
  obtain ⟨w, hwW, hw⟩ : ∃ w ∈ W, ¬ ∀ i : Fin n, M - 1 ≤ (i : ℕ) → w i = 0 := by
    by_contra hc
    exact hmin fun w hw i hi => by
      by_contra h
      exact hc ⟨w, hw, fun h' => h (h' i hi)⟩
  obtain ⟨i₀, hi₀, hwi₀⟩ : ∃ i₀ : Fin n, M - 1 ≤ (i₀ : ℕ) ∧ w i₀ ≠ 0 := by
    by_contra hc
    exact hw fun i hi => by
      by_contra h
      exact hc ⟨i, hi, h⟩
  have hi₀M : (i₀ : ℕ) = M - 1 := by
    have := hMW hwW i₀
    by_contra hne
    exact hwi₀ (this (by omega))
  have hw1 : w i₀ = 1 := zmod2_eq_one_of_ne_zero hwi₀
  have hdown : ∀ t : ℕ, t < M - 1 → ∀ j : Fin n, (j : ℕ) = M - 2 - t →
      Pi.single j (1 : ZMod 2) ∈ W := by
    intro t
    induction t with
    | zero =>
      intro ht j hj
      have hj1 : (j : ℕ) + 1 = i₀ := by omega
      have h1 := W.add_mem (hW j i₀ hj1 w hwW) hwW
      rwa [trvE_mulVec, hw1, one_smul, add_add_cancel_vec] at h1
    | succ t ih =>
      intro ht j hj
      have hj' : (j : ℕ) + 1 < n := by omega
      set j' : Fin n := ⟨(j : ℕ) + 1, hj'⟩
      have hprev := ih (by omega) j' (by simp [j']; omega)
      have h1 := W.add_mem (hW j j' rfl _ hprev) hprev
      rwa [trvE_mulVec, Pi.single_eq_same, one_smul, add_add_cancel_vec] at h1
  have hlow : ∀ j : Fin n, (j : ℕ) < M - 1 → Pi.single j (1 : ZMod 2) ∈ W := fun j hj =>
    hdown (M - 2 - j) (by omega) j (by omega)
  have htop : Pi.single i₀ (1 : ZMod 2) ∈ W := by
    have hlowE : stdE n (M - 1) ≤ W := stdE_le_of_single hlow
    have hdiff : w + Pi.single i₀ (1 : ZMod 2) ∈ stdE n (M - 1) := by
      intro i hi
      rw [Pi.add_apply, Pi.single_apply]
      by_cases h : i = i₀
      · simp only [h, ite_true, hw1]
        exact zmod2_add_self 1
      · simp only [h, ite_false, add_zero]
        refine hMW hwW i ?_
        have : (i : ℕ) ≠ i₀ := fun h' => h (Fin.ext h')
        omega
    have := W.add_mem hwW (hlowE hdiff)
    rwa [← add_assoc, add_self_vec, zero_add] at this
  refine stdE_le_of_single fun j hj => ?_
  by_cases hj' : (j : ℕ) < M - 1
  · exact hlow j hj'
  · have : j = i₀ := Fin.ext (by omega)
    rw [this]
    exact htop

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
