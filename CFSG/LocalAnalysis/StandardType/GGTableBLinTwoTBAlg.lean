module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.StandardType.LinTwoTB

variable {s : ℕ}

@[expose] def signV (i : Fin s) (v : Fin s → ZMod 3) : Fin s → ZMod 3 :=
  Function.update v i (-v i)

@[expose] def swapV (i j : Fin s) (v : Fin s → ZMod 3) : Fin s → ZMod 3 :=
  v ∘ Equiv.swap i j

theorem signV_self (i : Fin s) (v : Fin s → ZMod 3) : signV i v i = -v i := by
  simp [signV]

theorem signV_of_ne {i k : Fin s} (h : k ≠ i) (v : Fin s → ZMod 3) : signV i v k = v k := by
  simp [signV, Function.update_of_ne h]

theorem signV_single_of_ne {i k : Fin s} (h : k ≠ i) (c : ZMod 3) :
    signV i (Pi.single k c) = Pi.single k c := by
  funext m
  by_cases hm : m = i
  · subst hm
    simp [signV_self, Pi.single_apply, Ne.symm h]
  · simp [signV_of_ne hm]

theorem signV_single_self (i : Fin s) (c : ZMod 3) :
    signV i (Pi.single i c) = Pi.single i (-c) := by
  funext m
  by_cases hm : m = i
  · subst hm
    simp [signV_self]
  · simp [signV_of_ne hm, Pi.single_apply, hm]

theorem swapV_single_left (i j : Fin s) (c : ZMod 3) :
    swapV i j (Pi.single i c) = Pi.single j c := by
  funext m
  have h : Equiv.swap i j m = i ↔ m = j := by
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
  simp only [swapV, Function.comp_apply, Pi.single_apply, h]

theorem swapV_comm (i j : Fin s) (v : Fin s → ZMod 3) : swapV i j v = swapV j i v := by
  simp [swapV, Equiv.swap_comm]

theorem swapV_single_right (i j : Fin s) (c : ZMod 3) :
    swapV i j (Pi.single j c) = Pi.single i c := by
  rw [swapV_comm, swapV_single_left]

theorem single_eq_nsmul (l : Fin s) (c : ZMod 3) :
    (Pi.single l c : Fin s → ZMod 3) = c.val • Pi.single l 1 := by
  funext k
  by_cases hk : k = l
  · subst hk
    simp [nsmul_eq_mul]
  · simp [Pi.single_apply, hk]

theorem swapV_single_of_ne {i j k : Fin s} (hi : k ≠ i) (hj : k ≠ j) (c : ZMod 3) :
    swapV i j (Pi.single k c) = Pi.single k c := by
  funext m
  have h : Equiv.swap i j m = k ↔ m = k := by
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne hi hj]
  simp only [swapV, Function.comp_apply, Pi.single_apply, h]

theorem eq_zero_of_signFixed {v : Fin s → ZMod 3} (h : ∀ i, signV i v = v) : v = 0 := by
  funext i
  have h1 := congrFun (h i) i
  rw [signV_self] at h1
  have h2 : ∀ x : ZMod 3, -x = x → x = 0 := by decide
  exact h2 _ h1

theorem eq_top_of_single_one (F : AddSubgroup (Fin s → ZMod 3))
    (h : ∀ i, Pi.single i (1 : ZMod 3) ∈ F) : F = ⊤ := by
  classical
  have h4 : ∀ j (c : ZMod 3), Pi.single j c ∈ F := by
    intro j c
    have hc : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 := by decide
    rcases hc c with rfl | rfl | rfl
    · simp
    · exact h j
    · have : (Pi.single j (2 : ZMod 3) : Fin s → ZMod 3) =
          Pi.single j (1 : ZMod 3) + Pi.single j (1 : ZMod 3) := by
        rw [← Pi.single_add]
        congr 1
      rw [this]
      exact F.add_mem (h j) (h j)
  rw [eq_top_iff]
  intro w _
  rw [← Finset.univ_sum_single w]
  exact F.sum_mem fun j _ => h4 j (w j)

theorem eq_top_of_signed (F : AddSubgroup (Fin s → ZMod 3))
    (hsg : ∀ i v, v ∈ F → signV i v ∈ F) (hsw : ∀ i j v, v ∈ F → swapV i j v ∈ F)
    (hne : ∃ v ∈ F, v ≠ 0) : F = ⊤ := by
  classical
  obtain ⟨v, hvF, hv0⟩ := hne
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  have h1 : Pi.single i (2 * v i) ∈ F := by
    have e : v - signV i v = Pi.single i (2 * v i) := by
      funext k
      by_cases hk : k = i
      · subst hk
        simp only [Pi.sub_apply, signV_self, Pi.single_eq_same]
        ring
      · simp [signV_of_ne hk, Pi.single_apply, hk]
    rw [← e]
    exact F.sub_mem hvF (hsg i v hvF)
  have h2 : Pi.single i (1 : ZMod 3) ∈ F := by
    have key : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = 2 := by decide
    have hne2 : (2 : ZMod 3) * v i ≠ 0 := by
      have : ∀ x : ZMod 3, x ≠ 0 → 2 * x ≠ 0 := by decide
      exact this _ hi
    rcases key _ hne2 with h | h
    · rwa [h] at h1
    · rw [h] at h1
      have : (Pi.single i (1 : ZMod 3) : Fin s → ZMod 3) =
          Pi.single i (2 : ZMod 3) + Pi.single i (2 : ZMod 3) := by
        rw [← Pi.single_add]
        congr 1
      rw [this]
      exact F.add_mem h1 h1
  refine eq_top_of_single_one F fun j => ?_
  have := hsw i j _ h2
  rwa [swapV_single_left] at this

theorem exists_scalar_of_commute (F : (Fin s → ZMod 3) → (Fin s → ZMod 3))
    (hadd : ∀ v w, F (v + w) = F v + F w) (hsg : ∀ i v, F (signV i v) = signV i (F v))
    (hsw : ∀ i j v, F (swapV i j v) = swapV i j (F v)) :
    ∃ c : ZMod 3, ∀ v, F v = c • v := by
  classical
  set f : (Fin s → ZMod 3) →+ (Fin s → ZMod 3) := AddMonoidHom.mk' F hadd with hf
  have hFf : ∀ v, F v = f v := fun v => rfl
  have h2x : ∀ x : ZMod 3, -x = x → x = 0 := by decide
  have hoff : ∀ (i k : Fin s) (x : ZMod 3), k ≠ i → F (Pi.single i x) k = 0 := by
    intro i k x hki
    have h1 := hsg k (Pi.single i x)
    rw [signV_single_of_ne (Ne.symm hki)] at h1
    have h2 := congrFun h1 k
    rw [signV_self] at h2
    exact h2x _ h2.symm
  have hmul : ∀ (i : Fin s) (x : ZMod 3),
      F (Pi.single i x) = Pi.single i (F (Pi.single i x) i) := by
    intro i x
    funext k
    by_cases hk : k = i
    · subst hk
      simp
    · rw [hoff i k x hk]
      simp [Pi.single_apply, hk]
  set c : Fin s → ZMod 3 := fun i => F (Pi.single i 1) i with hc
  have hsingle : ∀ (i : Fin s) (x : ZMod 3), F (Pi.single i x) = Pi.single i (x * c i) := by
    intro i x
    have hx : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
    rcases hx x with rfl | rfl | rfl
    · have h0 : F 0 = 0 := by
        have := hadd 0 0
        simpa using this
      simp [h0]
    · have := hmul i 1
      rw [one_mul]
      exact this
    · have e : (Pi.single i (2 : ZMod 3) : Fin s → ZMod 3) =
          Pi.single i (1 : ZMod 3) + Pi.single i (1 : ZMod 3) := by
        rw [← Pi.single_add]
        congr 1
      rw [e, hadd, hmul i 1, ← Pi.single_add]
      congr 1
      ring
  have hconst : ∀ i j : Fin s, c i = c j := by
    intro i j
    have h1 := hsw i j (Pi.single i 1)
    rw [swapV_single_left, hsingle j 1, hsingle i 1, swapV_single_left] at h1
    have := congrFun h1 j
    simpa using this.symm
  by_cases hs : Nonempty (Fin s)
  · obtain ⟨i₀⟩ := hs
    refine ⟨c i₀, fun v => ?_⟩
    rw [← Finset.univ_sum_single v, hFf, map_sum]
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [← hFf, hsingle]
    rw [Finset.sum_eq_single k]
    · simp only [Pi.single_eq_same, hconst k i₀, Finset.sum_apply, Pi.single_apply]
      simp [Finset.sum_apply, Pi.single_apply, mul_comm]
    · intro m _ hm
      simp [Pi.single_apply, Ne.symm hm]
    · simp
  · refine ⟨0, fun v => ?_⟩
    funext k
    exact (hs ⟨k⟩).elim

end CFSG.StandardType.LinTwoTB

end
