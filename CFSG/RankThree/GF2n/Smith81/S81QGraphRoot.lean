module

public import CFSG.RankThree.GF2n.Smith81.S81QGraphCl
public import CFSG.LieType.Steinberg.Classical.SpinPlus.Basic

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.SpinFrame
open CFSG.LieType.RootSystem (roots)

section Vectors

variable (n : ℕ) (K : Type*) [Field K]

@[expose] def flipAt (i₀ i : Fin n) (s : Bool) : Bool := if i = i₀ then !s else s

theorem swapIso_plusVec (i₀ i : Fin n) (s : Bool) :
    swapIso n K i₀ (plusVec n K i s) = plusVec n K i (flipAt n i₀ i s) := by
  funext a
  rw [swapIso_apply, swapLin_apply]
  by_cases hi : i = i₀
  · subst hi
    cases s <;>
      simp [flipAt, plusVec, Pi.single_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left,
        Equiv.swap_apply_right]
  · have h1 : (Sum.inl i : Fin n ⊕ Fin n) ≠ Sum.inl i₀ := fun h => hi (Sum.inl_injective h)
    have h2 : (Sum.inr i : Fin n ⊕ Fin n) ≠ Sum.inl i₀ := Sum.inr_ne_inl
    have h3 : (Sum.inl i : Fin n ⊕ Fin n) ≠ Sum.inr i₀ := Sum.inl_ne_inr
    have h4 : (Sum.inr i : Fin n ⊕ Fin n) ≠ Sum.inr i₀ := fun h => hi (Sum.inr_injective h)
    cases s <;>
      simp [flipAt, hi, plusVec, Pi.single_apply, Equiv.swap_apply_eq_iff,
        Equiv.swap_apply_of_ne_of_ne h1 h3, Equiv.swap_apply_of_ne_of_ne h2 h4]

variable {n}

@[expose] def negAt (i₀ : Fin n) (e : Fin n → ℤ) : Fin n → ℤ := fun a => if a = i₀ then -e a else e a

theorem negAt_single_add_single (i₀ : Fin n) {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    negAt i₀ (Pi.single i (boolSign s) + Pi.single j (boolSign t) : Fin n → ℤ) =
      Pi.single i (boolSign (flipAt n i₀ i s)) + Pi.single j (boolSign (flipAt n i₀ j t)) := by
  funext a
  by_cases hai : a = i
  · subst hai
    by_cases ha : a = i₀
    · subst ha
      simp [negAt, flipAt, Pi.single_apply, hij]
    · simp [negAt, flipAt, ha, Pi.single_apply, hij]
  · by_cases haj : a = j
    · subst haj
      by_cases ha : a = i₀
      · subst ha
        simp [negAt, flipAt, Pi.single_apply, hai]
      · simp [negAt, flipAt, ha, Pi.single_apply, hai]
    · simp [negAt, Pi.single_apply, hai, haj]

theorem isLong_negAt (i₀ : Fin n) {e : Fin n → ℤ} (he : IsLong e) : IsLong (negAt i₀ e) := by
  obtain ⟨i, j, hij, s, t, rfl⟩ := he
  exact ⟨i, j, hij, flipAt n i₀ i s, flipAt n i₀ j t, negAt_single_add_single i₀ hij s t⟩

end Vectors

section Roots

variable {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)

theorem graphSpin_longRoot (i₀ : Fin n) {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K) :
    graphSpin n K i₀ ((plusFrame n K hn).longRoot hij s t (.ofAdd c)) =
      (plusFrame n K hn).longRoot hij (flipAt n i₀ i s) (flipAt n i₀ j t) (.ofAdd c) := by
  apply Subtype.ext
  show CliffordAlgebra.map (swapIso n K i₀) _ = _
  rw [HypFrame.coe_longRoot, HypFrame.coe_longRoot, map_add, map_one, map_smul, map_mul,
    CliffordAlgebra.map_apply_ι, CliffordAlgebra.map_apply_ι]
  simp only [plusFrame_vec, swapIso_plusVec]

theorem intCast_eq_one_of_sq [CharP K 2] {z : ℤ} (hz : z = 1 ∨ z = -1) : (z : K) = 1 := by
  rcases hz with rfl | rfl
  · simp
  · simp [CharTwo.neg_eq]

theorem graphSpin_rootElt [CharP K 2] (i₀ : Fin n) {e : Fin n → ℤ} (he : IsLong e) (c : K) :
    graphSpin n K i₀ (rootElt (plusFrame n K hn) e c) =
      rootElt (plusFrame n K hn) (negAt i₀ e) c := by
  obtain ⟨i, j, hij, s, t, rfl⟩ := he
  have he' := negAt_single_add_single i₀ hij s t
  rw [rootElt_eq _ hij rfl, rootElt_eq _ hij he', graphSpin_longRoot hn i₀ hij,
    intCast_eq_one_of_sq (repSign_eq_one_or_eq_neg_one i j s t),
    intCast_eq_one_of_sq (repSign_eq_one_or_eq_neg_one i j (flipAt n i₀ i s) (flipAt n i₀ j t))]

end Roots

section D6

variable {K : Type} [Field K]

@[expose] def swap45 (γ : Fin 6 → ℤ) : Fin 6 → ℤ := γ ∘ Equiv.swap (4 : Fin 6) 5

theorem toStdD_swap45 (γ : Fin 6 → ℤ) : toStdD 6 (swap45 γ) = negAt 5 (toStdD 6 γ) := by
  funext a
  fin_cases a <;> simp [toStdD, negAt, swap45, Equiv.swap_apply_of_ne_of_ne] <;> omega

theorem swap45_mem_roots {γ : Fin 6 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanD 6) ∅) :
    swap45 γ ∈ roots (isFiniteType_cartanD 6) ∅ := by
  rw [← SpinPlus.isLong_toStdD_iff (by norm_num : 2 ≤ 6)] at hγ ⊢
  rw [toStdD_swap45]
  exact isLong_negAt 5 hγ

theorem graphSpin_x [CharP K 2] {γ : Fin 6 → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanD 6) ∅) (c : K) :
    graphSpin 6 K 5 (SpinPlus.x 6 K (by norm_num) γ c) =
      SpinPlus.x 6 K (by norm_num) (swap45 γ) c := by
  unfold SpinPlus.x
  rw [toStdD_swap45]
  exact graphSpin_rootElt (by norm_num) 5 ((SpinPlus.isLong_toStdD_iff (by norm_num : 2 ≤ 6)).2 hγ) c

end D6

end CFSG.RankThree.GF2n.Smith81.D6Spin
