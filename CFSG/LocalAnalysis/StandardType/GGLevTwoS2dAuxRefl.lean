module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2dAuxClass
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2bAux

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Spin

noncomputable def levTwoS2d_ofCoord (n : ℕ) (i j : Fin n) (s t : ℤ)
    (hij : i ≠ j) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) : Fin n → ℤ :=
  Classical.choose (exists_mem_rootsD_toStdD_eq n hij hs ht)

theorem levTwoS2d_ofCoord_toStdD (n : ℕ) (i j : Fin n) (s t : ℤ)
    (hij : i ≠ j) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    toStdD n (levTwoS2d_ofCoord n i j s t hij hs ht) = Pi.single i s + Pi.single j t :=
  (Classical.choose_spec (exists_mem_rootsD_toStdD_eq n hij hs ht)).2

theorem levTwoS2d_ofCoord_isRt (n : ℕ) (i j : Fin n) (s t : ℤ)
    (hij : i ≠ j) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    IsRt (isFiniteType_cartanD n) (levTwoS2d_ofCoord n i j s t hij hs ht) :=
  (isRt_iff_mem_roots (isFiniteType_cartanD n)).mpr
    (Classical.choose_spec (exists_mem_rootsD_toStdD_eq n hij hs ht)).1

@[simp] theorem levTwoS2d_dot_single_left {n : ℕ} (p : Fin n) (x : ℤ) (f : Fin n → ℤ) :
    ∑ c, (((Pi.single p x : Fin n → ℤ) c : ℚ) * (f c : ℚ)) = (x : ℚ) * (f p : ℚ) := by
  rw [Finset.sum_eq_single p]
  · simp
  · intro c _ hc; simp [Pi.single_eq_of_ne hc]
  · intro hp; exact absurd (Finset.mem_univ p) hp

theorem levTwoS2d_dot_add_self (n : ℕ) {a b : Fin n} (hab : a ≠ b) (s t : ℤ) :
    ∑ c, (((Pi.single a s + Pi.single b t : Fin n → ℤ) c : ℚ) *
      ((Pi.single a s + Pi.single b t : Fin n → ℤ) c : ℚ)) =
      (s : ℚ) * (s : ℚ) + (t : ℚ) * (t : ℚ) := by
  simp only [Pi.add_apply, Int.cast_add, add_mul, mul_add, Finset.sum_add_distrib]
  simp [Pi.single_apply, hab, Ne.symm hab]

theorem levTwoS2d_dot_add_coord (n : ℕ) {a b : Fin n} (_hab : a ≠ b) (s t : ℤ)
    (v : Fin n → ℤ) :
    ∑ c, (((Pi.single a s + Pi.single b t : Fin n → ℤ) c : ℚ) * (toStdD n v c : ℚ)) =
      (s : ℚ) * (toStdD n v a : ℚ) + (t : ℚ) * (toStdD n v b : ℚ) := by
  simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
  simp

theorem levTwoS2d_rRefl_apply (n : ℕ) (_hn : 4 ≤ n) {β v : Fin n → ℤ}
    (hβ : IsRt (isFiniteType_cartanD n) β) {k₀ : ℤ}
    (hk : (k₀ : ℚ) * form (isFiniteType_cartanD n) (toRat β) (toRat β) =
      2 * form (isFiniteType_cartanD n) (toRat β) (toRat v)) :
    weylAction (isFiniteType_cartanD n) (rRefl (isFiniteType_cartanD n) β) v = v - k₀ • β := by
  obtain ⟨k, hk', hw⟩ := weylAction_rRefl (isFiniteType_cartanD n) hβ v
  have hβne : β ≠ 0 := by
    obtain ⟨w, j, rfl⟩ := hβ
    intro h
    have h1 : (Pi.single j (1 : ℤ) : Fin n → ℤ) = 0 := by
      have hw := congrArg (weylAction (isFiniteType_cartanD n) w⁻¹) h
      rwa [weylAction_inv_apply_apply, map_zero] at hw
    simpa using congrFun h1 j
  have hbb : form (isFiniteType_cartanD n) (toRat β) (toRat β) ≠ 0 :=
    ne_of_gt (form_pos (isFiniteType_cartanD n) (fun h => hβne (toRat_injective (by rw [h, map_zero]))))
  have hk_eq : k = k₀ := by
    have : (k : ℚ) * form (isFiniteType_cartanD n) (toRat β) (toRat β) =
        (k₀ : ℚ) * form (isFiniteType_cartanD n) (toRat β) (toRat β) := by linarith
    exact_mod_cast mul_right_cancel₀ hbb this
  rw [hw, hk_eq]

theorem levTwoS2d_rRefl_self (n : ℕ) (hn : 4 ≤ n) {β : Fin n → ℤ}
    (hβ : IsRt (isFiniteType_cartanD n) β) :
    weylAction (isFiniteType_cartanD n) (rRefl (isFiniteType_cartanD n) β) β = -β := by
  have hk : (2 : ℚ) * form (isFiniteType_cartanD n) (toRat β) (toRat β) =
      2 * form (isFiniteType_cartanD n) (toRat β) (toRat β) := rfl
  rw [levTwoS2d_rRefl_apply n hn hβ hk]
  module

theorem levTwoS2d_toStdD_rRefl_gen (n : ℕ) (hn : 4 ≤ n) {a b : Fin n} (hab : a ≠ b)
    {s t : ℤ} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) (v : Fin n → ℤ) :
    toStdD n
        (weylAction (isFiniteType_cartanD n)
          (rRefl (isFiniteType_cartanD n)
            (levTwoS2d_ofCoord n a b s t hab hs ht)) v) =
      toStdD n v - (s * toStdD n v a + t * toStdD n v b) •
        (Pi.single a s + Pi.single b t) := by
  set β := levTwoS2d_ofCoord n a b s t hab hs ht with hβdef
  have hβ : IsRt (isFiniteType_cartanD n) β := levTwoS2d_ofCoord_isRt n a b s t hab hs ht
  have hβc : toStdD n β = Pi.single a s + Pi.single b t := levTwoS2d_ofCoord_toStdD n a b s t hab hs ht
  have hk : ((s * toStdD n v a + t * toStdD n v b : ℤ) : ℚ) *
      form (isFiniteType_cartanD n) (toRat β) (toRat β) =
      2 * form (isFiniteType_cartanD n) (toRat β) (toRat v) := by
    obtain ⟨κ, hκpos, hκ⟩ := levTwoS2d_form_coord n hn
    rw [hκ, hκ, hβc]
    push_cast
    rw [levTwoS2d_dot_add_self n hab s t, levTwoS2d_dot_add_coord n hab s t v]
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> push_cast <;> ring
  rw [levTwoS2d_rRefl_apply n hn hβ hk, toStdD_sub, toStdD_smul, hβc]

theorem levTwoS2d_toStdD_rRefl_diff_apply (n : ℕ) (hn : 4 ≤ n) {k a b : Fin n}
    (hak : a ≠ k) (hbk : b ≠ k) (hab : a ≠ b) {σ τ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    toStdD n
        (weylAction (isFiniteType_cartanD n)
          (rRefl (isFiniteType_cartanD n)
            (levTwoS2d_ofCoord n a b 1 (-1) hab (Or.inl rfl) (Or.inr rfl)))
          (levTwoS2d_ofCoord n k a σ τ (Ne.symm hak) hσ hτ)) =
      Pi.single k σ + Pi.single b τ := by
  rw [levTwoS2d_toStdD_rRefl_gen n hn hab (Or.inl rfl) (Or.inr rfl)
      (levTwoS2d_ofCoord n k a σ τ (Ne.symm hak) hσ hτ),
    levTwoS2d_ofCoord_toStdD n k a σ τ (Ne.symm hak) hσ hτ]
  ext c
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs <;> simp_all

theorem levTwoS2d_toStdD_rRefl_add_apply (n : ℕ) (hn : 4 ≤ n) {k a b : Fin n}
    (hak : a ≠ k) (hbk : b ≠ k) (hab : a ≠ b) {σ τ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    toStdD n
        (weylAction (isFiniteType_cartanD n)
          (rRefl (isFiniteType_cartanD n)
            (levTwoS2d_ofCoord n a b 1 1 hab (Or.inl rfl) (Or.inl rfl)))
          (levTwoS2d_ofCoord n k a σ τ (Ne.symm hak) hσ hτ)) =
      Pi.single k σ - Pi.single b τ := by
  rw [levTwoS2d_toStdD_rRefl_gen n hn hab (Or.inl rfl) (Or.inl rfl)
      (levTwoS2d_ofCoord n k a σ τ (Ne.symm hak) hσ hτ),
    levTwoS2d_ofCoord_toStdD n k a σ τ (Ne.symm hak) hσ hτ]
  ext c
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs <;> simp_all

end CFSG.StandardType.LevTwo
