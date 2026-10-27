module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoBstar

public section

open Polynomial Module CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.StandardType

namespace ChoiceTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Signs

@[expose] def sgnZ (b : Bool) (a : ZMod 3) : ZMod 3 := if b then -a else a

theorem sgnZ_false (a : ZMod 3) : sgnZ false a = a := rfl

theorem sgnZ_true (a : ZMod 3) : sgnZ true a = -a := rfl

theorem sgnZ_sgnZ (b : Bool) (a : ZMod 3) : sgnZ b (sgnZ b a) = a := by
  cases b <;> simp [sgnZ]

theorem sgnZ_zero (b : Bool) : sgnZ b 0 = 0 := by cases b <;> simp [sgnZ]

theorem sgnZ_eq_zero_iff (b : Bool) (a : ZMod 3) : sgnZ b a = 0 ↔ a = 0 := by
  cases b <;> simp [sgnZ]

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]

@[expose] def sgnL (σ : L ≃ₗ[K] L) (b : Bool) : L ≃ₗ[K] L :=
  if b then σ else LinearEquiv.refl K L

variable {σ : L ≃ₗ[K] L} {ζ : L}

theorem sgnL_false (u : L) : sgnL σ false u = u := rfl

theorem sgnL_true (u : L) : sgnL σ true u = σ u := rfl

theorem sgnL_sgnL (hσσ : ∀ u, σ (σ u) = u) (b : Bool) (u : L) : sgnL σ b (sgnL σ b u) = u := by
  cases b
  · rfl
  · exact hσσ u

theorem sgnL_bilin {β : LinearMap.BilinForm K L} (hσβ : ∀ u v, β (σ u) (σ v) = β u v) (b : Bool)
    (u v : L) : β (sgnL σ b u) (sgnL σ b v) = β u v := by
  cases b
  · rfl
  · exact hσβ u v

theorem sigma_pow_mul (hσζ : ∀ u, σ (ζ * u) = ζ ^ 2 * σ u) (m : ℕ) (u : L) :
    σ (ζ ^ m * u) = ζ ^ (2 * m) * σ u := by
  induction m generalizing u with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, mul_assoc, ih, hσζ, ← mul_assoc, ← pow_add]
    congr 2

theorem sgnL_pow_mul (hζ : ζ ^ 3 = 1) (hσζ : ∀ u, σ (ζ * u) = ζ ^ 2 * σ u) (b : Bool)
    (a : ZMod 3) (u : L) : sgnL σ b (ζ ^ a.val * u) = ζ ^ (sgnZ b a).val * sgnL σ b u := by
  cases b
  · rfl
  · rw [sgnL_true, sgnL_true, sigma_pow_mul hσζ, sgnZ_true]
    congr 1
    have hne : ζ ≠ 0 := by
      rintro rfl
      norm_num at hζ
    have h1 : ζ ^ (2 * a.val) * ζ ^ a.val = 1 := by
      rw [← pow_add, show 2 * a.val + a.val = 3 * a.val by ring, pow_mul, hζ, one_pow]
    have h2 : ζ ^ (-a).val * ζ ^ a.val = 1 := by
      rw [← CoordSL.pow_val_add hζ, neg_add_cancel, ZMod.val_zero, pow_zero]
    exact mul_right_cancel₀ (pow_ne_zero _ hne) (h1.trans h2.symm)

end Signs

section Mono

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] {s : ℕ} (σ : L ≃ₗ[K] L)

@[expose] def monoL (π : Equiv.Perm (Fin s)) (η : Fin s → Bool) :
    (Fin s → L) ≃ₗ[K] (Fin s → L) where
  toFun d i := sgnL σ (η i) (d (π i))
  invFun d j := (sgnL σ (η (π.symm j))).symm (d (π.symm j))
  map_add' d d' := funext fun _ => map_add _ _ _
  map_smul' c d := funext fun _ => map_smul _ _ _
  left_inv d := funext fun j => by simp
  right_inv d := funext fun i => by simp

theorem monoL_apply (π : Equiv.Perm (Fin s)) (η : Fin s → Bool) (d : Fin s → L) (i : Fin s) :
    monoL σ π η d i = sgnL σ (η i) (d (π i)) := rfl

@[expose] def moveExp (π : Equiv.Perm (Fin s)) (η : Fin s → Bool) (f : Fin s → ZMod 3) :
    Fin s → ZMod 3 :=
  fun i => sgnZ (η i) (f (π i))

theorem moveExp_apply (π : Equiv.Perm (Fin s)) (η : Fin s → Bool) (f : Fin s → ZMod 3)
    (i : Fin s) : moveExp π η f i = sgnZ (η i) (f (π i)) := rfl

variable {σ} {ζ : L}

theorem monoL_torE (hζ : ζ ^ 3 = 1) (hσζ : ∀ u, σ (ζ * u) = ζ ^ 2 * σ u)
    (π : Equiv.Perm (Fin s)) (η : Fin s → Bool) (f : Fin s → ZMod 3) (d : Fin s → L) :
    monoL σ π η (torE ζ f d) = torE ζ (moveExp π η f) (monoL σ π η d) :=
  funext fun i => sgnL_pow_mul hζ hσζ (η i) (f (π i)) (d (π i))

theorem monoL_isom {β : LinearMap.BilinForm K L} (hσβ : ∀ u v, β (σ u) (σ v) = β u v)
    (π : Equiv.Perm (Fin s)) (η : Fin s → Bool) (d d' : Fin s → L) :
    ∑ i, β (monoL σ π η d i) (monoL σ π η d' i) = ∑ i, β (d i) (d' i) := by
  simp only [monoL_apply, sgnL_bilin hσβ]
  exact Equiv.sum_comp π (fun i => β (d i) (d' i))

end Mono

section Swap

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] {s : ℕ} (σ : L ≃ₗ[K] L)

@[expose] def swapSgn (i j : Fin s) (b : Bool) : Fin s → Bool :=
  fun l => if l = i ∨ l = j then b else false

@[expose] def swapL (i j : Fin s) (b : Bool) : (Fin s → L) ≃ₗ[K] (Fin s → L) :=
  monoL σ (Equiv.swap i j) (swapSgn i j b)

variable {σ}

theorem swapL_apply_left (i j : Fin s) (b : Bool) (d : Fin s → L) :
    swapL σ i j b d i = sgnL σ b (d j) := by
  simp [swapL, monoL_apply, swapSgn]

theorem swapL_apply_right (i j : Fin s) (b : Bool) (d : Fin s → L) :
    swapL σ i j b d j = sgnL σ b (d i) := by
  simp [swapL, monoL_apply, swapSgn]

theorem swapL_apply_of_ne {i j l : Fin s} (b : Bool) (hli : l ≠ i) (hlj : l ≠ j)
    (d : Fin s → L) : swapL σ i j b d l = d l := by
  simp [swapL, monoL_apply, swapSgn, hli, hlj, Equiv.swap_apply_of_ne_of_ne hli hlj, sgnL_false]

theorem swapL_swapL (hσσ : ∀ u, σ (σ u) = u) {i j : Fin s} (hij : i ≠ j) (b : Bool)
    (d : Fin s → L) : swapL σ i j b (swapL σ i j b d) = d := by
  funext l
  by_cases hli : l = i
  · subst hli
    rw [swapL_apply_left, swapL_apply_right, sgnL_sgnL hσσ]
  · by_cases hlj : l = j
    · subst hlj
      rw [swapL_apply_right, swapL_apply_left, sgnL_sgnL hσσ]
    · rw [swapL_apply_of_ne b hli hlj, swapL_apply_of_ne b hli hlj]

variable {ζ : L}

theorem swapL_torE (hζ : ζ ^ 3 = 1) (hσζ : ∀ u, σ (ζ * u) = ζ ^ 2 * σ u) {i j : Fin s}
    (b : Bool) {f : Fin s → ZMod 3} (hf : f i = sgnZ b (f j)) (d : Fin s → L) :
    swapL σ i j b (torE ζ f d) = torE ζ f (swapL σ i j b d) := by
  rw [swapL, monoL_torE hζ hσζ]
  congr 1
  funext l
  rw [moveExp_apply]
  by_cases hli : l = i
  · subst hli
    simp [swapSgn, hf]
  · by_cases hlj : l = j
    · subst hlj
      simp only [swapSgn, or_true, ite_true, Equiv.swap_apply_right]
      rw [hf, sgnZ_sgnZ]
    · simp [swapSgn, hli, hlj, Equiv.swap_apply_of_ne_of_ne hli hlj, sgnZ_false]

end Swap

end ChoiceTwo

end CFSG.StandardType
