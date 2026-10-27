module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08TestLin
public import CFSG.LocalAnalysis.StandardType.GGQ2S08PermLin
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.Fin.Tuple.Sort

public section

namespace CFSG.StandardType.TestLin

open Matrix

variable {r : ℕ}

@[expose] def xLast (r : ℕ) : Vn (r + 1) := Pi.single (Fin.last r) 1

theorem xLast_apply (k : Fin (r + 1)) : xLast r k = if k = Fin.last r then 1 else 0 := by
  simp [xLast, Pi.single_apply]


@[expose] def frameE (r : ℕ) (i : Fin r) : Vn (r + 1) := Pi.single i.castSucc 1
theorem frameE_apply (i : Fin r) (k : Fin (r + 1)) :
    frameE r i k = if k = i.castSucc then 1 else 0 := by
  simp [frameE, Pi.single_apply]

theorem dot_xLast (a : Vn (r + 1)) : a ⬝ᵥ xLast r = a (Fin.last r) := by
  rw [xLast, dotProduct_single, mul_one]

theorem dot_frameE (a : Vn (r + 1)) (i : Fin r) : a ⬝ᵥ frameE r i = a i.castSucc := by
  rw [frameE, dotProduct_single, mul_one]

theorem frameE_dot (c : Vn (r + 1)) (i : Fin r) : frameE r i ⬝ᵥ c = c i.castSucc := by
  rw [frameE, single_dotProduct, one_mul]

theorem dot_frameE_sub (a : Vn (r + 1)) (i j : Fin r) :
    a ⬝ᵥ (frameE r i - frameE r j) = a i.castSucc - a j.castSucc := by
  rw [dotProduct_sub, dot_frameE, dot_frameE]

theorem frameE_sub_dot (c : Vn (r + 1)) (i j : Fin r) :
    (frameE r i - frameE r j) ⬝ᵥ c = c i.castSucc - c j.castSucc := by
  rw [sub_dotProduct, frameE_dot, frameE_dot]

theorem dot_frameE_add (a : Vn (r + 1)) (i j : Fin r) :
    a ⬝ᵥ (frameE r i + frameE r j) = a i.castSucc + a j.castSucc := by
  rw [dotProduct_add, dot_frameE, dot_frameE]

theorem frameE_add_dot (c : Vn (r + 1)) (i j : Fin r) :
    (frameE r i + frameE r j) ⬝ᵥ c = c i.castSucc + c j.castSucc := by
  rw [add_dotProduct, frameE_dot, frameE_dot]

theorem frameE_sub_self (i j : Fin r) (h : i ≠ j) :
    (frameE r i - frameE r j) ⬝ᵥ (frameE r i - frameE r j) = 2 := by
  rw [frameE_sub_dot]
  have hij : i.castSucc ≠ j.castSucc := fun hh => h (Fin.castSucc_injective _ hh)
  simp [frameE, Pi.single_eq_same, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne (Ne.symm hij)]
  decide

theorem frameE_add_self (i j : Fin r) (h : i ≠ j) :
    (frameE r i + frameE r j) ⬝ᵥ (frameE r i + frameE r j) = 2 := by
  rw [frameE_add_dot]
  have hij : i.castSucc ≠ j.castSucc := fun hh => h (Fin.castSucc_injective _ hh)
  simp [frameE, Pi.single_eq_same, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne (Ne.symm hij)]
  decide

@[expose] def sgnDiff (i j : Fin r) (h : i ≠ j) : Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1) :=
  refl (Pi.single i.castSucc 1 - Pi.single j.castSucc 1)
    (Pi.single i.castSucc 1 - Pi.single j.castSucc 1)
    (dot_sub_single_self i.castSucc j.castSucc
      (fun hh => h (Fin.castSucc_injective _ hh)))

@[expose] def sgnSum (i j : Fin r) (h : i ≠ j) : Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1) :=
  refl (frameE r i + frameE r j) (frameE r i + frameE r j) (frameE_add_self i j h)

theorem sgnFlip_dot (i : Fin r) : ((2 : ZMod 3) • frameE r i) ⬝ᵥ frameE r i = 2 := by
  rw [smul_dotProduct, frameE_dot]
  simp [frameE]

@[expose] def sgnFlip (i : Fin r) : Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1) :=
  refl (frameE r i) ((2 : ZMod 3) • frameE r i) (sgnFlip_dot i)

theorem sgnFlip_apply (i : Fin r) (v : Vn (r + 1)) :
    sgnFlip i v = v - ((2 : ZMod 3) * v i.castSucc) • frameE r i := by
  rw [sgnFlip, refl_apply, smul_dotProduct, frameE_dot, smul_eq_mul]

theorem sgnFlip_coord (i : Fin r) (v : Vn (r + 1)) (k : Fin (r + 1)) :
    sgnFlip i v k = if k = i.castSucc then -v i.castSucc else v k := by
  rw [sgnFlip_apply]
  by_cases hk : k = i.castSucc
  · subst hk
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, frameE, Pi.single_eq_same,
      if_true]
    ring
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, frameE,
      Pi.single_eq_of_ne hk, if_neg hk, mul_zero, sub_zero]

theorem zmod3_trichotomy : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = -1 := by decide

theorem zmod3_ne_zero : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 := by decide

theorem zmod3_sq_eq_one (x : ZMod 3) (hx : x ≠ 0) : x * x = 1 := by
  rcases zmod3_ne_zero x hx with h | h
  · simp [h]
  · simp [h]

theorem zmod3_eq_or_eq_neg {x y : ZMod 3} (hx : x ≠ 0) (hy : y ≠ 0) :
    y = x ∨ y = -x := by
  rcases zmod3_ne_zero x hx with hx | hx <;> rcases zmod3_ne_zero y hy with hy | hy
  · left; rw [hx, hy]
  · right; rw [hx, hy]
  · right; rw [hx, hy]; norm_num
  · left; rw [hx, hy]

theorem zmod3_two_mul_ne_zero (x : ZMod 3) (hx : x ≠ 0) : (2 : ZMod 3) * x ≠ 0 := by
  rcases zmod3_ne_zero x hx with h | h <;> rw [h] <;> decide

theorem zmod3_two_mul_eq_zero (x : ZMod 3) : (2 : ZMod 3) * x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact zmod3_two_mul_ne_zero x hx h
  · intro h; rw [h, mul_zero]

theorem sym_frame_B {c a : Vn (r + 1)}
    (hD : ∀ i j, i ≠ j → (a ⬝ᵥ (frameE r i - frameE r j) = 0 ↔
      (frameE r i - frameE r j) ⬝ᵥ c = 0))
    (hS : ∀ i j, i ≠ j → (a ⬝ᵥ (frameE r i + frameE r j) = 0 ↔
      (frameE r i + frameE r j) ⬝ᵥ c = 0))
    (hF : ∀ i : Fin r, (a i.castSucc = 0 ↔ c i.castSucc = 0)) :
    ∃ l : ZMod 3, ∀ i : Fin r, a i.castSucc = l * c i.castSucc := by
  classical
  have hD' : ∀ (i j : Fin r) (h : i ≠ j),
      a i.castSucc - a j.castSucc = 0 ↔ c i.castSucc - c j.castSucc = 0 := by
    intro i j h
    rw [← dot_frameE_sub, ← frameE_sub_dot]
    exact hD i j h
  have hS' : ∀ (i j : Fin r) (h : i ≠ j),
      a i.castSucc + a j.castSucc = 0 ↔ c i.castSucc + c j.castSucc = 0 := by
    intro i j h
    rw [← dot_frameE_add, ← frameE_add_dot]
    exact hS i j h
  by_cases hc : ∃ i : Fin r, c i.castSucc ≠ 0
  · obtain ⟨i0, hi0⟩ := hc
    refine ⟨a i0.castSucc * c i0.castSucc, fun j => ?_⟩
    have hsq : c i0.castSucc * c i0.castSucc = 1 := zmod3_sq_eq_one _ hi0
    by_cases hj : j = i0
    · subst hj
      rw [mul_assoc, hsq, mul_one]
    · by_cases hcj : c j.castSucc = 0
      · have haj : a j.castSucc = 0 := (hF j).mpr hcj
        rw [haj, hcj, mul_zero]
      · set t : ZMod 3 := c j.castSucc * c i0.castSucc with ht
        have htc : t * c i0.castSucc = c j.castSucc := by
          rw [ht, mul_assoc, hsq, mul_one]
        have htne : t ≠ 0 := by
          intro h0
          rw [h0, zero_mul] at htc
          exact hcj htc.symm
        rcases zmod3_ne_zero t htne with ht1 | ht1
        · have hcjeq : c j.castSucc = c i0.castSucc := by rw [← htc, ht1, one_mul]
          have hai : a i0.castSucc - a j.castSucc = 0 :=
            (hD' i0 j (Ne.symm hj)).mpr (by rw [hcjeq, sub_self])
          have haj : a j.castSucc = a i0.castSucc := (sub_eq_zero.mp hai).symm
          rw [haj, hcjeq, mul_assoc, hsq, mul_one]
        · have hcjeq : c j.castSucc = -c i0.castSucc := by
            rw [← htc, ht1, neg_one_mul]
          have hai : a i0.castSucc + a j.castSucc = 0 :=
            (hS' i0 j (Ne.symm hj)).mpr (by rw [hcjeq]; abel)
          have haj : a j.castSucc = -a i0.castSucc := by
            rw [eq_neg_iff_add_eq_zero, add_comm]
            exact hai
          rw [haj, hcjeq]
          have : (a i0.castSucc * c i0.castSucc) * -c i0.castSucc = -a i0.castSucc := by
            rw [mul_neg, mul_assoc, hsq, mul_one]
          rw [this]
  · simp only [not_exists, not_not] at hc
    refine ⟨0, fun i => ?_⟩
    have hci : c i.castSucc = 0 := hc i
    have hai : a i.castSucc = 0 := (hF i).mpr hci
    rw [hai, hci, mul_zero]

def optFin (r : ℕ) : Option (Fin r) ≃ Fin (r + 1) := finSuccEquivLast.symm

theorem optFin_none (r : ℕ) : optFin r none = Fin.last r := finSuccEquivLast_symm_none

theorem optFin_some (r : ℕ) (i : Fin r) : optFin r (some i) = i.castSucc :=
  finSuccEquivLast_symm_some i

@[expose] def extFramePerm (σ : Equiv.Perm (Fin r)) : Equiv.Perm (Fin (r + 1)) :=
  (optFin r).symm.trans ((Equiv.optionCongr σ).trans (optFin r))

theorem extFramePerm_one : extFramePerm (1 : Equiv.Perm (Fin r)) = 1 := by
  ext i
  simp [extFramePerm, optFin, Equiv.optionCongr]

theorem extFramePerm_mul (σ τ : Equiv.Perm (Fin r)) :
    extFramePerm (σ * τ) = extFramePerm σ * extFramePerm τ := by
  ext i
  simp [extFramePerm, optFin, Equiv.optionCongr, Equiv.Perm.mul_apply]

theorem extFramePerm_swap (i j : Fin r) (_h : i ≠ j) :
    extFramePerm (Equiv.swap i j) = Equiv.swap i.castSucc j.castSucc := by
  rw [extFramePerm, Equiv.optionCongr_swap]
  rw [← Equiv.trans_assoc]
  rw [Equiv.symm_trans_swap_trans]
  simp [optFin, finSuccEquivLast_symm_some]

theorem extFramePerm_castSucc (σ : Equiv.Perm (Fin r)) (i : Fin r) :
    extFramePerm σ i.castSucc = (σ i).castSucc := by
  simp [extFramePerm, optFin, Equiv.optionCongr]

theorem extFramePerm_last (σ : Equiv.Perm (Fin r)) :
    extFramePerm σ (Fin.last r) = Fin.last r := by
  simp [extFramePerm, optFin, Equiv.optionCongr]

theorem extFramePerm_symm_castSucc (σ : Equiv.Perm (Fin r)) (i : Fin r) :
    (extFramePerm σ).symm i.castSucc = (σ⁻¹ i).castSucc := by
  rw [Equiv.symm_apply_eq, extFramePerm_castSucc]
  simp

theorem extFramePerm_symm_last (σ : Equiv.Perm (Fin r)) :
    (extFramePerm σ).symm (Fin.last r) = Fin.last r := by
  rw [Equiv.symm_apply_eq, extFramePerm_last]

@[expose] def framePerm (σ : Equiv.Perm (Fin r)) : Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1) :=
  permN (extFramePerm σ)

theorem framePerm_one : framePerm (1 : Equiv.Perm (Fin r)) = 1 := by
  rw [framePerm, extFramePerm_one]
  apply LinearEquiv.ext
  intro v
  funext i
  rfl

theorem framePerm_mul (σ τ : Equiv.Perm (Fin r)) :
    framePerm (σ * τ) = framePerm σ * framePerm τ := by
  rw [framePerm, extFramePerm_mul, permN_mul]
  rfl

theorem framePerm_swap (i j : Fin r) (h0 : i ≠ j) :
    framePerm (Equiv.swap i j) = sgnDiff i j h0 := by
  have hij : i.castSucc ≠ j.castSucc := fun hh => h0 (Fin.castSucc_injective _ hh)
  rw [framePerm, extFramePerm_swap i j h0]
  exact permN_swap i.castSucc j.castSucc hij

theorem framePerm_apply_castSucc (σ : Equiv.Perm (Fin r)) (v : Vn (r + 1)) (i : Fin r) :
    framePerm σ v i.castSucc = v (σ⁻¹ i).castSucc := by
  rw [framePerm, permN_apply, extFramePerm_symm_castSucc]

theorem framePerm_apply_last (σ : Equiv.Perm (Fin r)) (v : Vn (r + 1)) :
    framePerm σ v (Fin.last r) = v (Fin.last r) := by
  rw [framePerm, permN_apply, extFramePerm_symm_last]

theorem framePerm_xLast (σ : Equiv.Perm (Fin r)) : framePerm σ (xLast r) = xLast r := by
  funext k
  cases k using Fin.lastCases with
  | last => rw [framePerm_apply_last]
  | cast j =>
      rw [framePerm_apply_castSucc]
      have h1 : (σ⁻¹ j).castSucc ≠ Fin.last r := by
        intro hh
        have hval := congrArg Fin.val hh
        simp only [Fin.val_last, Fin.val_castSucc] at hval
        omega
      have h2 : j.castSucc ≠ Fin.last r := by
        intro hh
        have hval := congrArg Fin.val hh
        simp only [Fin.val_last, Fin.val_castSucc] at hval
        omega
      simp [xLast]

theorem framePerm_conj_refl (σ : Equiv.Perm (Fin r)) (c a : Vn (r + 1))
    (h : a ⬝ᵥ c = 2) :
    framePerm σ * refl c a h * (framePerm σ)⁻¹ =
      refl (c ∘ (extFramePerm σ).symm) (a ∘ (extFramePerm σ).symm)
        (by
          rw [dotProduct_comp_equiv_symm]
          simpa [Function.comp_def] using h) := by
  rw [framePerm]
  exact permN_conj_refl (extFramePerm σ) c a h

theorem framePerm_conj_sgnFlip (σ : Equiv.Perm (Fin r)) (i : Fin r) :
    framePerm σ * sgnFlip i * (framePerm σ)⁻¹ = sgnFlip (σ i) := by
  rw [sgnFlip, framePerm_conj_refl]
  congr 1
  · funext k
    cases k using Fin.lastCases with
    | last => simp [frameE, extFramePerm_symm_last]
    | cast j =>
        simp only [Function.comp_def, frameE, Pi.single_apply, extFramePerm_symm_castSucc,
          Fin.castSucc_inj]
        by_cases h : j = σ i
        · have h1 : σ⁻¹ j = i := by
            rw [h]
            exact Equiv.symm_apply_apply σ i
          rw [h1, h]
          simp
        · have h1 : σ⁻¹ j ≠ i := by
            intro hh
            apply h
            rw [← hh]
            exact (Equiv.apply_symm_apply σ j).symm
          rw [if_neg h1, if_neg h]
  · funext k
    cases k using Fin.lastCases with
    | last => simp [frameE, Pi.smul_apply, extFramePerm_symm_last]
    | cast j =>
        simp only [Function.comp_def, frameE, Pi.smul_apply, Pi.single_apply,
          extFramePerm_symm_castSucc, Fin.castSucc_inj]
        by_cases h : j = σ i
        · have h1 : σ⁻¹ j = i := by
            rw [h]
            exact Equiv.symm_apply_apply σ i
          rw [h1, h]
          simp
        · have h1 : σ⁻¹ j ≠ i := by
            intro hh
            apply h
            rw [← hh]
            exact (Equiv.apply_symm_apply σ j).symm
          rw [if_neg h1, if_neg h]

theorem framePerm_conj_sgnSum (σ : Equiv.Perm (Fin r)) (i j : Fin r) (h : i ≠ j)
    (h' : σ i ≠ σ j) :
    framePerm σ * sgnSum i j h * (framePerm σ)⁻¹ = sgnSum (σ i) (σ j) h' := by
  rw [sgnSum, framePerm_conj_refl]
  congr 1 <;>
    (funext k
     cases k using Fin.lastCases with
     | last => simp [frameE, Pi.add_apply, extFramePerm_symm_last]
     | cast l =>
         simp only [Function.comp_def, frameE, Pi.add_apply, Pi.single_apply,
           extFramePerm_symm_castSucc, Fin.castSucc_inj]
         by_cases hi : l = σ i <;> by_cases hj : l = σ j <;>
           simp [Equiv.symm_apply_eq, hi, hj])

theorem framePerm_mem_adj {W : Subgroup (Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1))}
    (hW : ∀ (i : Fin r) (h : i.val + 1 < r),
      sgnDiff i ⟨i.val + 1, h⟩ (by
        intro hh; have := congrArg Fin.val hh; simp only at this; omega) ∈ W)
    (σ : Equiv.Perm (Fin r)) : framePerm σ ∈ W := by
  cases r with
  | zero =>
      have h1 : σ = 1 := Subsingleton.elim σ 1
      rw [h1, framePerm_one]
      exact W.one_mem
  | succ m =>
      have hσ : σ ∈ Submonoid.closure
          (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
        rw [Equiv.Perm.mclosure_swap_castSucc_succ]
        exact Submonoid.mem_top σ
      induction hσ using Submonoid.closure_induction with
      | mem τ hτ =>
          obtain ⟨i, rfl⟩ := hτ
          rw [framePerm_swap]
          exact hW i.castSucc (by simp)
      | one => rw [framePerm_one]; exact W.one_mem
      | mul a b ha hb iha ihb => rw [framePerm_mul]; exact W.mul_mem iha ihb

@[expose] def flipSign (S : Finset (Fin r)) (i : Fin (r + 1)) : ZMod 3 :=
  Fin.lastCases 1 (fun j => if j ∈ S then -1 else 1) i

theorem flipSign_last (S : Finset (Fin r)) : flipSign S (Fin.last r) = 1 := by
  simp [flipSign]

theorem flipSign_castSucc (S : Finset (Fin r)) (i : Fin r) :
    flipSign S i.castSucc = if i ∈ S then -1 else 1 := by
  simp [flipSign]

theorem flipSign_mul_self (S : Finset (Fin r)) (i : Fin (r + 1)) :
    flipSign S i * flipSign S i = 1 := by
  cases i using Fin.lastCases with
  | last => rw [flipSign_last]; norm_num
  | cast j => rw [flipSign_castSucc]; split_ifs <;> norm_num

@[expose] def frameFlip (S : Finset (Fin r)) : Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1) where
  toFun v := fun i => flipSign S i * v i
  invFun v := fun i => flipSign S i * v i
  map_add' v w := by funext i; simp only [Pi.add_apply]; ring
  map_smul' c v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  left_inv v := by
    funext i
    show flipSign S i * (flipSign S i * v i) = v i
    rw [← mul_assoc, flipSign_mul_self, one_mul]
  right_inv v := by
    funext i
    show flipSign S i * (flipSign S i * v i) = v i
    rw [← mul_assoc, flipSign_mul_self, one_mul]

theorem frameFlip_apply (S : Finset (Fin r)) (v : Vn (r + 1)) (i : Fin (r + 1)) :
    frameFlip S v i = flipSign S i * v i := rfl

theorem frameFlip_xLast (S : Finset (Fin r)) : frameFlip S (xLast r) = xLast r := by
  funext k
  rw [frameFlip_apply]
  cases k using Fin.lastCases with
  | last => rw [flipSign_last, one_mul]
  | cast j => simp [flipSign, xLast]

theorem frameFlip_empty : frameFlip (∅ : Finset (Fin r)) = 1 := by
  apply LinearEquiv.ext
  intro v
  funext k
  rw [frameFlip_apply]
  cases k using Fin.lastCases with
  | last => rw [flipSign_last]; simp
  | cast j => simp [flipSign]

theorem frameFlip_insert (i : Fin r) (S : Finset (Fin r)) (hi : i ∉ S) :
    frameFlip (insert i S) = sgnFlip i * frameFlip S := by
  apply LinearEquiv.ext
  intro v
  funext k
  rw [LinearEquiv.mul_apply, sgnFlip_coord, frameFlip_apply]
  simp only [frameFlip_apply]
  cases k using Fin.lastCases with
  | last =>
      rw [flipSign_last, flipSign_last]
      have h : ¬ (Fin.last r = i.castSucc) := by
        intro hh
        have hv := congrArg Fin.val hh
        simp only [Fin.val_last, Fin.val_castSucc] at hv
        omega
      rw [if_neg h]
  | cast j =>
      rw [flipSign_castSucc, flipSign_castSucc]
      by_cases hji : j = i
      · rw [hji] at *
        rw [if_pos (Finset.mem_insert_self i S), if_neg hi, if_pos rfl]
        simp
      · have hki : ¬ (j.castSucc = i.castSucc) := fun hh => hji (Fin.castSucc_injective _ hh)
        have hmem : (j ∈ insert i S) ↔ (j ∈ S) := by
          rw [Finset.mem_insert]
          exact ⟨fun h => h.resolve_left hji, fun h => Or.inr h⟩
        rw [if_neg hki, if_congr hmem rfl rfl, flipSign_castSucc]

theorem frameFlip_mem {W : Subgroup (Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1))}
    (hW : ∀ i, sgnFlip i ∈ W) (S : Finset (Fin r)) : frameFlip S ∈ W := by
  induction S using Finset.induction with
  | empty => rw [frameFlip_empty]; exact W.one_mem
  | insert i S hi ih => rw [frameFlip_insert i S hi]; exact W.mul_mem (hW i) ih

theorem sgnDiff_mul_self (i j : Fin r) (h : i ≠ j) :
    sgnDiff i j h * sgnDiff i j h = 1 := by
  rw [sgnDiff]
  exact refl_mul_self _ _ _

theorem sgnSum_eq (i j : Fin r) (h : i ≠ j) :
    sgnSum i j h = sgnFlip i * sgnFlip j * sgnDiff i j h := by
  apply LinearEquiv.ext
  intro v
  funext k
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  simp only [sgnFlip, sgnSum, sgnDiff]
  rw [refl_apply, refl_apply, refl_apply, refl_apply]
  by_cases hki : k = i.castSucc
  · subst hki
    simp [frameE, h, Ne.symm h]
    ring_nf
  · by_cases hkj : k = j.castSucc
    · subst hkj
      simp [frameE, h, hki]
      ring_nf
    · simp [frameE, h, Ne.symm h, hki, hkj]

theorem sgnFlip_mul_sgnFlip_mem {W : Subgroup (Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1))}
    (hWd : ∀ (i j : Fin r) (h : i ≠ j), sgnDiff i j h ∈ W)
    (hWs : ∀ (i j : Fin r) (h : i ≠ j), sgnSum i j h ∈ W)
    {i j : Fin r} (h : i ≠ j) : sgnFlip i * sgnFlip j ∈ W := by
  have hsum := hWs i j h
  have hdiff := hWd i j h
  have hEq : sgnSum i j h * sgnDiff i j h = sgnFlip i * sgnFlip j := by
    rw [sgnSum_eq i j h, mul_assoc, sgnDiff_mul_self, mul_one]
  rw [← hEq]
  exact W.mul_mem hsum hdiff

theorem frameFlip_mem_even {W : Subgroup (Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1))}
    (hWd : ∀ (i j : Fin r) (h : i ≠ j), sgnDiff i j h ∈ W)
    (hWs : ∀ (i j : Fin r) (h : i ≠ j), sgnSum i j h ∈ W)
    (S : Finset (Fin r)) (hS : Even S.card) : frameFlip S ∈ W := by
  classical
  let P : ℕ → Prop := fun n => ∀ S : Finset (Fin r), S.card = n →
    Even S.card → frameFlip S ∈ W
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro S hcard hseven
      rcases Finset.eq_empty_or_nonempty S with rfl | hne
      · rw [frameFlip_empty]
        exact W.one_mem
      · have h2 : 2 ≤ S.card := by
          obtain ⟨m, hm⟩ := hseven
          obtain ⟨i, hi⟩ := hne
          have hpos : 0 < S.card := Finset.card_pos.mpr ⟨i, hi⟩
          omega
        obtain ⟨i, hiS⟩ := hne
        have herase : (S.erase i).card = S.card - 1 := Finset.card_erase_of_mem hiS
        have hne2 : (S.erase i).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro h0
          have hc0 : (S.erase i).card = 0 := by rw [h0]; simp
          omega
        obtain ⟨j, hj⟩ := hne2
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        have hjS : j ∈ S := Finset.mem_of_mem_erase hj
        let S' : Finset (Fin r) := (S.erase i).erase j
        have hS'eq : S = insert i (insert j S') := by
          rw [← Finset.insert_erase hiS, ← Finset.insert_erase hj]
        have hcard' : S'.card = S.card - 2 := by
          have h1 : S'.card = (S.erase i).card - 1 := Finset.card_erase_of_mem hj
          omega
        have hlt : S'.card < n := by omega
        have heven' : Even S'.card := by
          obtain ⟨m, hm⟩ := hseven
          have : S'.card = 2 * m - 2 := by omega
          rw [this]
          exact ⟨m - 1, by omega⟩
        have ihS' : frameFlip S' ∈ W := ih S'.card hlt S' rfl heven'
        have hni : i ∉ insert j S' := by
          intro hh
          rcases Finset.mem_insert.mp hh with rfl | hh'
          · exact hji rfl
          · rcases Finset.mem_erase.mp hh' with ⟨_, hh''⟩
            exact (Finset.mem_erase.mp hh'').1 rfl
        have hnj : j ∉ S' := by
          simp only [S', Finset.mem_erase]
          exact fun h => h.1 rfl
        rw [hS'eq, frameFlip_insert i (insert j S') hni,
          frameFlip_insert j S' hnj]
        rw [← mul_assoc]
        exact W.mul_mem (sgnFlip_mul_sgnFlip_mem hWd hWs (Ne.symm hji)) ihS'
  exact hP S.card S rfl hS

@[expose] def canonC (r k : ℕ) (g : ZMod 3) : Vn (r + 1) :=
  fun i => if i.val < r then (if r - k ≤ i.val then 1 else 0) else g

@[expose] def canonA (r k : ℕ) (l d : ZMod 3) : Vn (r + 1) :=
  fun i => if i.val < r then (if r - k ≤ i.val then l else 0) else d

theorem canonC_castSucc (k : ℕ) (g : ZMod 3) (i : Fin r) :
    canonC r k g i.castSucc = if r - k ≤ i.val then 1 else 0 := by
  simp [canonC, i.isLt]

theorem canonC_last (k : ℕ) (g : ZMod 3) : canonC r k g (Fin.last r) = g := by
  simp [canonC, Fin.val_last]

theorem canonA_castSucc (k : ℕ) (l d : ZMod 3) (i : Fin r) :
    canonA r k l d i.castSucc = if r - k ≤ i.val then l else 0 := by
  simp [canonA, i.isLt]

theorem canonA_last (k : ℕ) (l d : ZMod 3) : canonA r k l d (Fin.last r) = d := by
  simp [canonA, Fin.val_last]

@[expose] def canonD (r : ℕ) (g : ZMod 3) : Vn (r + 1) :=
  fun i => if i.val < r then (if i.val = r - 1 then 2 else 1) else g

@[expose] def canonAD (r : ℕ) (l d : ZMod 3) : Vn (r + 1) :=
  fun i => if i.val < r then (if i.val = r - 1 then 2 * l else l) else d

theorem canonD_castSucc (g : ZMod 3) (i : Fin r) :
    canonD r g i.castSucc = if i.val = r - 1 then 2 else 1 := by
  simp [canonD, i.isLt]

theorem canonD_last (g : ZMod 3) : canonD r g (Fin.last r) = g := by
  simp [canonD, Fin.val_last]

theorem canonAD_castSucc (l d : ZMod 3) (i : Fin r) :
    canonAD r l d i.castSucc = if i.val = r - 1 then 2 * l else l := by
  simp [canonAD, i.isLt]

theorem canonAD_last (l d : ZMod 3) : canonAD r l d (Fin.last r) = d := by
  simp [canonAD, Fin.val_last]

private theorem finset_fin_eq_filter_val_lt {r k : ℕ} (S : Finset (Fin r))
    (hdown : ∀ i ∈ S, ∀ j : Fin r, j ≤ i → j ∈ S) (hcard : S.card = r - k) :
    S = Finset.univ.filter (fun i : Fin r => i.val < r - k) := by
  ext i
  constructor
  · intro hi
    by_contra hlt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hlt
    have hsub : Finset.Iic i ⊆ S := fun j hj => hdown i hi j (Finset.mem_Iic.mp hj)
    have hle := Finset.card_le_card hsub
    rw [hcard, Fin.card_Iic] at hle
    omega
  · intro hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    by_contra hni
    have hsub : S ⊆ Finset.Iio i := by
      intro j hj
      rw [Finset.mem_Iio]
      by_contra hji
      have hij : i ≤ j := Nat.le_of_not_lt hji
      exact hni (hdown j hj i hij)
    have hle := Finset.card_le_card hsub
    rw [hcard, Fin.card_Iio] at hle
    omega

theorem exists_frame_canonical_B {W : Subgroup (Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1))}
    (hW : ∀ (i j : Fin r) (h : i ≠ j), sgnDiff i j h ∈ W)
    (hWf : ∀ i, sgnFlip i ∈ W)
    {c : Vn (r + 1)} (hcH : ∃ i : Fin r, c i.castSucc ≠ 0) :
    ∃ w ∈ W, ∃ k : ℕ, 1 ≤ k ∧ k ≤ r ∧ w (xLast r) = xLast r ∧
      (w c) (Fin.last r) = c (Fin.last r) ∧
      (∀ i : Fin r, (w c) i.castSucc = if r - k ≤ i.val then 1 else 0) := by
  classical
  let key : Fin r → ℕ := fun i => if c i.castSucc = 0 then 0 else 1
  let σ : Equiv.Perm (Fin r) := Tuple.sort key
  have hmono : Monotone (fun i => key (σ i)) := by
    simpa only [Function.comp_def] using Tuple.monotone_sort key
  let Z : Finset (Fin r) := Finset.univ.filter (fun i => key (σ i) = 0)
  let k : ℕ := (Finset.univ.filter (fun i : Fin r => key (σ i) = 1)).card
  have hkey01 : ∀ i : Fin r, key i = 0 ∨ key i = 1 := by
    intro i
    dsimp only [key]
    split_ifs <;> simp
  have hnot : (Finset.univ.filter (fun i : Fin r => ¬ key (σ i) = 0)) =
      Finset.univ.filter (fun i : Fin r => key (σ i) = 1) := by
    apply Finset.filter_congr
    intro i _
    constructor
    · intro h
      rcases hkey01 (σ i) with h1 | h1
      · exact absurd h1 h
      · exact h1
    · intro h h0
      rw [h] at h0
      exact (by decide : (1 : ℕ) ≠ 0) h0
  have hcard : Z.card = r - k := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (p := fun i : Fin r => key (σ i) = 0)
    have h2 : (Finset.univ.filter (fun i : Fin r => ¬ key (σ i) = 0)).card = k := by
      rw [hnot]
    rw [Finset.card_univ, Fintype.card_fin] at h
    dsimp only [Z]
    omega
  have hdown : ∀ i ∈ Z, ∀ j : Fin r, j ≤ i → j ∈ Z := by
    intro i hi j hj
    dsimp only [Z] at hi ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have hle : key (σ j) ≤ key (σ i) := hmono hj
    omega
  have hZeq : Z = Finset.univ.filter (fun i : Fin r => i.val < r - k) :=
    finset_fin_eq_filter_val_lt Z hdown hcard
  let w1 : Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1) := framePerm σ⁻¹
  have hw1 : ∀ i : Fin r, (w1 c) i.castSucc = c (σ i).castSucc := by
    intro i
    change framePerm σ⁻¹ c i.castSucc = c (σ i).castSucc
    rw [framePerm_apply_castSucc, inv_inv]
  have hw1zero : ∀ i : Fin r, (w1 c) i.castSucc = 0 ↔ i.val < r - k := by
    intro i
    rw [hw1]
    have h1 : key (σ i) = 0 ↔ c (σ i).castSucc = 0 := by
      dsimp only [key]
      split_ifs <;> simp_all
    rw [← h1]
    have h2 : i ∈ Z ↔ i.val < r - k := by
      rw [hZeq]
      simp
    rw [← h2]
    dsimp only [Z]
    simp
  let S : Finset (Fin r) := Finset.univ.filter (fun i => (w1 c) i.castSucc = 2)
  let w : Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1) := frameFlip S * w1
  have hwW : w ∈ W :=
    W.mul_mem (frameFlip_mem hWf S)
      (framePerm_mem_adj (fun i h => hW i ⟨i.val + 1, h⟩ _) σ⁻¹)
  have hmemS : ∀ i : Fin r, i ∈ S ↔ (w1 c) i.castSucc = 2 := by
    intro i
    dsimp only [S]
    simp
  have hval : ∀ i : Fin r, (w c) i.castSucc = if r - k ≤ i.val then 1 else 0 := by
    intro i
    change (frameFlip S (w1 c)) i.castSucc = _
    rw [frameFlip_apply, flipSign_castSucc]
    by_cases hlt : r - k ≤ i.val
    · have hne : (w1 c) i.castSucc ≠ 0 := by
        intro h0
        have hlt2 := (hw1zero i).mp h0
        omega
      rw [if_pos hlt]
      by_cases h2 : (w1 c) i.castSucc = 2
      · rw [if_pos ((hmemS i).mpr h2), h2]
        decide
      · have h1 : (w1 c) i.castSucc = 1 := by
          rcases zmod3_ne_zero _ hne with h | h
          · exact h
          · exact absurd h h2
        rw [if_neg (fun hh => h2 ((hmemS i).mp hh)), h1]
        decide
    · have h0 : (w1 c) i.castSucc = 0 :=
        (hw1zero i).mpr (Nat.lt_of_not_le hlt)
      have hnotS : i ∉ S := fun hh => by
        have h2 : (w1 c) i.castSucc = 2 := (hmemS i).mp hh
        rw [h0] at h2
        exact (by decide : (0 : ZMod 3) ≠ 2) h2
      rw [if_neg hlt, if_neg hnotS, h0, mul_zero]
  have hlast : (w c) (Fin.last r) = c (Fin.last r) := by
    change (frameFlip S (w1 c)) (Fin.last r) = c (Fin.last r)
    rw [frameFlip_apply, flipSign_last, one_mul]
    change framePerm σ⁻¹ c (Fin.last r) = c (Fin.last r)
    rw [framePerm_apply_last]
  have hk1 : 1 ≤ k := by
    obtain ⟨i0, hi0⟩ := hcH
    have hmem : σ.symm i0 ∈ Finset.univ.filter (fun i : Fin r => key (σ i) = 1) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp only [key]
      rw [show σ (σ.symm i0) = i0 from Equiv.apply_symm_apply σ i0]
      rw [if_neg hi0]
    have hpos : 0 < k := by
      dsimp only [k]
      exact Finset.card_pos.mpr ⟨_, hmem⟩
    omega
  have hk2 : k ≤ r := by
    dsimp only [k]
    calc (Finset.univ.filter (fun i : Fin r => key (σ i) = 1)).card
        ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = r := by simp
  have hwx : w (xLast r) = xLast r := by
    dsimp only [w]
    rw [LinearEquiv.mul_apply, framePerm_xLast, frameFlip_xLast]
  exact ⟨w, hwW, k, hk1, hk2, hwx, hlast, hval⟩

theorem exists_frame_canonical_D {W : Subgroup (Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1))}
    (hr : 3 ≤ r)
    (hWd : ∀ (i j : Fin r) (h : i ≠ j), sgnDiff i j h ∈ W)
    (hWs : ∀ (i j : Fin r) (h : i ≠ j), sgnSum i j h ∈ W)
    {c : Vn (r + 1)} (hcH : ∃ i : Fin r, c i.castSucc ≠ 0) :
    ∃ w ∈ W, ∃ k : ℕ, 1 ≤ k ∧ k ≤ r ∧ w (xLast r) = xLast r ∧
      (w c) (Fin.last r) = c (Fin.last r) ∧
      ((∀ i : Fin r, (w c) i.castSucc = if r - k ≤ i.val then 1 else 0) ∨
       (k = r ∧ ∀ i : Fin r, (w c) i.castSucc = if i.val = r - 1 then 2 else 1)) := by
  let key : Fin r → ℕ := fun i => if c i.castSucc = 0 then 0 else 1
  let σ : Equiv.Perm (Fin r) := Tuple.sort key
  have hmono : Monotone (fun i => key (σ i)) := by
    simpa only [Function.comp_def] using Tuple.monotone_sort key
  let Z : Finset (Fin r) := Finset.univ.filter (fun i => key (σ i) = 0)
  let k : ℕ := (Finset.univ.filter (fun i : Fin r => key (σ i) = 1)).card
  have hkey01 : ∀ i : Fin r, key i = 0 ∨ key i = 1 := by
    intro i
    dsimp only [key]
    split_ifs <;> simp
  have hnot : (Finset.univ.filter (fun i : Fin r => ¬ key (σ i) = 0)) =
      Finset.univ.filter (fun i : Fin r => key (σ i) = 1) := by
    apply Finset.filter_congr
    intro i _
    constructor
    · intro h
      rcases hkey01 (σ i) with h1 | h1
      · exact absurd h1 h
      · exact h1
    · intro h h0
      rw [h] at h0
      exact (by decide : (1 : ℕ) ≠ 0) h0
  have hcard : Z.card = r - k := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (p := fun i : Fin r => key (σ i) = 0)
    have h2 : (Finset.univ.filter (fun i : Fin r => ¬ key (σ i) = 0)).card = k := by
      rw [hnot]
    rw [Finset.card_univ, Fintype.card_fin] at h
    dsimp only [Z]
    omega
  have hdown : ∀ i ∈ Z, ∀ j : Fin r, j ≤ i → j ∈ Z := by
    intro i hi j hj
    dsimp only [Z] at hi ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have hle : key (σ j) ≤ key (σ i) := hmono hj
    omega
  have hZeq : Z = Finset.univ.filter (fun i : Fin r => i.val < r - k) :=
    finset_fin_eq_filter_val_lt Z hdown hcard
  let w1 : Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1) := framePerm σ⁻¹
  have hw1 : ∀ i : Fin r, (w1 c) i.castSucc = c (σ i).castSucc := by
    intro i
    change framePerm σ⁻¹ c i.castSucc = c (σ i).castSucc
    rw [framePerm_apply_castSucc, inv_inv]
  have hw1zero : ∀ i : Fin r, (w1 c) i.castSucc = 0 ↔ i.val < r - k := by
    intro i
    rw [hw1]
    have h1 : key (σ i) = 0 ↔ c (σ i).castSucc = 0 := by
      dsimp only [key]
      split_ifs <;> simp_all
    rw [← h1]
    have h2 : i ∈ Z ↔ i.val < r - k := by
      rw [hZeq]
      simp
    rw [← h2]
    dsimp only [Z]
    simp
  have hw1W : w1 ∈ W :=
    framePerm_mem_adj (fun i h => hWd i ⟨i.val + 1, h⟩ _) σ⁻¹
  let S : Finset (Fin r) := Finset.univ.filter (fun i => (w1 c) i.castSucc = 2)
  have hmemS : ∀ i : Fin r, i ∈ S ↔ (w1 c) i.castSucc = 2 := by
    intro i
    dsimp only [S]
    simp
  have hflip_erase (z : Fin r) (hz : z ∈ S) (i : Fin r) (hiz : i ≠ z) :
      (if i ∈ S.erase z then (-1 : ZMod 3) else 1) = (if i ∈ S then -1 else 1) := by
    congr 1
    exact propext (by
      rw [Finset.mem_erase]
      exact ⟨fun h => h.2, fun h => ⟨hiz, h⟩⟩)
  have hflip_insert (z : Fin r) (hz : z ∉ S) (i : Fin r) (hiz : i ≠ z) :
      (if i ∈ insert z S then (-1 : ZMod 3) else 1) = (if i ∈ S then -1 else 1) := by
    congr 1
    exact propext (by
      rw [Finset.mem_insert]
      exact ⟨fun h => h.elim (fun h' => absurd h' hiz) id, Or.inr⟩)
  have hlast_any (T : Finset (Fin r)) :
      (frameFlip T (w1 c)) (Fin.last r) = c (Fin.last r) := by
    rw [frameFlip_apply, flipSign_last, one_mul]
    change framePerm σ⁻¹ c (Fin.last r) = c (Fin.last r)
    rw [framePerm_apply_last]
  have hwx_any (T : Finset (Fin r)) : (frameFlip T * w1) (xLast r) = xLast r := by
    rw [LinearEquiv.mul_apply, framePerm_xLast, frameFlip_xLast]
  have hvalS : ∀ i : Fin r, (frameFlip S (w1 c)) i.castSucc =
      if r - k ≤ i.val then 1 else 0 := by
    intro i
    rw [frameFlip_apply, flipSign_castSucc]
    by_cases hlt : r - k ≤ i.val
    · have hne : (w1 c) i.castSucc ≠ 0 := by
        intro h0
        have hlt2 := (hw1zero i).mp h0
        omega
      rw [if_pos hlt]
      by_cases h2 : (w1 c) i.castSucc = 2
      · rw [if_pos ((hmemS i).mpr h2), h2]
        decide
      · have h1 : (w1 c) i.castSucc = 1 := by
          rcases zmod3_ne_zero _ hne with h | h
          · exact h
          · exact absurd h h2
        rw [if_neg (fun hh => h2 ((hmemS i).mp hh)), h1]
        decide
    · have h0 : (w1 c) i.castSucc = 0 :=
        (hw1zero i).mpr (Nat.lt_of_not_le hlt)
      have hnotS : i ∉ S := fun hh => by
        have h2 : (w1 c) i.castSucc = 2 := (hmemS i).mp hh
        rw [h0] at h2
        exact (by decide : (0 : ZMod 3) ≠ 2) h2
      rw [if_neg hlt, if_neg hnotS, h0, mul_zero]
  have hk1 : 1 ≤ k := by
    obtain ⟨i0, hi0⟩ := hcH
    have hmem : σ.symm i0 ∈ Finset.univ.filter (fun i : Fin r => key (σ i) = 1) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp only [key]
      rw [show σ (σ.symm i0) = i0 from Equiv.apply_symm_apply σ i0]
      rw [if_neg hi0]
    have hpos : 0 < k := by
      dsimp only [k]
      exact Finset.card_pos.mpr ⟨_, hmem⟩
    omega
  have hk2 : k ≤ r := by
    dsimp only [k]
    calc (Finset.univ.filter (fun i : Fin r => key (σ i) = 1)).card
        ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = r := by simp
  by_cases hEven : Even S.card
  · exact ⟨frameFlip S * w1, W.mul_mem (frameFlip_mem_even hWd hWs S hEven) hw1W,
      k, hk1, hk2, hwx_any S, hlast_any S, Or.inl hvalS⟩
  · have hOdd : Odd S.card := by
      rcases Nat.even_or_odd S.card with h | h
      · exact absurd h hEven
      · exact h
    by_cases hkr : k = r
    · let z : Fin r := ⟨r - 1, by omega⟩
      have hzval : z.val = r - 1 := rfl
      have hz0 : (w1 c) z.castSucc ≠ 0 := by
        intro h0
        have hlt := (hw1zero z).mp h0
        rw [hzval] at hlt
        omega
      have hvalOne : ∀ i : Fin r, (frameFlip S (w1 c)) i.castSucc = 1 := by
        intro i
        rw [hvalS i]
        have h0 : r - k = 0 := by omega
        rw [h0]
        exact if_pos (Nat.zero_le _)
      let S' : Finset (Fin r) := if z ∈ S then S.erase z else insert z S
      have hS'even : Even S'.card := by
        by_cases hzS : z ∈ S
        · simp only [S', if_pos hzS, Finset.card_erase_of_mem hzS]
          obtain ⟨m, hm⟩ := hOdd
          exact ⟨m, by omega⟩
        · simp only [S', if_neg hzS, Finset.card_insert_of_notMem hzS]
          obtain ⟨m, hm⟩ := hOdd
          exact ⟨m + 1, by omega⟩
      have hvalExtra : ∀ i : Fin r, (frameFlip S' (w1 c)) i.castSucc =
          if i.val = r - 1 then 2 else 1 := by
        intro i
        by_cases hiz : i = z
        · subst hiz
          by_cases hzS : z ∈ S
          · simp only [S', if_pos hzS, frameFlip_apply, flipSign_castSucc]
            have hznot : z ∉ S.erase z := fun h => (Finset.mem_erase.mp h).1 rfl
            simp only [if_neg hznot]
            have h2 : (w1 c) z.castSucc = 2 := (hmemS z).mp hzS
            rw [h2, one_mul, if_pos hzval]
          · simp only [S', if_neg hzS, frameFlip_apply, flipSign_castSucc]
            simp only [if_pos (Finset.mem_insert_self z S)]
            have hne2 : (w1 c) z.castSucc ≠ 2 := fun h => hzS ((hmemS z).mpr h)
            have h1 : (w1 c) z.castSucc = 1 := by
              rcases zmod3_ne_zero _ hz0 with h | h
              · exact h
              · exact absurd h hne2
            rw [h1, if_pos hzval]
            decide
        · rw [frameFlip_apply, flipSign_castSucc]
          have hival : i.val ≠ r - 1 := by
            intro hv
            apply hiz
            exact Fin.ext (by rw [hzval, hv])
          rw [if_neg hival]
          by_cases hzS : z ∈ S
          · simp only [S', if_pos hzS, hflip_erase z hzS i hiz]
            have h := hvalOne i
            rw [frameFlip_apply, flipSign_castSucc] at h
            exact h
          · simp only [S', if_neg hzS, hflip_insert z hzS i hiz]
            have h := hvalOne i
            rw [frameFlip_apply, flipSign_castSucc] at h
            exact h
      refine ⟨frameFlip S' * w1,
        W.mul_mem (frameFlip_mem_even hWd hWs S' hS'even) hw1W,
        k, hk1, hk2, hwx_any S', hlast_any S', Or.inr ⟨hkr, hvalExtra⟩⟩
    · let z : Fin r := ⟨0, by omega⟩
      have hzval : z.val = 0 := rfl
      have hz0 : (w1 c) z.castSucc = 0 := by
        rw [hw1zero z, hzval]
        omega
      have hzS : z ∉ S := by
        intro h
        have h2 : (w1 c) z.castSucc = 2 := (hmemS z).mp h
        rw [hz0] at h2
        exact (by decide : (0 : ZMod 3) ≠ 2) h2
      let S' : Finset (Fin r) := insert z S
      have hS'even : Even S'.card := by
        simp only [S', Finset.card_insert_of_notMem hzS]
        obtain ⟨m, hm⟩ := hOdd
        exact ⟨m + 1, by omega⟩
      have hvalStd : ∀ i : Fin r, (frameFlip S' (w1 c)) i.castSucc =
          if r - k ≤ i.val then 1 else 0 := by
        intro i
        by_cases hiz : i = z
        · subst hiz
          simp only [S', frameFlip_apply, flipSign_castSucc]
          simp only [if_pos (Finset.mem_insert_self z S), hz0, mul_zero]
          have hlt : ¬ (r - k ≤ z.val) := by
            rw [hzval]
            omega
          rw [if_neg hlt]
        · simp only [S', frameFlip_apply, flipSign_castSucc]
          have h := hvalS i
          rw [frameFlip_apply, flipSign_castSucc] at h
          calc (if i ∈ insert z S then (-1 : ZMod 3) else 1) * (w1 c) i.castSucc
              = (if i ∈ S then -1 else 1) * (w1 c) i.castSucc := by
                  congr 1
                  exact hflip_insert z hzS i hiz
            _ = if r - k ≤ i.val then 1 else 0 := h
      refine ⟨frameFlip S' * w1,
        W.mul_mem (frameFlip_mem_even hWd hWs S' hS'even) hw1W,
        k, hk1, hk2, hwx_any S', hlast_any S', Or.inl hvalStd⟩

theorem sym_frame_D_ne {c a : Vn (r + 1)} (hr : 3 ≤ r)
    (hD : ∀ i j, i ≠ j → (a ⬝ᵥ (frameE r i - frameE r j) = 0 ↔
      (frameE r i - frameE r j) ⬝ᵥ c = 0))
    (hS : ∀ i j, i ≠ j → (a ⬝ᵥ (frameE r i + frameE r j) = 0 ↔
      (frameE r i + frameE r j) ⬝ᵥ c = 0))
    (i : Fin r) (hi : c i.castSucc ≠ 0) : a i.castSucc ≠ 0 := by
  classical
  have hD' : ∀ (p q : Fin r) (h : p ≠ q),
      a p.castSucc - a q.castSucc = 0 ↔ c p.castSucc - c q.castSucc = 0 := by
    intro p q h
    rw [← dot_frameE_sub, ← frameE_sub_dot]
    exact hD p q h
  have hS' : ∀ (p q : Fin r) (h : p ≠ q),
      a p.castSucc + a q.castSucc = 0 ↔ c p.castSucc + c q.castSucc = 0 := by
    intro p q h
    rw [← dot_frameE_add, ← frameE_add_dot]
    exact hS p q h
  intro hai
  have hzero : ∀ j : Fin r, j ≠ i → c j.castSucc = 0 := by
    intro j hj
    by_contra hcj
    rcases zmod3_eq_or_eq_neg hi hcj with h | h
    · have haj : a j.castSucc = 0 := by
        have hd : a i.castSucc - a j.castSucc = 0 :=
          (hD' i j (Ne.symm hj)).mpr (by rw [h, sub_self])
        have h1 : a i.castSucc = a j.castSucc := sub_eq_zero.mp hd
        rw [← h1]; exact hai
      have hsum : a i.castSucc + a j.castSucc = 0 := by rw [hai, haj, add_zero]
      have hc : c i.castSucc + c j.castSucc = 0 := (hS' i j (Ne.symm hj)).mp hsum
      rw [h] at hc
      have h2 : (2 : ZMod 3) * c i.castSucc = 0 := by rw [two_mul]; exact hc
      exact zmod3_two_mul_ne_zero _ hi h2
    · have hsum : a i.castSucc + a j.castSucc = 0 :=
        (hS' i j (Ne.symm hj)).mpr (by rw [h]; abel)
      have haj : a j.castSucc = -a i.castSucc := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsum
      have hd : a i.castSucc - a j.castSucc = 0 := by rw [hai, haj, hai]; ring
      have hc : c i.castSucc - c j.castSucc = 0 := (hD' i j (Ne.symm hj)).mp hd
      rw [h] at hc
      have h2 : (2 : ZMod 3) * c i.castSucc = 0 := by
        rw [sub_neg_eq_add, ← two_mul] at hc; exact hc
      exact zmod3_two_mul_ne_zero _ hi h2
  have hne : ∀ j : Fin r, j ≠ i → a j.castSucc ≠ 0 := by
    intro j hj haj
    have hd : a i.castSucc - a j.castSucc = 0 := by rw [hai, haj, sub_zero]
    have hc : c i.castSucc - c j.castSucc = 0 := (hD' i j (Ne.symm hj)).mp hd
    rw [hzero j hj, sub_zero] at hc
    exact hi hc
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) i
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega : 2 < r)
  have hdjk : a j.castSucc - a k.castSucc = 0 :=
    (hD' j k (Ne.symm hkj)).mpr (by rw [hzero j hj, hzero k hki, sub_self])
  have heq : a j.castSucc = a k.castSucc := sub_eq_zero.mp hdjk
  have hsum : a j.castSucc + a k.castSucc = 0 :=
    (hS' j k (Ne.symm hkj)).mpr (by rw [hzero j hj, hzero k hki, add_zero])
  rw [← heq] at hsum
  have h2 : (2 : ZMod 3) * a j.castSucc = 0 := by rw [two_mul]; exact hsum
  exact hne j hj ((zmod3_two_mul_eq_zero _).mp h2)

theorem sym_frame_D {c a : Vn (r + 1)} (hr : 3 ≤ r)
    (hD : ∀ i j, i ≠ j → (a ⬝ᵥ (frameE r i - frameE r j) = 0 ↔
      (frameE r i - frameE r j) ⬝ᵥ c = 0))
    (hS : ∀ i j, i ≠ j → (a ⬝ᵥ (frameE r i + frameE r j) = 0 ↔
      (frameE r i + frameE r j) ⬝ᵥ c = 0)) :
    ∃ l : ZMod 3, ∀ i : Fin r, a i.castSucc = l * c i.castSucc := by
  classical
  have hDswap : ∀ i j, i ≠ j → (c ⬝ᵥ (frameE r i - frameE r j) = 0 ↔
      (frameE r i - frameE r j) ⬝ᵥ a = 0) := by
    intro i j h
    rw [dotProduct_comm c, dotProduct_comm (frameE r i - frameE r j) a]
    exact (hD i j h).symm
  have hSswap : ∀ i j, i ≠ j → (c ⬝ᵥ (frameE r i + frameE r j) = 0 ↔
      (frameE r i + frameE r j) ⬝ᵥ a = 0) := by
    intro i j h
    rw [dotProduct_comm c, dotProduct_comm (frameE r i + frameE r j) a]
    exact (hS i j h).symm
  have hF : ∀ i : Fin r, (a i.castSucc = 0 ↔ c i.castSucc = 0) := by
    intro i
    constructor
    · intro ha0
      by_contra hc0
      exact sym_frame_D_ne hr hD hS i hc0 ha0
    · intro hc0
      by_contra ha0
      exact sym_frame_D_ne hr hDswap hSswap i ha0 hc0
  exact sym_frame_B hD hS hF

theorem TestHyp.exists_canonical_B {W A M : Subgroup (Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1))}
    (hT : TestHyp W (xLast r) A M)
    (hW : ∀ (i j : Fin r) (h : i ≠ j), sgnDiff i j h ∈ W)
    (hWs : ∀ (i j : Fin r) (h : i ≠ j), sgnSum i j h ∈ W)
    (hWf : ∀ i : Fin r, sgnFlip i ∈ W)
    {u : Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1)} (hu : u ∈ A) (huR : IsRefl u)
    (hux : ¬ FixesLine (xLast r) u) :
    ∃ (w : Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1)) (_ : w ∈ W)
      (k : ℕ) (l g d : ZMod 3) (h : canonA r k l d ⬝ᵥ canonC r k g = 2),
      1 ≤ k ∧ k ≤ r ∧ w (xLast r) = xLast r ∧
      w * u * w⁻¹ = refl (canonC r k g) (canonA r k l d) h := by
  classical
  obtain ⟨c, a, hac, rfl⟩ := eq_refl_of_isRefl huR
  have hcH : ∃ i : Fin r, c i.castSucc ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hux
    have hcx : c = (c (Fin.last r)) • xLast r := by
      funext k
      cases k using Fin.lastCases with
      | last => simp [xLast]
      | cast j =>
          have hj : j.castSucc ≠ Fin.last r := by
            intro hh
            have := congrArg Fin.val hh
            simp only [Fin.val_last, Fin.val_castSucc] at this
            omega
          rw [h j, Pi.smul_apply, xLast_apply, if_neg hj, smul_eq_mul, mul_zero]
    have hx0 : xLast r ≠ 0 := by
      intro h0
      have := congrFun h0 (Fin.last r)
      simp [xLast] at this
    have huapply : (refl c a hac) (xLast r)
        = (1 - (a ⬝ᵥ xLast r) * c (Fin.last r)) • xLast r := by
      rw [refl_apply, hcx, smul_smul]
      conv_rhs => rw [sub_smul, one_smul]
      simp only [Pi.smul_apply, xLast_apply, if_true, smul_eq_mul, mul_one]
    have hne : (1 - (a ⬝ᵥ xLast r) * c (Fin.last r)) ≠ 0 := by
      intro h0
      have hzero : (refl c a hac) (xLast r) = 0 := by rw [huapply, h0, zero_smul]
      exact hx0 (((refl c a hac).map_eq_zero_iff).mp hzero)
    rcases zmod3_ne_zero _ hne with h1 | h1
    · left; rw [huapply, h1, one_smul]
    · right; rw [huapply, h1, neg_one_smul]
  have hD : ∀ i j, i ≠ j → (a ⬝ᵥ (frameE r i - frameE r j) = 0 ↔
      (frameE r i - frameE r j) ⬝ᵥ c = 0) := by
    intro i j hij
    have hmem : sgnDiff i j hij ∈ A := hT.le (hT.W_le (hW i j hij))
    have hmem' : refl (Pi.single i.castSucc 1 - Pi.single j.castSucc 1)
        (Pi.single i.castSucc 1 - Pi.single j.castSucc 1)
        (dot_sub_single_self i.castSucc j.castSucc
          (fun hh => hij (Fin.castSucc_injective _ hh))) ∈ A := hmem
    have hs := sym_of_noTransv hT.noTransv hac
      (dot_sub_single_self i.castSucc j.castSucc
        (fun hh => hij (Fin.castSucc_injective _ hh))) hu hmem'
    simpa [frameE] using hs
  have hS : ∀ i j, i ≠ j → (a ⬝ᵥ (frameE r i + frameE r j) = 0 ↔
      (frameE r i + frameE r j) ⬝ᵥ c = 0) := by
    intro i j hij
    have hmem : sgnSum i j hij ∈ A := hT.le (hT.W_le (hWs i j hij))
    exact sym_of_noTransv hT.noTransv hac (frameE_add_self i j hij) hu hmem
  have hF : ∀ i : Fin r, (a i.castSucc = 0 ↔ c i.castSucc = 0) := by
    intro i
    have hmem : sgnFlip i ∈ A := hT.le (hT.W_le (hWf i))
    have hs := sym_of_noTransv hT.noTransv hac (sgnFlip_dot i) hu hmem
    rw [dot_frameE, smul_dotProduct, frameE_dot, smul_eq_mul] at hs
    constructor
    · intro h0
      by_contra hc0
      exact zmod3_two_mul_ne_zero _ hc0 (hs.mp h0)
    · intro hc0
      exact hs.mpr (by rw [hc0, mul_zero])
  obtain ⟨l, hl⟩ := sym_frame_B hD hS hF
  obtain ⟨w, hwW, k, hk1, hk2, hwx, hwlast, hwc⟩ := exists_frame_canonical_B hW hWf hcH
  set c' : Vn (r + 1) := w c with hc'def
  set a' : Vn (r + 1) := dualVec (w.symm : Vn (r + 1) →ₗ[ZMod 3] Vn (r + 1)) a with ha'def
  have hac' : a' ⬝ᵥ c' = 2 := by
    rw [ha'def, hc'def, dualVec_dotProduct]
    simpa using hac
  have hconj : w * refl c a hac * w⁻¹ = refl c' a' hac' := conj_refl w c a hac
  have hmemA : refl c' a' hac' ∈ A := by
    rw [← hconj]
    exact A.mul_mem (A.mul_mem (hT.le (hT.W_le hwW)) hu)
      (A.inv_mem (hT.le (hT.W_le hwW)))
  have hc' : c' = canonC r k (c (Fin.last r)) := by
    funext i
    cases i using Fin.lastCases with
    | last => rw [canonC_last]; exact hwlast
    | cast j => rw [canonC_castSucc]; exact hwc j
  have hD' : ∀ i j, i ≠ j → (a' ⬝ᵥ (frameE r i - frameE r j) = 0 ↔
      (frameE r i - frameE r j) ⬝ᵥ c' = 0) := by
    intro i j hij
    have hmem : sgnDiff i j hij ∈ A := hT.le (hT.W_le (hW i j hij))
    have hmem' : refl (Pi.single i.castSucc 1 - Pi.single j.castSucc 1)
        (Pi.single i.castSucc 1 - Pi.single j.castSucc 1)
        (dot_sub_single_self i.castSucc j.castSucc
          (fun hh => hij (Fin.castSucc_injective _ hh))) ∈ A := hmem
    have hs := sym_of_noTransv hT.noTransv hac'
      (dot_sub_single_self i.castSucc j.castSucc
        (fun hh => hij (Fin.castSucc_injective _ hh))) hmemA hmem'
    simpa [frameE] using hs
  have hS' : ∀ i j, i ≠ j → (a' ⬝ᵥ (frameE r i + frameE r j) = 0 ↔
      (frameE r i + frameE r j) ⬝ᵥ c' = 0) := by
    intro i j hij
    have hmem : sgnSum i j hij ∈ A := hT.le (hT.W_le (hWs i j hij))
    have hs := sym_of_noTransv hT.noTransv hac' (frameE_add_self i j hij) hmemA hmem
    exact hs
  have hF' : ∀ i : Fin r, (a' i.castSucc = 0 ↔ c' i.castSucc = 0) := by
    intro i
    have hmem : sgnFlip i ∈ A := hT.le (hT.W_le (hWf i))
    have hs := sym_of_noTransv hT.noTransv hac' (sgnFlip_dot i) hmemA hmem
    rw [dot_frameE, smul_dotProduct, frameE_dot, smul_eq_mul] at hs
    constructor
    · intro h0
      by_contra hc0
      exact zmod3_two_mul_ne_zero _ hc0 (hs.mp h0)
    · intro hc0
      exact hs.mpr (by rw [hc0, mul_zero])
  obtain ⟨l', hl'⟩ := sym_frame_B hD' hS' hF'
  set d' : ZMod 3 := a' (Fin.last r) with hd'def
  have ha' : a' = canonA r k l' d' := by
    funext i
    cases i using Fin.lastCases with
    | last => rw [canonA_last]
    | cast j =>
        rw [canonA_castSucc, hl' j, hc', canonC_castSucc]
        by_cases hlt : r - k ≤ j.val
        · rw [if_pos hlt, if_pos hlt, mul_one]
        · rw [if_neg hlt, if_neg hlt, mul_zero]
  have hfinalProof : canonA r k l' d' ⬝ᵥ canonC r k (c (Fin.last r)) = 2 := by
    rw [← ha', ← hc']
    exact hac'
  refine ⟨w, hwW, k, l', c (Fin.last r), d', hfinalProof, hk1, hk2, hwx, ?_⟩
  calc w * refl c a hac * w⁻¹ = refl c' a' hac' := hconj
    _ = refl (canonC r k (c (Fin.last r))) (canonA r k l' d') hfinalProof := by
        apply LinearEquiv.ext
        intro v
        rw [refl_apply, refl_apply, hc', ha']

theorem TestHyp.exists_canonical_D {W A M : Subgroup (Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1))}
    (hr : 3 ≤ r) (hT : TestHyp W (xLast r) A M)
    (hWd : ∀ (i j : Fin r) (h : i ≠ j), sgnDiff i j h ∈ W)
    (hWs : ∀ (i j : Fin r) (h : i ≠ j), sgnSum i j h ∈ W)
    {u : Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1)} (hu : u ∈ A) (huR : IsRefl u)
    (hux : ¬ FixesLine (xLast r) u) :
    ∃ (w : Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1)) (_ : w ∈ W) (k : ℕ),
      1 ≤ k ∧ k ≤ r ∧ w (xLast r) = xLast r ∧
      ((∃ (l g d : ZMod 3) (h : canonA r k l d ⬝ᵥ canonC r k g = 2),
          w * u * w⁻¹ = refl (canonC r k g) (canonA r k l d) h) ∨
       (k = r ∧ ∃ (l g d : ZMod 3) (h : canonAD r l d ⬝ᵥ canonD r g = 2),
          w * u * w⁻¹ = refl (canonD r g) (canonAD r l d) h)) := by
  classical
  obtain ⟨c, a, hac, rfl⟩ := eq_refl_of_isRefl huR
  have hcH : ∃ i : Fin r, c i.castSucc ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hux
    have hcx : c = (c (Fin.last r)) • xLast r := by
      funext k
      cases k using Fin.lastCases with
      | last => simp [xLast]
      | cast j =>
          have hj : j.castSucc ≠ Fin.last r := by
            intro hh
            have := congrArg Fin.val hh
            simp only [Fin.val_last, Fin.val_castSucc] at this
            omega
          rw [h j, Pi.smul_apply, xLast_apply, if_neg hj, smul_eq_mul, mul_zero]
    have hx0 : xLast r ≠ 0 := by
      intro h0
      have := congrFun h0 (Fin.last r)
      simp [xLast] at this
    have huapply : (refl c a hac) (xLast r)
        = (1 - (a ⬝ᵥ xLast r) * c (Fin.last r)) • xLast r := by
      rw [refl_apply, hcx, smul_smul]
      conv_rhs => rw [sub_smul, one_smul]
      simp only [Pi.smul_apply, xLast_apply, if_true, smul_eq_mul, mul_one]
    have hne : (1 - (a ⬝ᵥ xLast r) * c (Fin.last r)) ≠ 0 := by
      intro h0
      have hzero : (refl c a hac) (xLast r) = 0 := by rw [huapply, h0, zero_smul]
      exact hx0 (((refl c a hac).map_eq_zero_iff).mp hzero)
    rcases zmod3_ne_zero _ hne with h1 | h1
    · left; rw [huapply, h1, one_smul]
    · right; rw [huapply, h1, neg_one_smul]
  have hD : ∀ i j, i ≠ j → (a ⬝ᵥ (frameE r i - frameE r j) = 0 ↔
      (frameE r i - frameE r j) ⬝ᵥ c = 0) := by
    intro i j hij
    have hmem : sgnDiff i j hij ∈ A := hT.le (hT.W_le (hWd i j hij))
    have hmem' : refl (Pi.single i.castSucc 1 - Pi.single j.castSucc 1)
        (Pi.single i.castSucc 1 - Pi.single j.castSucc 1)
        (dot_sub_single_self i.castSucc j.castSucc
          (fun hh => hij (Fin.castSucc_injective _ hh))) ∈ A := hmem
    have hs := sym_of_noTransv hT.noTransv hac
      (dot_sub_single_self i.castSucc j.castSucc
        (fun hh => hij (Fin.castSucc_injective _ hh))) hu hmem'
    simpa [frameE] using hs
  have hS : ∀ i j, i ≠ j → (a ⬝ᵥ (frameE r i + frameE r j) = 0 ↔
      (frameE r i + frameE r j) ⬝ᵥ c = 0) := by
    intro i j hij
    have hmem : sgnSum i j hij ∈ A := hT.le (hT.W_le (hWs i j hij))
    exact sym_of_noTransv hT.noTransv hac (frameE_add_self i j hij) hu hmem
  obtain ⟨w, hwW, k, hk1, hk2, hwx, hwlast, hshape⟩ :=
    exists_frame_canonical_D hr hWd hWs hcH
  set c' : Vn (r + 1) := w c with hc'def
  set a' : Vn (r + 1) := dualVec (w.symm : Vn (r + 1) →ₗ[ZMod 3] Vn (r + 1)) a with ha'def
  have hac' : a' ⬝ᵥ c' = 2 := by
    rw [ha'def, hc'def, dualVec_dotProduct]
    simpa using hac
  have hconj : w * refl c a hac * w⁻¹ = refl c' a' hac' := conj_refl w c a hac
  have hmemA : refl c' a' hac' ∈ A := by
    rw [← hconj]
    exact A.mul_mem (A.mul_mem (hT.le (hT.W_le hwW)) hu)
      (A.inv_mem (hT.le (hT.W_le hwW)))
  have hD' : ∀ i j, i ≠ j → (a' ⬝ᵥ (frameE r i - frameE r j) = 0 ↔
      (frameE r i - frameE r j) ⬝ᵥ c' = 0) := by
    intro i j hij
    have hmem : sgnDiff i j hij ∈ A := hT.le (hT.W_le (hWd i j hij))
    have hmem' : refl (Pi.single i.castSucc 1 - Pi.single j.castSucc 1)
        (Pi.single i.castSucc 1 - Pi.single j.castSucc 1)
        (dot_sub_single_self i.castSucc j.castSucc
          (fun hh => hij (Fin.castSucc_injective _ hh))) ∈ A := hmem
    have hs := sym_of_noTransv hT.noTransv hac'
      (dot_sub_single_self i.castSucc j.castSucc
        (fun hh => hij (Fin.castSucc_injective _ hh))) hmemA hmem'
    simpa [frameE] using hs
  have hS' : ∀ i j, i ≠ j → (a' ⬝ᵥ (frameE r i + frameE r j) = 0 ↔
      (frameE r i + frameE r j) ⬝ᵥ c' = 0) := by
    intro i j hij
    have hmem : sgnSum i j hij ∈ A := hT.le (hT.W_le (hWs i j hij))
    exact sym_of_noTransv hT.noTransv hac' (frameE_add_self i j hij) hmemA hmem
  obtain ⟨l', hl'⟩ := sym_frame_D hr hD' hS'
  set d' : ZMod 3 := a' (Fin.last r) with hd'def
  rcases hshape with hstd | ⟨hkr, hextra⟩
  · have hc' : c' = canonC r k (c (Fin.last r)) := by
      funext i
      cases i using Fin.lastCases with
      | last => rw [canonC_last]; exact hwlast
      | cast j => rw [canonC_castSucc]; exact hstd j
    have ha' : a' = canonA r k l' d' := by
      funext i
      cases i using Fin.lastCases with
      | last => rw [canonA_last]
      | cast j =>
          rw [canonA_castSucc, hl' j, hc', canonC_castSucc]
          by_cases hlt : r - k ≤ j.val
          · rw [if_pos hlt, if_pos hlt, mul_one]
          · rw [if_neg hlt, if_neg hlt, mul_zero]
    have hfinalProof : canonA r k l' d' ⬝ᵥ canonC r k (c (Fin.last r)) = 2 := by
      rw [← ha', ← hc']
      exact hac'
    refine ⟨w, hwW, k, hk1, hk2, hwx, Or.inl ⟨l', c (Fin.last r), d', hfinalProof, ?_⟩⟩
    calc w * refl c a hac * w⁻¹ = refl c' a' hac' := hconj
      _ = refl (canonC r k (c (Fin.last r))) (canonA r k l' d') hfinalProof := by
          apply LinearEquiv.ext
          intro v
          rw [refl_apply, refl_apply, hc', ha']
  · have hc' : c' = canonD r (c (Fin.last r)) := by
      funext i
      cases i using Fin.lastCases with
      | last => rw [canonD_last]; exact hwlast
      | cast j => rw [canonD_castSucc]; exact hextra j
    have ha' : a' = canonAD r l' d' := by
      funext i
      cases i using Fin.lastCases with
      | last => rw [canonAD_last]
      | cast j =>
          rw [canonAD_castSucc, hl' j, hc', canonD_castSucc]
          by_cases hlt : j.val = r - 1
          · rw [if_pos hlt, if_pos hlt]; ring
          · rw [if_neg hlt, if_neg hlt]; ring
    have hfinalProof : canonAD r l' d' ⬝ᵥ canonD r (c (Fin.last r)) = 2 := by
      rw [← ha', ← hc']
      exact hac'
    refine ⟨w, hwW, k, hk1, hk2, hwx, Or.inr ⟨hkr, ⟨l', c (Fin.last r), d', hfinalProof, ?_⟩⟩⟩
    calc w * refl c a hac * w⁻¹ = refl c' a' hac' := hconj
      _ = refl (canonD r (c (Fin.last r))) (canonAD r l' d') hfinalProof := by
          apply LinearEquiv.ext
          intro v
          rw [refl_apply, refl_apply, hc', ha']

