module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08SgnLin

public section

namespace CFSG.StandardType.TestLin

open Matrix

variable {r : ℕ}



@[expose] def xLast2 (r : ℕ) : Vn (r + 2) := Pi.single (Fin.last (r + 1)) 1

theorem xLast2_apply (k : Fin (r + 2)) : xLast2 r k = if k = Fin.last (r + 1) then 1 else 0 := by
  simp [xLast2, Pi.single_apply]



private theorem frameIndex_ne_last (i : Fin r) :
    i.castSucc.castSucc ≠ Fin.last (r + 1) := by
  intro hh
  have hv := congrArg Fin.val hh
  simp only [Fin.val_last, Fin.val_castSucc] at hv
  omega

private theorem extraIndex_ne_last (r : ℕ) :
    ((Fin.last r).castSucc : Fin (r + 2)) ≠ Fin.last (r + 1) := by
  intro hh
  have hv := congrArg Fin.val hh
  simp only [Fin.val_last, Fin.val_castSucc] at hv
  omega

private theorem extraIndex_ne_frame (i : Fin r) :
    ((Fin.last r).castSucc : Fin (r + 2)) ≠ i.castSucc.castSucc := by
  intro hh
  have hv := congrArg Fin.val hh
  simp only [Fin.val_last, Fin.val_castSucc] at hv
  omega

private theorem xLast2_frame (i : Fin r) : xLast2 r i.castSucc.castSucc = 0 := by
  rw [xLast2_apply, if_neg (frameIndex_ne_last i)]

private theorem xLast2_extra (r : ℕ) : xLast2 r ((Fin.last r).castSucc) = 0 := by
  rw [xLast2_apply, if_neg (extraIndex_ne_last r)]

@[expose] def frameE2 (r : ℕ) (i : Fin r) : Vn (r + 2) := Pi.single i.castSucc.castSucc 1
theorem frameE2_apply (i : Fin r) (k : Fin (r + 2)) :
    frameE2 r i k = if k = i.castSucc.castSucc then 1 else 0 := by
  simp [frameE2, Pi.single_apply]

theorem dot_xLast2 (a : Vn (r + 2)) : a ⬝ᵥ xLast2 r = a (Fin.last (r + 1)) := by
  rw [xLast2, dotProduct_single, mul_one]

theorem dot_frameE2 (a : Vn (r + 2)) (i : Fin r) : a ⬝ᵥ frameE2 r i = a i.castSucc.castSucc := by
  rw [frameE2, dotProduct_single, mul_one]

theorem frameE2_dot (c : Vn (r + 2)) (i : Fin r) : frameE2 r i ⬝ᵥ c = c i.castSucc.castSucc := by
  rw [frameE2, single_dotProduct, one_mul]

theorem dot_frameE2_sub (a : Vn (r + 2)) (i j : Fin r) :
    a ⬝ᵥ (frameE2 r i - frameE2 r j) = a i.castSucc.castSucc - a j.castSucc.castSucc := by
  rw [dotProduct_sub, dot_frameE2, dot_frameE2]

theorem frameE2_sub_dot (c : Vn (r + 2)) (i j : Fin r) :
    (frameE2 r i - frameE2 r j) ⬝ᵥ c = c i.castSucc.castSucc - c j.castSucc.castSucc := by
  rw [sub_dotProduct, frameE2_dot, frameE2_dot]

theorem dot_frameE2_add (a : Vn (r + 2)) (i j : Fin r) :
    a ⬝ᵥ (frameE2 r i + frameE2 r j) = a i.castSucc.castSucc + a j.castSucc.castSucc := by
  rw [dotProduct_add, dot_frameE2, dot_frameE2]

theorem frameE2_add_dot (c : Vn (r + 2)) (i j : Fin r) :
    (frameE2 r i + frameE2 r j) ⬝ᵥ c = c i.castSucc.castSucc + c j.castSucc.castSucc := by
  rw [add_dotProduct, frameE2_dot, frameE2_dot]

theorem frameE2_sub_self (i j : Fin r) (h : i ≠ j) :
    (frameE2 r i - frameE2 r j) ⬝ᵥ (frameE2 r i - frameE2 r j) = 2 := by
  rw [frameE2_sub_dot]
  have hij : i.castSucc.castSucc ≠ j.castSucc.castSucc := fun hh => h (Fin.castSucc_injective _ (Fin.castSucc_injective _ hh))
  simp [frameE2, Pi.single_eq_same, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne (Ne.symm hij)]
  decide

theorem frameE2_add_self (i j : Fin r) (h : i ≠ j) :
    (frameE2 r i + frameE2 r j) ⬝ᵥ (frameE2 r i + frameE2 r j) = 2 := by
  rw [frameE2_add_dot]
  have hij : i.castSucc.castSucc ≠ j.castSucc.castSucc := fun hh => h (Fin.castSucc_injective _ (Fin.castSucc_injective _ hh))
  simp [frameE2, Pi.single_eq_same, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne (Ne.symm hij)]
  decide

@[expose] def sgnDiff2 (i j : Fin r) (h : i ≠ j) : Vn (r + 2) ≃ₗ[ZMod 3] Vn (r + 2) :=
  refl (frameE2 r i - frameE2 r j) (frameE2 r i - frameE2 r j) (frameE2_sub_self i j h)

@[expose] def sgnSum2 (i j : Fin r) (h : i ≠ j) : Vn (r + 2) ≃ₗ[ZMod 3] Vn (r + 2) :=
  refl (frameE2 r i + frameE2 r j) (frameE2 r i + frameE2 r j) (frameE2_add_self i j h)

theorem sgnFlip2_dot (i : Fin r) : ((2 : ZMod 3) • frameE2 r i) ⬝ᵥ frameE2 r i = 2 := by
  rw [smul_dotProduct, frameE2_dot]
  simp [frameE2]

@[expose] def sgnFlip2 (i : Fin r) : Vn (r + 2) ≃ₗ[ZMod 3] Vn (r + 2) :=
  refl (frameE2 r i) ((2 : ZMod 3) • frameE2 r i) (sgnFlip2_dot i)

theorem sgnFlip2_apply (i : Fin r) (v : Vn (r + 2)) :
    sgnFlip2 i v = v - ((2 : ZMod 3) * v i.castSucc.castSucc) • frameE2 r i := by
  rw [sgnFlip2, refl_apply, smul_dotProduct, frameE2_dot, smul_eq_mul]

theorem sgnFlip2_coord (i : Fin r) (v : Vn (r + 2)) (k : Fin (r + 2)) :
    sgnFlip2 i v k = if k = i.castSucc.castSucc then -v i.castSucc.castSucc else v k := by
  rw [sgnFlip2_apply]
  by_cases hk : k = i.castSucc.castSucc
  · subst hk
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, frameE2, Pi.single_eq_same,
      if_true]
    ring
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, frameE2,
      Pi.single_eq_of_ne hk, if_neg hk, mul_zero, sub_zero]

theorem sym_frame_B2 {c a : Vn (r + 2)}
    (hD : ∀ i j, i ≠ j → (a ⬝ᵥ (frameE2 r i - frameE2 r j) = 0 ↔
      (frameE2 r i - frameE2 r j) ⬝ᵥ c = 0))
    (hS : ∀ i j, i ≠ j → (a ⬝ᵥ (frameE2 r i + frameE2 r j) = 0 ↔
      (frameE2 r i + frameE2 r j) ⬝ᵥ c = 0))
    (hF : ∀ i : Fin r, (a i.castSucc.castSucc = 0 ↔ c i.castSucc.castSucc = 0)) :
    ∃ l : ZMod 3, ∀ i : Fin r, a i.castSucc.castSucc = l * c i.castSucc.castSucc := by
  classical
  have hD' : ∀ (i j : Fin r) (h : i ≠ j),
      a i.castSucc.castSucc - a j.castSucc.castSucc = 0 ↔ c i.castSucc.castSucc - c j.castSucc.castSucc = 0 := by
    intro i j h
    rw [← dot_frameE2_sub, ← frameE2_sub_dot]
    exact hD i j h
  have hS' : ∀ (i j : Fin r) (h : i ≠ j),
      a i.castSucc.castSucc + a j.castSucc.castSucc = 0 ↔ c i.castSucc.castSucc + c j.castSucc.castSucc = 0 := by
    intro i j h
    rw [← dot_frameE2_add, ← frameE2_add_dot]
    exact hS i j h
  by_cases hc : ∃ i : Fin r, c i.castSucc.castSucc ≠ 0
  · obtain ⟨i0, hi0⟩ := hc
    refine ⟨a i0.castSucc.castSucc * c i0.castSucc.castSucc, fun j => ?_⟩
    have hsq : c i0.castSucc.castSucc * c i0.castSucc.castSucc = 1 := zmod3_sq_eq_one _ hi0
    by_cases hj : j = i0
    · subst hj
      rw [mul_assoc, hsq, mul_one]
    · by_cases hcj : c j.castSucc.castSucc = 0
      · have haj : a j.castSucc.castSucc = 0 := (hF j).mpr hcj
        rw [haj, hcj, mul_zero]
      · set t : ZMod 3 := c j.castSucc.castSucc * c i0.castSucc.castSucc with ht
        have htc : t * c i0.castSucc.castSucc = c j.castSucc.castSucc := by
          rw [ht, mul_assoc, hsq, mul_one]
        have htne : t ≠ 0 := by
          intro h0
          rw [h0, zero_mul] at htc
          exact hcj htc.symm
        rcases zmod3_ne_zero t htne with ht1 | ht1
        · have hcjeq : c j.castSucc.castSucc = c i0.castSucc.castSucc := by rw [← htc, ht1, one_mul]
          have hai : a i0.castSucc.castSucc - a j.castSucc.castSucc = 0 :=
            (hD' i0 j (Ne.symm hj)).mpr (by rw [hcjeq, sub_self])
          have haj : a j.castSucc.castSucc = a i0.castSucc.castSucc := (sub_eq_zero.mp hai).symm
          rw [haj, hcjeq, mul_assoc, hsq, mul_one]
        · have hcjeq : c j.castSucc.castSucc = -c i0.castSucc.castSucc := by
            rw [← htc, ht1, neg_one_mul]
          have hai : a i0.castSucc.castSucc + a j.castSucc.castSucc = 0 :=
            (hS' i0 j (Ne.symm hj)).mpr (by rw [hcjeq]; abel)
          have haj : a j.castSucc.castSucc = -a i0.castSucc.castSucc := by
            rw [eq_neg_iff_add_eq_zero, add_comm]
            exact hai
          rw [haj, hcjeq]
          have : (a i0.castSucc.castSucc * c i0.castSucc.castSucc) * -c i0.castSucc.castSucc = -a i0.castSucc.castSucc := by
            rw [mul_neg, mul_assoc, hsq, mul_one]
          rw [this]
  · simp only [not_exists, not_not] at hc
    refine ⟨0, fun i => ?_⟩
    have hci : c i.castSucc.castSucc = 0 := hc i
    have hai : a i.castSucc.castSucc = 0 := (hF i).mpr hci
    rw [hai, hci, mul_zero]

def extFrameFun2 (τ : Equiv.Perm (Fin r)) (i : Fin (r + 2)) : Fin (r + 2) :=
  if h : i.val < r then (τ ⟨i.val, h⟩).castSucc.castSucc else i

theorem extFrameFun2_of_lt (τ : Equiv.Perm (Fin r)) {i : Fin (r + 2)}
    (h : i.val < r) : extFrameFun2 τ i = (τ ⟨i.val, h⟩).castSucc.castSucc := by
  simp [extFrameFun2, h]

theorem extFrameFun2_of_not_lt (τ : Equiv.Perm (Fin r)) {i : Fin (r + 2)}
    (h : ¬ i.val < r) : extFrameFun2 τ i = i := by
  simp [extFrameFun2, h]

theorem extFrameFun2_castSucc (τ : Equiv.Perm (Fin r)) (i : Fin r) :
    extFrameFun2 τ i.castSucc.castSucc = (τ i).castSucc.castSucc := by
  rw [extFrameFun2_of_lt τ i.isLt]
  have h : (⟨(i.castSucc.castSucc : Fin (r + 2)).val, i.isLt⟩ : Fin r) = i := Fin.ext rfl
  rw [h]

theorem extFrameFun2_extra (τ : Equiv.Perm (Fin r)) :
    extFrameFun2 τ ((Fin.last r).castSucc) = (Fin.last r).castSucc := by
  rw [extFrameFun2_of_not_lt τ (by simp [Fin.val_last])]

theorem extFrameFun2_last (τ : Equiv.Perm (Fin r)) :
    extFrameFun2 τ (Fin.last (r + 1)) = Fin.last (r + 1) := by
  rw [extFrameFun2_of_not_lt τ (by simp [Fin.val_last])]

@[expose] def extFramePerm2 (σ : Equiv.Perm (Fin r)) : Equiv.Perm (Fin (r + 2)) where
  toFun := extFrameFun2 σ
  invFun := extFrameFun2 σ⁻¹
  left_inv i := by
    by_cases h : i.val < r
    · rw [extFrameFun2_of_lt σ h, extFrameFun2_castSucc]
      have hx : σ⁻¹ (σ ⟨i.val, h⟩) = ⟨i.val, h⟩ := Equiv.symm_apply_apply σ _
      rw [hx]
      exact Fin.ext rfl
    · rw [extFrameFun2_of_not_lt σ h, extFrameFun2_of_not_lt σ⁻¹ h]
  right_inv i := by
    by_cases h : i.val < r
    · rw [extFrameFun2_of_lt σ⁻¹ h, extFrameFun2_castSucc]
      have hx : σ (σ⁻¹ ⟨i.val, h⟩) = ⟨i.val, h⟩ := Equiv.apply_symm_apply σ _
      rw [hx]
      exact Fin.ext rfl
    · rw [extFrameFun2_of_not_lt σ⁻¹ h, extFrameFun2_of_not_lt σ h]

theorem extFramePerm2_apply (σ : Equiv.Perm (Fin r)) (i : Fin (r + 2)) :
    extFramePerm2 σ i = extFrameFun2 σ i := rfl

theorem extFramePerm2_apply_castSucc (σ : Equiv.Perm (Fin r)) (i : Fin r) :
    extFramePerm2 σ i.castSucc.castSucc = (σ i).castSucc.castSucc := by
  change extFrameFun2 σ i.castSucc.castSucc = (σ i).castSucc.castSucc
  rw [extFrameFun2_castSucc]

theorem extFramePerm2_apply_extra (σ : Equiv.Perm (Fin r)) :
    extFramePerm2 σ ((Fin.last r).castSucc) = (Fin.last r).castSucc := by
  change extFrameFun2 σ ((Fin.last r).castSucc) = (Fin.last r).castSucc
  rw [extFrameFun2_extra]

theorem extFramePerm2_apply_last (σ : Equiv.Perm (Fin r)) :
    extFramePerm2 σ (Fin.last (r + 1)) = Fin.last (r + 1) := by
  change extFrameFun2 σ (Fin.last (r + 1)) = Fin.last (r + 1)
  rw [extFrameFun2_last]

theorem extFramePerm2_symm_castSucc (σ : Equiv.Perm (Fin r)) (i : Fin r) :
    (extFramePerm2 σ).symm i.castSucc.castSucc = (σ⁻¹ i).castSucc.castSucc := by
  change extFrameFun2 σ⁻¹ i.castSucc.castSucc = (σ⁻¹ i).castSucc.castSucc
  rw [extFrameFun2_castSucc]

theorem extFramePerm2_symm_extra (σ : Equiv.Perm (Fin r)) :
    (extFramePerm2 σ).symm ((Fin.last r).castSucc) = (Fin.last r).castSucc := by
  change extFrameFun2 σ⁻¹ ((Fin.last r).castSucc) = (Fin.last r).castSucc
  rw [extFrameFun2_extra]

theorem extFramePerm2_symm_last (σ : Equiv.Perm (Fin r)) :
    (extFramePerm2 σ).symm (Fin.last (r + 1)) = Fin.last (r + 1) := by
  change extFrameFun2 σ⁻¹ (Fin.last (r + 1)) = Fin.last (r + 1)
  rw [extFrameFun2_last]

theorem extFramePerm2_one : extFramePerm2 (1 : Equiv.Perm (Fin r)) = 1 := by
  apply Equiv.ext
  intro i
  rw [extFramePerm2_apply]
  change extFrameFun2 1 i = i
  by_cases h : i.val < r
  · rw [extFrameFun2_of_lt 1 h]
    exact Fin.ext rfl
  · rw [extFrameFun2_of_not_lt 1 h]

theorem extFramePerm2_mul (σ τ : Equiv.Perm (Fin r)) :
    extFramePerm2 (σ * τ) = extFramePerm2 σ * extFramePerm2 τ := by
  apply Equiv.ext
  intro i
  rw [Equiv.Perm.mul_apply]
  rw [extFramePerm2_apply, extFramePerm2_apply, extFramePerm2_apply]
  by_cases h : i.val < r
  · rw [extFrameFun2_of_lt (σ * τ) h, extFrameFun2_of_lt τ h]
    have h' : ((τ ⟨i.val, h⟩).castSucc.castSucc : Fin (r + 2)).val < r := by simp
    rw [extFrameFun2_of_lt σ h']
    have hx : (⟨((τ ⟨i.val, h⟩).castSucc.castSucc : Fin (r + 2)).val, h'⟩ : Fin r) =
        τ ⟨i.val, h⟩ := Fin.ext rfl
    rw [hx]
    rfl
  · rw [extFrameFun2_of_not_lt (σ * τ) h, extFrameFun2_of_not_lt τ h,
        extFrameFun2_of_not_lt σ h]

theorem extFramePerm2_swap (i j : Fin r) (_h : i ≠ j) :
    extFramePerm2 (Equiv.swap i j) =
      Equiv.swap i.castSucc.castSucc j.castSucc.castSucc := by
  apply Equiv.ext
  intro k
  rw [extFramePerm2_apply]
  change extFrameFun2 (Equiv.swap i j) k =
    Equiv.swap i.castSucc.castSucc j.castSucc.castSucc k
  by_cases hk : k.val < r
  · set k' : Fin r := ⟨k.val, hk⟩ with hk'def
    have hk_eq : k = k'.castSucc.castSucc := Fin.ext rfl
    rw [hk_eq, extFrameFun2_castSucc]
    by_cases hki : k' = i
    · subst hki
      rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
    · by_cases hkj : k' = j
      · subst hkj
        rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj,
            Equiv.swap_apply_of_ne_of_ne
              (fun hh => hki (Fin.castSucc_injective _ (Fin.castSucc_injective _ hh)))
              (fun hh => hkj (Fin.castSucc_injective _ (Fin.castSucc_injective _ hh)))]
  · rw [extFrameFun2_of_not_lt (Equiv.swap i j) hk]
    have hki : k ≠ i.castSucc.castSucc := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [Fin.val_castSucc] at hv
      omega
    have hkj : k ≠ j.castSucc.castSucc := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [Fin.val_castSucc] at hv
      omega
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj]


@[expose] def framePerm2 (σ : Equiv.Perm (Fin r)) : Vn (r + 2) ≃ₗ[ZMod 3] Vn (r + 2) :=
  permN (extFramePerm2 σ)

theorem framePerm2_one : framePerm2 (1 : Equiv.Perm (Fin r)) = 1 := by
  rw [framePerm2, extFramePerm2_one]
  apply LinearEquiv.ext
  intro v
  funext i
  rfl

theorem framePerm2_mul (σ τ : Equiv.Perm (Fin r)) :
    framePerm2 (σ * τ) = framePerm2 σ * framePerm2 τ := by
  rw [framePerm2, extFramePerm2_mul, permN_mul]
  rfl

theorem framePerm2_swap (i j : Fin r) (h0 : i ≠ j) :
    framePerm2 (Equiv.swap i j) = sgnDiff2 i j h0 := by
  have hij : i.castSucc.castSucc ≠ j.castSucc.castSucc :=
    fun hh => h0 (Fin.castSucc_injective _ (Fin.castSucc_injective _ hh))
  rw [framePerm2, extFramePerm2_swap i j h0]
  exact permN_swap i.castSucc.castSucc j.castSucc.castSucc hij

theorem framePerm2_apply_castSucc (σ : Equiv.Perm (Fin r)) (v : Vn (r + 2)) (i : Fin r) :
    framePerm2 σ v i.castSucc.castSucc = v (σ⁻¹ i).castSucc.castSucc := by
  rw [framePerm2, permN_apply, extFramePerm2_symm_castSucc]

theorem framePerm2_apply_extra (σ : Equiv.Perm (Fin r)) (v : Vn (r + 2)) :
    framePerm2 σ v ((Fin.last r).castSucc) = v ((Fin.last r).castSucc) := by
  rw [framePerm2, permN_apply, extFramePerm2_symm_extra]

theorem framePerm2_apply_last (σ : Equiv.Perm (Fin r)) (v : Vn (r + 2)) :
    framePerm2 σ v (Fin.last (r + 1)) = v (Fin.last (r + 1)) := by
  rw [framePerm2, permN_apply, extFramePerm2_symm_last]

theorem framePerm2_xLast2 (σ : Equiv.Perm (Fin r)) : framePerm2 σ (xLast2 r) = xLast2 r := by
  funext k
  cases k using Fin.lastCases with
  | last => rw [framePerm2_apply_last]
  | cast j =>
      cases j using Fin.lastCases with
      | last =>
          rw [framePerm2_apply_extra]
      | cast i =>
          rw [framePerm2_apply_castSucc, xLast2_frame (σ⁻¹ i), xLast2_frame i]

theorem framePerm2_mem_adj {W : Subgroup (Vn (r + 2) ≃ₗ[ZMod 3] Vn (r + 2))}
    (hW : ∀ (i : Fin r) (h : i.val + 1 < r),
      sgnDiff2 i ⟨i.val + 1, h⟩ (by
        intro hh; have := congrArg Fin.val hh; simp only at this; omega) ∈ W)
    (σ : Equiv.Perm (Fin r)) : framePerm2 σ ∈ W := by
  cases r with
  | zero =>
      have h1 : σ = 1 := Subsingleton.elim σ 1
      rw [h1, framePerm2_one]
      exact W.one_mem
  | succ m =>
      have hσ : σ ∈ Submonoid.closure
          (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
        rw [Equiv.Perm.mclosure_swap_castSucc_succ]
        exact Submonoid.mem_top σ
      induction hσ using Submonoid.closure_induction with
      | mem τ hτ =>
          obtain ⟨i, rfl⟩ := hτ
          rw [framePerm2_swap]
          exact hW i.castSucc (by simp)
      | one => rw [framePerm2_one]; exact W.one_mem
      | mul a b ha hb iha ihb => rw [framePerm2_mul]; exact W.mul_mem iha ihb

@[expose] def flipSign2 (S : Finset (Fin r)) (i : Fin (r + 2)) : ZMod 3 :=
  if h : i.val < r then (if (⟨i.val, h⟩ : Fin r) ∈ S then -1 else 1) else 1

theorem flipSign2_castSucc (S : Finset (Fin r)) (i : Fin r) :
    flipSign2 S i.castSucc.castSucc = if i ∈ S then -1 else 1 := by
  rw [flipSign2, dif_pos (show (i.castSucc.castSucc : Fin (r + 2)).val < r from by simp)]
  have h : (⟨(i.castSucc.castSucc : Fin (r + 2)).val, i.isLt⟩ : Fin r) = i := Fin.ext rfl
  rw [h]

theorem flipSign2_extra (S : Finset (Fin r)) :
    flipSign2 S ((Fin.last r).castSucc) = 1 := by
  rw [flipSign2, dif_neg (show ¬ ((Fin.last r).castSucc : Fin (r + 2)).val < r by simp [Fin.val_last])]

theorem flipSign2_last (S : Finset (Fin r)) :
    flipSign2 S (Fin.last (r + 1)) = 1 := by
  rw [flipSign2, dif_neg (show ¬ (Fin.last (r + 1)).val < r by simp)]

theorem flipSign2_mul_self (S : Finset (Fin r)) (i : Fin (r + 2)) :
    flipSign2 S i * flipSign2 S i = 1 := by
  by_cases h : i.val < r
  · rw [flipSign2, dif_pos h]
    split_ifs <;> norm_num
  · rw [flipSign2, dif_neg h]
    norm_num

@[expose] def frameFlip2 (S : Finset (Fin r)) : Vn (r + 2) ≃ₗ[ZMod 3] Vn (r + 2) where
  toFun v := fun i => flipSign2 S i * v i
  invFun v := fun i => flipSign2 S i * v i
  map_add' v w := by funext i; simp only [Pi.add_apply]; ring
  map_smul' c v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  left_inv v := by
    funext i
    show flipSign2 S i * (flipSign2 S i * v i) = v i
    rw [← mul_assoc, flipSign2_mul_self, one_mul]
  right_inv v := by
    funext i
    show flipSign2 S i * (flipSign2 S i * v i) = v i
    rw [← mul_assoc, flipSign2_mul_self, one_mul]

theorem frameFlip2_apply (S : Finset (Fin r)) (v : Vn (r + 2)) (i : Fin (r + 2)) :
    frameFlip2 S v i = flipSign2 S i * v i := rfl

theorem frameFlip2_xLast2 (S : Finset (Fin r)) : frameFlip2 S (xLast2 r) = xLast2 r := by
  funext k
  rw [frameFlip2_apply]
  cases k using Fin.lastCases with
  | last => rw [flipSign2_last, one_mul]
  | cast j =>
      cases j using Fin.lastCases with
      | last => rw [flipSign2_extra, one_mul]
      | cast i =>
          rw [flipSign2_castSucc, xLast2_frame i, mul_zero]

theorem frameFlip2_empty : frameFlip2 (∅ : Finset (Fin r)) = 1 := by
  apply LinearEquiv.ext
  intro v
  funext k
  rw [frameFlip2_apply]
  cases k using Fin.lastCases with
  | last => rw [flipSign2_last]; simp
  | cast j =>
      cases j using Fin.lastCases with
      | last => rw [flipSign2_extra]; simp
      | cast i => rw [flipSign2_castSucc]; simp

theorem frameFlip2_insert (i : Fin r) (S : Finset (Fin r)) (hi : i ∉ S) :
    frameFlip2 (insert i S) = sgnFlip2 i * frameFlip2 S := by
  apply LinearEquiv.ext
  intro v
  funext k
  rw [LinearEquiv.mul_apply, sgnFlip2_coord, frameFlip2_apply]
  simp only [frameFlip2_apply]
  cases k using Fin.lastCases with
  | last =>
      rw [if_neg (fun hh => frameIndex_ne_last i hh.symm), flipSign2_last, flipSign2_last]
      try ring
  | cast j =>
      cases j using Fin.lastCases with
      | last =>
          rw [if_neg (extraIndex_ne_frame i), flipSign2_extra, flipSign2_extra]
          try ring
      | cast k =>
          rw [flipSign2_castSucc, flipSign2_castSucc]
          by_cases hki : k = i
          · rw [hki]
            rw [if_pos rfl, if_pos (Finset.mem_insert_self i S), if_neg hi]
            simp
          · have hki' : ¬ (k.castSucc.castSucc = i.castSucc.castSucc) :=
              fun hh => hki (Fin.castSucc_injective _ (Fin.castSucc_injective _ hh))
            have hmem : (k ∈ insert i S) ↔ (k ∈ S) := by
              rw [Finset.mem_insert]
              exact ⟨fun h => h.resolve_left hki, fun h => Or.inr h⟩
            rw [if_neg hki', if_congr hmem rfl rfl, flipSign2_castSucc]
            try ring_nf

theorem frameFlip2_mem {W : Subgroup (Vn (r + 2) ≃ₗ[ZMod 3] Vn (r + 2))}
    (hW : ∀ i, sgnFlip2 i ∈ W) (S : Finset (Fin r)) : frameFlip2 S ∈ W := by
  induction S using Finset.induction with
  | empty => rw [frameFlip2_empty]; exact W.one_mem
  | insert i S hi ih => rw [frameFlip2_insert i S hi]; exact W.mul_mem (hW i) ih

theorem sgnDiff2_mul_self (i j : Fin r) (h : i ≠ j) :
    sgnDiff2 i j h * sgnDiff2 i j h = 1 := by
  rw [sgnDiff2]
  exact refl_mul_self _ _ _

theorem sgnSum2_eq (i j : Fin r) (h : i ≠ j) :
    sgnSum2 i j h = sgnFlip2 i * sgnFlip2 j * sgnDiff2 i j h := by
  apply LinearEquiv.ext
  intro v
  funext k
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  simp only [sgnFlip2, sgnSum2, sgnDiff2]
  rw [refl_apply, refl_apply, refl_apply, refl_apply]
  by_cases hki : k = i.castSucc.castSucc
  · subst hki
    simp [frameE2, h, Ne.symm h]
    ring_nf
  · by_cases hkj : k = j.castSucc.castSucc
    · subst hkj
      simp [frameE2, h, hki]
      ring_nf
    · simp [frameE2, h, Ne.symm h, hki, hkj]

theorem sgnFlip2_mul_sgnFlip2_mem {W : Subgroup (Vn (r + 2) ≃ₗ[ZMod 3] Vn (r + 2))}
    (hWd : ∀ (i j : Fin r) (h : i ≠ j), sgnDiff2 i j h ∈ W)
    (hWs : ∀ (i j : Fin r) (h : i ≠ j), sgnSum2 i j h ∈ W)
    {i j : Fin r} (h : i ≠ j) : sgnFlip2 i * sgnFlip2 j ∈ W := by
  have hsum := hWs i j h
  have hdiff := hWd i j h
  have hEq : sgnSum2 i j h * sgnDiff2 i j h = sgnFlip2 i * sgnFlip2 j := by
    rw [sgnSum2_eq i j h, mul_assoc, sgnDiff2_mul_self, mul_one]
  rw [← hEq]
  exact W.mul_mem hsum hdiff

theorem frameFlip_mem_even2 {W : Subgroup (Vn (r + 2) ≃ₗ[ZMod 3] Vn (r + 2))}
    (hWd : ∀ (i j : Fin r) (h : i ≠ j), sgnDiff2 i j h ∈ W)
    (hWs : ∀ (i j : Fin r) (h : i ≠ j), sgnSum2 i j h ∈ W)
    (S : Finset (Fin r)) (hS : Even S.card) : frameFlip2 S ∈ W := by
  classical
  let P : ℕ → Prop := fun n => ∀ S : Finset (Fin r), S.card = n →
    Even S.card → frameFlip2 S ∈ W
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro S hcard hseven
      rcases Finset.eq_empty_or_nonempty S with rfl | hne
      · rw [frameFlip2_empty]
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
        have ihS' : frameFlip2 S' ∈ W := ih S'.card hlt S' rfl heven'
        have hni : i ∉ insert j S' := by
          intro hh
          rcases Finset.mem_insert.mp hh with rfl | hh'
          · exact hji rfl
          · rcases Finset.mem_erase.mp hh' with ⟨_, hh''⟩
            exact (Finset.mem_erase.mp hh'').1 rfl
        have hnj : j ∉ S' := by
          simp only [S', Finset.mem_erase]
          exact fun h => h.1 rfl
        rw [hS'eq, frameFlip2_insert i (insert j S') hni,
          frameFlip2_insert j S' hnj]
        rw [← mul_assoc]
        exact W.mul_mem (sgnFlip2_mul_sgnFlip2_mem hWd hWs (Ne.symm hji)) ihS'
  exact hP S.card S rfl hS


theorem sym_frame_D_ne2 {c a : Vn (r + 2)} (hr : 3 ≤ r)
    (hD : ∀ i j, i ≠ j → (a ⬝ᵥ (frameE2 r i - frameE2 r j) = 0 ↔
      (frameE2 r i - frameE2 r j) ⬝ᵥ c = 0))
    (hS : ∀ i j, i ≠ j → (a ⬝ᵥ (frameE2 r i + frameE2 r j) = 0 ↔
      (frameE2 r i + frameE2 r j) ⬝ᵥ c = 0))
    (i : Fin r) (hi : c i.castSucc.castSucc ≠ 0) : a i.castSucc.castSucc ≠ 0 := by
  classical
  have hD' : ∀ (p q : Fin r) (h : p ≠ q),
      a p.castSucc.castSucc - a q.castSucc.castSucc = 0 ↔ c p.castSucc.castSucc - c q.castSucc.castSucc = 0 := by
    intro p q h
    rw [← dot_frameE2_sub, ← frameE2_sub_dot]
    exact hD p q h
  have hS' : ∀ (p q : Fin r) (h : p ≠ q),
      a p.castSucc.castSucc + a q.castSucc.castSucc = 0 ↔ c p.castSucc.castSucc + c q.castSucc.castSucc = 0 := by
    intro p q h
    rw [← dot_frameE2_add, ← frameE2_add_dot]
    exact hS p q h
  intro hai
  have hzero : ∀ j : Fin r, j ≠ i → c j.castSucc.castSucc = 0 := by
    intro j hj
    by_contra hcj
    rcases zmod3_eq_or_eq_neg hi hcj with h | h
    · have haj : a j.castSucc.castSucc = 0 := by
        have hd : a i.castSucc.castSucc - a j.castSucc.castSucc = 0 :=
          (hD' i j (Ne.symm hj)).mpr (by rw [h, sub_self])
        have h1 : a i.castSucc.castSucc = a j.castSucc.castSucc := sub_eq_zero.mp hd
        rw [← h1]; exact hai
      have hsum : a i.castSucc.castSucc + a j.castSucc.castSucc = 0 := by rw [hai, haj, add_zero]
      have hc : c i.castSucc.castSucc + c j.castSucc.castSucc = 0 := (hS' i j (Ne.symm hj)).mp hsum
      rw [h] at hc
      have h2 : (2 : ZMod 3) * c i.castSucc.castSucc = 0 := by rw [two_mul]; exact hc
      exact zmod3_two_mul_ne_zero _ hi h2
    · have hsum : a i.castSucc.castSucc + a j.castSucc.castSucc = 0 :=
        (hS' i j (Ne.symm hj)).mpr (by rw [h]; abel)
      have haj : a j.castSucc.castSucc = -a i.castSucc.castSucc := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsum
      have hd : a i.castSucc.castSucc - a j.castSucc.castSucc = 0 := by rw [hai, haj, hai]; ring
      have hc : c i.castSucc.castSucc - c j.castSucc.castSucc = 0 := (hD' i j (Ne.symm hj)).mp hd
      rw [h] at hc
      have h2 : (2 : ZMod 3) * c i.castSucc.castSucc = 0 := by
        rw [sub_neg_eq_add, ← two_mul] at hc; exact hc
      exact zmod3_two_mul_ne_zero _ hi h2
  have hne : ∀ j : Fin r, j ≠ i → a j.castSucc.castSucc ≠ 0 := by
    intro j hj haj
    have hd : a i.castSucc.castSucc - a j.castSucc.castSucc = 0 := by rw [hai, haj, sub_zero]
    have hc : c i.castSucc.castSucc - c j.castSucc.castSucc = 0 := (hD' i j (Ne.symm hj)).mp hd
    rw [hzero j hj, sub_zero] at hc
    exact hi hc
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) i
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega : 2 < r)
  have hdjk : a j.castSucc.castSucc - a k.castSucc.castSucc = 0 :=
    (hD' j k (Ne.symm hkj)).mpr (by rw [hzero j hj, hzero k hki, sub_self])
  have heq : a j.castSucc.castSucc = a k.castSucc.castSucc := sub_eq_zero.mp hdjk
  have hsum : a j.castSucc.castSucc + a k.castSucc.castSucc = 0 :=
    (hS' j k (Ne.symm hkj)).mpr (by rw [hzero j hj, hzero k hki, add_zero])
  rw [← heq] at hsum
  have h2 : (2 : ZMod 3) * a j.castSucc.castSucc = 0 := by rw [two_mul]; exact hsum
  exact hne j hj ((zmod3_two_mul_eq_zero _).mp h2)

theorem sym_frame_D2 {c a : Vn (r + 2)} (hr : 3 ≤ r)
    (hD : ∀ i j, i ≠ j → (a ⬝ᵥ (frameE2 r i - frameE2 r j) = 0 ↔
      (frameE2 r i - frameE2 r j) ⬝ᵥ c = 0))
    (hS : ∀ i j, i ≠ j → (a ⬝ᵥ (frameE2 r i + frameE2 r j) = 0 ↔
      (frameE2 r i + frameE2 r j) ⬝ᵥ c = 0)) :
    ∃ l : ZMod 3, ∀ i : Fin r, a i.castSucc.castSucc = l * c i.castSucc.castSucc := by
  classical
  have hDswap : ∀ i j, i ≠ j → (c ⬝ᵥ (frameE2 r i - frameE2 r j) = 0 ↔
      (frameE2 r i - frameE2 r j) ⬝ᵥ a = 0) := by
    intro i j h
    rw [dotProduct_comm c, dotProduct_comm (frameE2 r i - frameE2 r j) a]
    exact (hD i j h).symm
  have hSswap : ∀ i j, i ≠ j → (c ⬝ᵥ (frameE2 r i + frameE2 r j) = 0 ↔
      (frameE2 r i + frameE2 r j) ⬝ᵥ a = 0) := by
    intro i j h
    rw [dotProduct_comm c, dotProduct_comm (frameE2 r i + frameE2 r j) a]
    exact (hS i j h).symm
  have hF : ∀ i : Fin r, (a i.castSucc.castSucc = 0 ↔ c i.castSucc.castSucc = 0) := by
    intro i
    constructor
    · intro ha0
      by_contra hc0
      exact sym_frame_D_ne2 hr hD hS i hc0 ha0
    · intro hc0
      by_contra ha0
      exact sym_frame_D_ne2 hr hDswap hSswap i ha0 hc0
  exact sym_frame_B2 hD hS hF

@[expose] def canonC2 (r k : ℕ) (e g : ZMod 3) : Vn (r + 2) :=
  fun i => if i.val < r then (if r - k ≤ i.val then 1 else 0) else if i.val = r then e else g

@[expose] def canonA2 (r k : ℕ) (l e d : ZMod 3) : Vn (r + 2) :=
  fun i => if i.val < r then (if r - k ≤ i.val then l else 0) else if i.val = r then e else d

@[expose] def canonD2 (r : ℕ) (e g : ZMod 3) : Vn (r + 2) :=
  fun i => if i.val < r then (if i.val = r - 1 then 2 else 1) else if i.val = r then e else g

@[expose] def canonAD2 (r : ℕ) (l e d : ZMod 3) : Vn (r + 2) :=
  fun i => if i.val < r then (if i.val = r - 1 then 2 * l else l) else if i.val = r then e else d

theorem canonC2_castSucc (k : ℕ) (e g : ZMod 3) (i : Fin r) :
    canonC2 r k e g i.castSucc.castSucc = if r - k ≤ i.val then 1 else 0 := by
  simp [canonC2, i.isLt]

theorem canonC2_extra (k : ℕ) (e g : ZMod 3) :
    canonC2 r k e g ((Fin.last r).castSucc) = e := by
  simp [canonC2, Fin.val_last]

theorem canonC2_last (k : ℕ) (e g : ZMod 3) :
    canonC2 r k e g (Fin.last (r + 1)) = g := by
  simp [canonC2, Fin.val_last]

theorem canonA2_castSucc (k : ℕ) (l e d : ZMod 3) (i : Fin r) :
    canonA2 r k l e d i.castSucc.castSucc = if r - k ≤ i.val then l else 0 := by
  simp [canonA2, i.isLt]

theorem canonA2_extra (k : ℕ) (l e d : ZMod 3) :
    canonA2 r k l e d ((Fin.last r).castSucc) = e := by
  simp [canonA2, Fin.val_last]

theorem canonA2_last (k : ℕ) (l e d : ZMod 3) :
    canonA2 r k l e d (Fin.last (r + 1)) = d := by
  simp [canonA2, Fin.val_last]

theorem canonD2_castSucc (e g : ZMod 3) (i : Fin r) :
    canonD2 r e g i.castSucc.castSucc = if i.val = r - 1 then 2 else 1 := by
  simp [canonD2, i.isLt]

theorem canonD2_extra (e g : ZMod 3) :
    canonD2 r e g ((Fin.last r).castSucc) = e := by
  simp [canonD2, Fin.val_last]

theorem canonD2_last (e g : ZMod 3) :
    canonD2 r e g (Fin.last (r + 1)) = g := by
  simp [canonD2, Fin.val_last]

theorem canonAD2_castSucc (l e d : ZMod 3) (i : Fin r) :
    canonAD2 r l e d i.castSucc.castSucc = if i.val = r - 1 then 2 * l else l := by
  simp [canonAD2, i.isLt]

theorem canonAD2_extra (l e d : ZMod 3) :
    canonAD2 r l e d ((Fin.last r).castSucc) = e := by
  simp [canonAD2, Fin.val_last]

theorem canonAD2_last (l e d : ZMod 3) :
    canonAD2 r l e d (Fin.last (r + 1)) = d := by
  simp [canonAD2, Fin.val_last]

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
theorem exists_frame_canonical_D2 {W : Subgroup (Vn (r + 2) ≃ₗ[ZMod 3] Vn (r + 2))}
    (hr : 3 ≤ r)
    (hWd : ∀ (i j : Fin r) (h : i ≠ j), sgnDiff2 i j h ∈ W)
    (hWs : ∀ (i j : Fin r) (h : i ≠ j), sgnSum2 i j h ∈ W)
    {c : Vn (r + 2)} (hcH : ∃ i : Fin r, c i.castSucc.castSucc ≠ 0) :
    ∃ w ∈ W, ∃ k : ℕ, 1 ≤ k ∧ k ≤ r ∧ w (xLast2 r) = xLast2 r ∧
      (w c) (Fin.last (r + 1)) = c (Fin.last (r + 1)) ∧
      ((∀ i : Fin r, (w c) i.castSucc.castSucc = if r - k ≤ i.val then 1 else 0) ∨
       (k = r ∧ ∀ i : Fin r, (w c) i.castSucc.castSucc = if i.val = r - 1 then 2 else 1)) := by
  let key : Fin r → ℕ := fun i => if c i.castSucc.castSucc = 0 then 0 else 1
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
  let w1 : Vn (r + 2) ≃ₗ[ZMod 3] Vn (r + 2) := framePerm2 σ⁻¹
  have hw1 : ∀ i : Fin r, (w1 c) i.castSucc.castSucc = c (σ i).castSucc.castSucc := by
    intro i
    change framePerm2 σ⁻¹ c i.castSucc.castSucc = c (σ i).castSucc.castSucc
    rw [framePerm2_apply_castSucc, inv_inv]
  have hw1zero : ∀ i : Fin r, (w1 c) i.castSucc.castSucc = 0 ↔ i.val < r - k := by
    intro i
    rw [hw1]
    have h1 : key (σ i) = 0 ↔ c (σ i).castSucc.castSucc = 0 := by
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
    framePerm2_mem_adj (fun i h => hWd i ⟨i.val + 1, h⟩ _) σ⁻¹
  let S : Finset (Fin r) := Finset.univ.filter (fun i => (w1 c) i.castSucc.castSucc = 2)
  have hmemS : ∀ i : Fin r, i ∈ S ↔ (w1 c) i.castSucc.castSucc = 2 := by
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
      (frameFlip2 T (w1 c)) (Fin.last (r + 1)) = c (Fin.last (r + 1)) := by
    rw [frameFlip2_apply, flipSign2_last, one_mul]
    change framePerm2 σ⁻¹ c (Fin.last (r + 1)) = c (Fin.last (r + 1))
    rw [framePerm2_apply_last]
  have hwx_any (T : Finset (Fin r)) : (frameFlip2 T * w1) (xLast2 r) = xLast2 r := by
    rw [LinearEquiv.mul_apply, framePerm2_xLast2, frameFlip2_xLast2]
  have hvalS : ∀ i : Fin r, (frameFlip2 S (w1 c)) i.castSucc.castSucc =
      if r - k ≤ i.val then 1 else 0 := by
    intro i
    rw [frameFlip2_apply, flipSign2_castSucc]
    by_cases hlt : r - k ≤ i.val
    · have hne : (w1 c) i.castSucc.castSucc ≠ 0 := by
        intro h0
        have hlt2 := (hw1zero i).mp h0
        omega
      rw [if_pos hlt]
      by_cases h2 : (w1 c) i.castSucc.castSucc = 2
      · rw [if_pos ((hmemS i).mpr h2), h2]
        decide
      · have h1 : (w1 c) i.castSucc.castSucc = 1 := by
          rcases zmod3_ne_zero _ hne with h | h
          · exact h
          · exact absurd h h2
        rw [if_neg (fun hh => h2 ((hmemS i).mp hh)), h1]
        decide
    · have h0 : (w1 c) i.castSucc.castSucc = 0 :=
        (hw1zero i).mpr (Nat.lt_of_not_le hlt)
      have hnotS : i ∉ S := fun hh => by
        have h2 : (w1 c) i.castSucc.castSucc = 2 := (hmemS i).mp hh
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
  · exact ⟨frameFlip2 S * w1, W.mul_mem (frameFlip_mem_even2 hWd hWs S hEven) hw1W,
      k, hk1, hk2, hwx_any S, hlast_any S, Or.inl hvalS⟩
  · have hOdd : Odd S.card := by
      rcases Nat.even_or_odd S.card with h | h
      · exact absurd h hEven
      · exact h
    by_cases hkr : k = r
    · let z : Fin r := ⟨r - 1, by omega⟩
      have hzval : z.val = r - 1 := rfl
      have hz0 : (w1 c) z.castSucc.castSucc ≠ 0 := by
        intro h0
        have hlt := (hw1zero z).mp h0
        rw [hzval] at hlt
        omega
      have hvalOne : ∀ i : Fin r, (frameFlip2 S (w1 c)) i.castSucc.castSucc = 1 := by
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
      have hvalExtra : ∀ i : Fin r, (frameFlip2 S' (w1 c)) i.castSucc.castSucc =
          if i.val = r - 1 then 2 else 1 := by
        intro i
        by_cases hiz : i = z
        · subst hiz
          by_cases hzS : z ∈ S
          · simp only [S', if_pos hzS, frameFlip2_apply, flipSign2_castSucc]
            have hznot : z ∉ S.erase z := fun h => (Finset.mem_erase.mp h).1 rfl
            simp only [if_neg hznot]
            have h2 : (w1 c) z.castSucc.castSucc = 2 := (hmemS z).mp hzS
            rw [h2, one_mul, if_pos hzval]
          · simp only [S', if_neg hzS, frameFlip2_apply, flipSign2_castSucc]
            simp only [if_pos (Finset.mem_insert_self z S)]
            have hne2 : (w1 c) z.castSucc.castSucc ≠ 2 := fun h => hzS ((hmemS z).mpr h)
            have h1 : (w1 c) z.castSucc.castSucc = 1 := by
              rcases zmod3_ne_zero _ hz0 with h | h
              · exact h
              · exact absurd h hne2
            rw [h1, if_pos hzval]
            decide
        · rw [frameFlip2_apply, flipSign2_castSucc]
          have hival : i.val ≠ r - 1 := by
            intro hv
            apply hiz
            exact Fin.ext (by rw [hzval, hv])
          rw [if_neg hival]
          by_cases hzS : z ∈ S
          · simp only [S', if_pos hzS, hflip_erase z hzS i hiz]
            have h := hvalOne i
            rw [frameFlip2_apply, flipSign2_castSucc] at h
            exact h
          · simp only [S', if_neg hzS, hflip_insert z hzS i hiz]
            have h := hvalOne i
            rw [frameFlip2_apply, flipSign2_castSucc] at h
            exact h
      refine ⟨frameFlip2 S' * w1,
        W.mul_mem (frameFlip_mem_even2 hWd hWs S' hS'even) hw1W,
        k, hk1, hk2, hwx_any S', hlast_any S', Or.inr ⟨hkr, hvalExtra⟩⟩
    · let z : Fin r := ⟨0, by omega⟩
      have hzval : z.val = 0 := rfl
      have hz0 : (w1 c) z.castSucc.castSucc = 0 := by
        rw [hw1zero z, hzval]
        omega
      have hzS : z ∉ S := by
        intro h
        have h2 : (w1 c) z.castSucc.castSucc = 2 := (hmemS z).mp h
        rw [hz0] at h2
        exact (by decide : (0 : ZMod 3) ≠ 2) h2
      let S' : Finset (Fin r) := insert z S
      have hS'even : Even S'.card := by
        simp only [S', Finset.card_insert_of_notMem hzS]
        obtain ⟨m, hm⟩ := hOdd
        exact ⟨m + 1, by omega⟩
      have hvalStd : ∀ i : Fin r, (frameFlip2 S' (w1 c)) i.castSucc.castSucc =
          if r - k ≤ i.val then 1 else 0 := by
        intro i
        by_cases hiz : i = z
        · subst hiz
          simp only [S', frameFlip2_apply, flipSign2_castSucc]
          simp only [if_pos (Finset.mem_insert_self z S), hz0, mul_zero]
          have hlt : ¬ (r - k ≤ z.val) := by
            rw [hzval]
            omega
          rw [if_neg hlt]
        · simp only [S', frameFlip2_apply, flipSign2_castSucc]
          have h := hvalS i
          rw [frameFlip2_apply, flipSign2_castSucc] at h
          calc (if i ∈ insert z S then (-1 : ZMod 3) else 1) * (w1 c) i.castSucc.castSucc
              = (if i ∈ S then -1 else 1) * (w1 c) i.castSucc.castSucc := by
                  congr 1
                  exact hflip_insert z hzS i hiz
            _ = if r - k ≤ i.val then 1 else 0 := h
      refine ⟨frameFlip2 S' * w1,
        W.mul_mem (frameFlip_mem_even2 hWd hWs S' hS'even) hw1W,
        k, hk1, hk2, hwx_any S', hlast_any S', Or.inl hvalStd⟩

theorem TestHyp.exists_canonical_D2 {W A M : Subgroup (Vn (r + 2) ≃ₗ[ZMod 3] Vn (r + 2))}
    (hr : 3 ≤ r) (hT : TestHyp W (xLast2 r) A M)
    (hWd : ∀ (i j : Fin r) (h : i ≠ j), sgnDiff2 i j h ∈ W)
    (hWs : ∀ (i j : Fin r) (h : i ≠ j), sgnSum2 i j h ∈ W)
    {u : Vn (r + 2) ≃ₗ[ZMod 3] Vn (r + 2)} (hu : u ∈ A) (huR : IsRefl u)
    (hux : ¬ FixesLine (xLast2 r) u) :
    ∃ (w : Vn (r + 2) ≃ₗ[ZMod 3] Vn (r + 2)) (_ : w ∈ W) (k : ℕ),
      k ≤ r ∧ w (xLast2 r) = xLast2 r ∧
      ((∃ (l e g e' d : ZMod 3) (h : canonA2 r k l e' d ⬝ᵥ canonC2 r k e g = 2),
          w * u * w⁻¹ = refl (canonC2 r k e g) (canonA2 r k l e' d) h) ∨
       (k = r ∧ ∃ (l e g e' d : ZMod 3) (h : canonAD2 r l e' d ⬝ᵥ canonD2 r e g = 2),
          w * u * w⁻¹ = refl (canonD2 r e g) (canonAD2 r l e' d) h)) := by
  classical
  obtain ⟨c, a, hac, rfl⟩ := eq_refl_of_isRefl huR
  have hD : ∀ i j, i ≠ j → (a ⬝ᵥ (frameE2 r i - frameE2 r j) = 0 ↔
      (frameE2 r i - frameE2 r j) ⬝ᵥ c = 0) := by
    intro i j hij
    have hmem : sgnDiff2 i j hij ∈ A := hT.le (hT.W_le (hWd i j hij))
    have hmem' : refl (Pi.single i.castSucc.castSucc 1 - Pi.single j.castSucc.castSucc 1)
        (Pi.single i.castSucc.castSucc 1 - Pi.single j.castSucc.castSucc 1)
        (dot_sub_single_self i.castSucc.castSucc j.castSucc.castSucc
          (fun hh => hij (Fin.castSucc_injective _ (Fin.castSucc_injective _ hh)))) ∈ A := hmem
    have hs := sym_of_noTransv hT.noTransv hac
      (dot_sub_single_self i.castSucc.castSucc j.castSucc.castSucc
        (fun hh => hij (Fin.castSucc_injective _ (Fin.castSucc_injective _ hh)))) hu hmem'
    simpa [frameE2] using hs
  have hS : ∀ i j, i ≠ j → (a ⬝ᵥ (frameE2 r i + frameE2 r j) = 0 ↔
      (frameE2 r i + frameE2 r j) ⬝ᵥ c = 0) := by
    intro i j hij
    have hmem : sgnSum2 i j hij ∈ A := hT.le (hT.W_le (hWs i j hij))
    exact sym_of_noTransv hT.noTransv hac (frameE2_add_self i j hij) hu hmem
  by_cases hcH : ∃ i : Fin r, c i.castSucc.castSucc ≠ 0
  · obtain ⟨w, hwW, k, hk1, hk2, hwx, hwlast, hshape⟩ :=
      exists_frame_canonical_D2 hr hWd hWs hcH
    set c' : Vn (r + 2) := w c with hc'def
    set a' : Vn (r + 2) := dualVec (w.symm : Vn (r + 2) →ₗ[ZMod 3] Vn (r + 2)) a with ha'def
    have hac' : a' ⬝ᵥ c' = 2 := by
      rw [ha'def, hc'def, dualVec_dotProduct]
      simpa using hac
    have hconj : w * refl c a hac * w⁻¹ = refl c' a' hac' := conj_refl w c a hac
    have hmemA : refl c' a' hac' ∈ A := by
      rw [← hconj]
      exact A.mul_mem (A.mul_mem (hT.le (hT.W_le hwW)) hu)
        (A.inv_mem (hT.le (hT.W_le hwW)))
    have hD' : ∀ i j, i ≠ j → (a' ⬝ᵥ (frameE2 r i - frameE2 r j) = 0 ↔
        (frameE2 r i - frameE2 r j) ⬝ᵥ c' = 0) := by
      intro i j hij
      have hmem : sgnDiff2 i j hij ∈ A := hT.le (hT.W_le (hWd i j hij))
      have hmem' : refl (Pi.single i.castSucc.castSucc 1 - Pi.single j.castSucc.castSucc 1)
          (Pi.single i.castSucc.castSucc 1 - Pi.single j.castSucc.castSucc 1)
          (dot_sub_single_self i.castSucc.castSucc j.castSucc.castSucc
            (fun hh => hij (Fin.castSucc_injective _ (Fin.castSucc_injective _ hh)))) ∈ A := hmem
      have hs := sym_of_noTransv hT.noTransv hac'
        (dot_sub_single_self i.castSucc.castSucc j.castSucc.castSucc
          (fun hh => hij (Fin.castSucc_injective _ (Fin.castSucc_injective _ hh)))) hmemA hmem'
      simpa [frameE2] using hs
    have hS' : ∀ i j, i ≠ j → (a' ⬝ᵥ (frameE2 r i + frameE2 r j) = 0 ↔
        (frameE2 r i + frameE2 r j) ⬝ᵥ c' = 0) := by
      intro i j hij
      have hmem : sgnSum2 i j hij ∈ A := hT.le (hT.W_le (hWs i j hij))
      exact sym_of_noTransv hT.noTransv hac' (frameE2_add_self i j hij) hmemA hmem
    obtain ⟨l', hl'⟩ := sym_frame_D2 hr hD' hS'
    set e : ZMod 3 := c' ((Fin.last r).castSucc) with he_def
    set g : ZMod 3 := c' (Fin.last (r + 1)) with hg_def
    set e' : ZMod 3 := a' ((Fin.last r).castSucc) with he'_def
    set d' : ZMod 3 := a' (Fin.last (r + 1)) with hd'_def
    rcases hshape with hstd | ⟨hkr, hextra⟩
    · have hc' : c' = canonC2 r k e g := by
        funext i
        cases i using Fin.lastCases with
        | last => rw [canonC2_last]
        | cast j =>
            cases j using Fin.lastCases with
            | last => rw [canonC2_extra]
            | cast k' => rw [canonC2_castSucc]; exact hstd k'
      have ha' : a' = canonA2 r k l' e' d' := by
        funext i
        cases i using Fin.lastCases with
        | last => rw [canonA2_last]
        | cast j =>
            cases j using Fin.lastCases with
            | last => rw [canonA2_extra]
            | cast k' =>
                rw [canonA2_castSucc, hl' k', hc', canonC2_castSucc]
                by_cases hlt : r - k ≤ k'.val
                · rw [if_pos hlt, if_pos hlt, mul_one]
                · rw [if_neg hlt, if_neg hlt, mul_zero]
      have hfinalProof : canonA2 r k l' e' d' ⬝ᵥ canonC2 r k e g = 2 := by
        rw [← ha', ← hc']
        exact hac'
      refine ⟨w, hwW, k, hk2, hwx, Or.inl ⟨l', e, g, e', d', hfinalProof, ?_⟩⟩
      calc w * refl c a hac * w⁻¹ = refl c' a' hac' := hconj
        _ = refl (canonC2 r k e g) (canonA2 r k l' e' d') hfinalProof := by
            apply LinearEquiv.ext
            intro v
            rw [refl_apply, refl_apply, hc', ha']
    · have hc' : c' = canonD2 r e g := by
        funext i
        cases i using Fin.lastCases with
        | last => rw [canonD2_last]
        | cast j =>
            cases j using Fin.lastCases with
            | last => rw [canonD2_extra]
            | cast k' => rw [canonD2_castSucc]; exact hextra k'
      have ha' : a' = canonAD2 r l' e' d' := by
        funext i
        cases i using Fin.lastCases with
        | last => rw [canonAD2_last]
        | cast j =>
            cases j using Fin.lastCases with
            | last => rw [canonAD2_extra]
            | cast k' =>
                rw [canonAD2_castSucc, hl' k', hc', canonD2_castSucc]
                by_cases hlt : k'.val = r - 1
                · rw [if_pos hlt, if_pos hlt]; ring
                · rw [if_neg hlt, if_neg hlt]; ring
      have hfinalProof : canonAD2 r l' e' d' ⬝ᵥ canonD2 r e g = 2 := by
        rw [← ha', ← hc']
        exact hac'
      refine ⟨w, hwW, k, hk2, hwx, Or.inr ⟨hkr, ⟨l', e, g, e', d', hfinalProof, ?_⟩⟩⟩
      calc w * refl c a hac * w⁻¹ = refl c' a' hac' := hconj
        _ = refl (canonD2 r e g) (canonAD2 r l' e' d') hfinalProof := by
            apply LinearEquiv.ext
            intro v
            rw [refl_apply, refl_apply, hc', ha']
  · simp only [not_exists, not_not] at hcH
    obtain ⟨l, hl⟩ := sym_frame_D2 hr hD hS
    have haframe : ∀ i : Fin r, a i.castSucc.castSucc = 0 := by
      intro i
      rw [hl i, hcH i, mul_zero]
    set e : ZMod 3 := c ((Fin.last r).castSucc) with he_def
    set g : ZMod 3 := c (Fin.last (r + 1)) with hg_def
    set e' : ZMod 3 := a ((Fin.last r).castSucc) with he'_def
    set d : ZMod 3 := a (Fin.last (r + 1)) with hd_def
    have hc_eq : c = canonC2 r 0 e g := by
      funext i
      by_cases hi : i.val < r
      · rw [canonC2, if_pos hi]
        have hri : ¬ r ≤ i.val := by omega
        rw [if_neg (by omega : ¬ r - 0 ≤ i.val)]
        have hii : i = (⟨i.val, hi⟩ : Fin r).castSucc.castSucc := Fin.ext rfl
        rw [hii]
        exact hcH ⟨i.val, hi⟩
      · by_cases hir : i.val = r
        · have hii : i = ((Fin.last r).castSucc : Fin (r + 2)) := Fin.ext (by
            rw [Fin.val_castSucc, Fin.val_last]
            exact hir)
          rw [hii, canonC2_extra]
        · have hil : i.val = r + 1 := by
            have := i.isLt
            omega
          have hii : i = Fin.last (r + 1) := Fin.ext (by
            rw [Fin.val_last]
            exact hil)
          rw [hii, canonC2_last]
    have ha_eq : a = canonA2 r 0 l e' d := by
      funext i
      by_cases hi : i.val < r
      · rw [canonA2, if_pos hi]
        have hri : ¬ r ≤ i.val := by omega
        rw [if_neg (by omega : ¬ r - 0 ≤ i.val)]
        have hii : i = (⟨i.val, hi⟩ : Fin r).castSucc.castSucc := Fin.ext rfl
        rw [hii]
        exact haframe ⟨i.val, hi⟩
      · by_cases hir : i.val = r
        · have hii : i = ((Fin.last r).castSucc : Fin (r + 2)) := Fin.ext (by
            rw [Fin.val_castSucc, Fin.val_last]
            exact hir)
          rw [hii, canonA2_extra]
        · have hil : i.val = r + 1 := by
            have := i.isLt
            omega
          have hii : i = Fin.last (r + 1) := Fin.ext (by
            rw [Fin.val_last]
            exact hil)
          rw [hii, canonA2_last]
    have hfinalProof : canonA2 r 0 l e' d ⬝ᵥ canonC2 r 0 e g = 2 := by
      rw [← ha_eq, ← hc_eq]
      exact hac
    refine ⟨1, W.one_mem, 0, Nat.zero_le r, by simp [xLast2],
      Or.inl ⟨l, e, g, e', d, hfinalProof, ?_⟩⟩
    calc 1 * refl c a hac * 1⁻¹ = refl c a hac := by simp
      _ = refl (canonC2 r 0 e g) (canonA2 r 0 l e' d) hfinalProof := by
          apply LinearEquiv.ext
          intro v
          rw [refl_apply, refl_apply, hc_eq, ha_eq]
