module

public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.SL2Semilinear

variable {F : Type*} [Field F]

@[expose] def tvX (a : F) : F × F →+ F × F where
  toFun p := (p.1 + a * p.2, p.2)
  map_zero' := by simp
  map_add' p q := by
    ext
    · simp only [Prod.fst_add, Prod.snd_add]
      ring
    · simp

@[expose] def tvY (a : F) : F × F →+ F × F where
  toFun p := (p.1, p.2 + a * p.1)
  map_zero' := by simp
  map_add' p q := by
    ext
    · simp
    · simp only [Prod.fst_add, Prod.snd_add]
      ring

theorem tvX_apply (a : F) (p : F × F) : tvX a p = (p.1 + a * p.2, p.2) := rfl

theorem tvY_apply (a : F) (p : F × F) : tvY a p = (p.1, p.2 + a * p.1) := rfl

theorem eq_smul_of_commute (φ : F × F →+ F × F) (hX : ∀ a q, φ (tvX a q) = tvX a (φ q))
    (hY : ∀ a q, φ (tvY a q) = tvY a (φ q)) (q : F × F) : φ q = (φ (1, 0)).1 • q := by
  have h10 : (φ (1, 0)).2 = 0 := by
    have h := congrArg Prod.fst (hX 1 (1, 0))
    rw [tvX_apply, tvX_apply] at h
    simp only [mul_zero, add_zero, one_mul] at h
    linear_combination -h
  have h01 : (φ (0, 1)).1 = 0 := by
    have h := congrArg Prod.snd (hY 1 (0, 1))
    rw [tvY_apply, tvY_apply] at h
    simp only [mul_zero, add_zero, one_mul] at h
    linear_combination -h
  have hx : ∀ a : F, φ (a, 0) = (a * (φ (0, 1)).2, 0) := by
    intro a
    have h := hX a (0, 1)
    rw [tvX_apply, tvX_apply] at h
    simp only [zero_add, mul_one] at h
    have hsum : ((a, 1) : F × F) = (a, 0) + (0, 1) := by simp
    rw [hsum, map_add] at h
    have e := congrArg (fun r => r - φ (0, 1)) h
    simp only [add_sub_cancel_right] at e
    rw [e]
    ext
    · simp [h01]
    · simp
  have hy : ∀ a : F, φ (0, a) = (0, a * (φ (1, 0)).1) := by
    intro a
    have h := hY a (1, 0)
    rw [tvY_apply, tvY_apply] at h
    simp only [zero_add, mul_one] at h
    have hsum : ((1, a) : F × F) = (1, 0) + (0, a) := by simp
    rw [hsum, map_add] at h
    have e := congrArg (fun r => r - φ (1, 0)) h
    simp only [add_sub_cancel_left] at e
    rw [e]
    ext
    · simp
    · simp [h10]
  have hps : (φ (1, 0)).1 = (φ (0, 1)).2 := by
    have := congrArg Prod.fst (hx 1)
    simpa using this
  obtain ⟨u, v⟩ := q
  have hsum : ((u, v) : F × F) = (u, 0) + (0, v) := by simp
  have e1 := hx u
  have e2 := hy v
  rw [← hps] at e1
  rw [hsum, map_add, e1, e2]
  ext
  · simp [mul_comm]
  · simp [mul_comm]

theorem exists_semilinear (τ : F × F ≃+ F × F)
    (hX : ∀ (a c : F) (q : F × F), τ.symm (tvX a (τ (c • q))) = c • τ.symm (tvX a (τ q)))
    (hY : ∀ (a c : F) (q : F × F), τ.symm (tvY a (τ (c • q))) = c • τ.symm (tvY a (τ q))) :
    ∃ σ : F →+* F, ∀ (c : F) (q : F × F), τ (c • q) = σ c • τ q := by
  let φ : F → (F × F →+ F × F) := fun c =>
    { toFun := fun q => τ (c • τ.symm q)
      map_zero' := by simp
      map_add' := fun q r => by simp [smul_add] }
  have hφ : ∀ c q, φ c q = τ (c • τ.symm q) := fun _ _ => rfl
  have hφX : ∀ c a q, φ c (tvX a q) = tvX a (φ c q) := by
    intro c a q
    obtain ⟨r, rfl⟩ := τ.surjective q
    rw [hφ, hφ, τ.symm_apply_apply, ← hX a c r, τ.apply_symm_apply]
  have hφY : ∀ c a q, φ c (tvY a q) = tvY a (φ c q) := by
    intro c a q
    obtain ⟨r, rfl⟩ := τ.surjective q
    rw [hφ, hφ, τ.symm_apply_apply, ← hY a c r, τ.apply_symm_apply]
  set σf : F → F := fun c => (φ c (1, 0)).1 with hσf
  have key : ∀ c q, τ (c • q) = σf c • τ q := by
    intro c q
    have h := eq_smul_of_commute (φ c) (hφX c) (hφY c) (τ q)
    rw [hφ, τ.symm_apply_apply] at h
    exact h
  have hval : ∀ c, τ (c • τ.symm ((1 : F), (0 : F))) = (σf c, 0) := by
    intro c
    rw [key, τ.apply_symm_apply]
    ext <;> simp
  have hinj : ∀ a b : F, ((a, 0) : F × F) = (b, 0) → a = b := fun a b h => by
    have := congrArg Prod.fst h
    simpa using this
  refine ⟨{ toFun := σf, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, key⟩
  · apply hinj
    rw [← hval, one_smul, τ.apply_symm_apply]
  · intro a b
    apply hinj
    rw [← hval, mul_smul, key, hval]
    ext <;> simp
  · apply hinj
    rw [← hval, zero_smul, map_zero]
    rfl
  · intro a b
    apply hinj
    rw [← hval, add_smul, map_add, hval, hval]
    ext <;> simp

end CFSG.Quasithin.SL2Semilinear
