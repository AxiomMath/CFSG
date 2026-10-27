module

public import CFSG.Quasithin.Vol2.Ch10Reselect.ModelAlgId

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open Matrix

variable {K : Type*} [Field K]

private lemma h2_bPerm_one : bPerm K (1 : GL (Fin 2) K) = 1 := by
  apply Equiv.ext
  intro v
  simp [bPerm_apply]

private lemma h2_phi_one_one_one : phi K 1 1 1 = 1 := by
  simp [phi, sigmaPerm_one, h2_bPerm_one]

private lemma h2_rho_eq_one {g : Matrix.SpecialLinearGroup (Fin 2) K} (h : rhoSL K g = 1) :
    g = 1 := by
  have key : ∀ v, rhoSL K g v = v := fun v => by simp [h]
  have h1 : (g : Matrix (Fin 2) (Fin 2) K) *ᵥ ![1, 0] = ![1, 0] := by
    have := key (![1, 0], 0)
    rw [rhoSL_apply] at this
    exact congrArg Prod.fst this
  have h2 : (g : Matrix (Fin 2) (Fin 2) K) *ᵥ ![0, 1] = ![0, 1] := by
    have := key (![0, 1], 0)
    rw [rhoSL_apply] at this
    exact congrArg Prod.fst this
  have hM : (g : Matrix (Fin 2) (Fin 2) K) = 1 := by
    have e00 := congrFun h1 0
    have e10 := congrFun h1 1
    have e01 := congrFun h2 0
    have e11 := congrFun h2 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e00 e10 e01 e11
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e00, e10, e01, e11]
  exact Subtype.ext hM

theorem rhoSL_injective : Function.Injective (rhoSL K) := by
  exact (injective_iff_map_eq_one (rhoSL K)).2 fun _ hg => h2_rho_eq_one hg

theorem rhoSL_eq_phi (g : Matrix.SpecialLinearGroup (Fin 2) K) : rhoSL K g = phi K g 1 1 := by
  simp [phi, sigmaPerm_one, h2_bPerm_one]

theorem bPerm_eq_phi (B : GL (Fin 2) K) : bPerm K B = phi K 1 1 B := by
  simp [phi, sigmaPerm_one]

theorem rhoSL_mul_phi (h g : Matrix.SpecialLinearGroup (Fin 2) K) (σ : RingAut K)
    (B : GL (Fin 2) K) : rhoSL K h * phi K g σ B = phi K (h * g) σ B := by
  simp only [phi, map_mul, mul_assoc]

theorem phi_one_pow (σ : RingAut K) (B : GL (Fin 2) K) (n : ℕ) :
    ∃ B' : GL (Fin 2) K, (phi K 1 σ B) ^ n = phi K 1 (σ ^ n) B' := by
  induction n with
  | zero => exact ⟨1, by simp [h2_phi_one_one_one]⟩
  | succ n ih =>
    obtain ⟨B', hB'⟩ := ih
    refine ⟨glMap K σ⁻¹ B' * B, ?_⟩
    rw [pow_succ, hB', phi_mul, map_one, one_mul, ← pow_succ]

theorem bPerm_pow (B : GL (Fin 2) K) (n : ℕ) : bPerm K B ^ n = bPerm K (B ^ n) := by
  induction n with
  | zero => simp [h2_bPerm_one]
  | succ n ih => rw [pow_succ, ih, ← bPerm_mul, ← pow_succ]

theorem eq_one_of_bPerm_eq_one {B : GL (Fin 2) K} (h : bPerm K B = 1) : B = 1 := by
  have hv : ∀ v : UTilde K, bPerm K B v = v := fun v => by
    have := congrArg (fun F : Equiv.Perm (UTilde K) => F v) h
    simpa using this
  have a00 : (B : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have := congrFun (congrArg Prod.fst (hv (![1, 0], 0))) 0
    simpa [bPerm_apply] using this
  have a10 : (B : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have := congrFun (congrArg Prod.snd (hv (![1, 0], 0))) 0
    simpa [bPerm_apply] using this
  have a01 : (B : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    have := congrFun (congrArg Prod.fst (hv (0, ![1, 0]))) 0
    simpa [bPerm_apply] using this
  have a11 : (B : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    have := congrFun (congrArg Prod.snd (hv (0, ![1, 0]))) 0
    simpa [bPerm_apply] using this
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a00, a01, a10, a11]

theorem bPerm_comm_rhoSL (B : GL (Fin 2) K) (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    bPerm K B * rhoSL K g = rhoSL K g * bPerm K B := by
  exact bPerm_rho B g

end CFSG.Quasithin.Vol2.Ch10Reselect
