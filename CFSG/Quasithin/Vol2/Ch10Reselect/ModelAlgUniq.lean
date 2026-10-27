module

public import CFSG.Quasithin.Vol2.Ch10Reselect.ModelAlgId
public import Mathlib.Algebra.Module.Torsion.Prod
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open Matrix

variable {K : Type*} [Field K] [CharP K 2]

private lemma uniq_phi_smul (g : Matrix.SpecialLinearGroup (Fin 2) K) (σ : RingAut K)
    (B : GL (Fin 2) K) (c : K) (v : UTilde K) :
    phi K g σ B (c • v) = σ c • phi K g σ B v := by
  have hB : bPerm K B (c • v) = c • bPerm K B v := by
    simp only [bPerm_apply, Prod.smul_fst, Prod.smul_snd, Prod.smul_mk, Prod.mk.injEq]
    constructor <;> module
  have hS : ∀ w : UTilde K, sigmaPerm K σ (c • w) = σ c • sigmaPerm K σ w := by
    intro w
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
      simp [sigmaPerm_apply, map_mul]
  have hR : ∀ u : UTilde K, rhoSL K g (σ c • u) = σ c • rhoSL K g u := by
    intro u
    simp only [rhoSL_apply, Prod.smul_fst, Prod.smul_snd, Prod.smul_mk, Matrix.mulVec_smul]
  simp only [phi, Equiv.Perm.mul_apply]
  rw [hB, hS, hR]

private lemma uniq_phi_zero (g : Matrix.SpecialLinearGroup (Fin 2) K) (σ : RingAut K)
    (B : GL (Fin 2) K) : phi K g σ B 0 = 0 := by
  simpa using uniq_phi_smul g σ B 0 0

private lemma uniq_phi_ne_zero (g : Matrix.SpecialLinearGroup (Fin 2) K) (σ : RingAut K)
    (B : GL (Fin 2) K) : phi K g σ B (![1, 0], 0) ≠ 0 := by
  intro h0
  have h1 : phi K g σ B (![1, 0], 0) = phi K g σ B 0 := by
    rw [h0, uniq_phi_zero]
  have h2 := (phi K g σ B).injective h1
  have h3 := congrArg (fun p : UTilde K => p.1 0) h2
  simp at h3

private lemma uniq_bPerm_one : bPerm K (1 : GL (Fin 2) K) = 1 := by
  apply Equiv.ext
  intro v
  simp [bPerm_apply]

private lemma uniq_bPerm_inv (B : GL (Fin 2) K) : bPerm K B⁻¹ = (bPerm K B)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← bPerm_mul, mul_inv_cancel, uniq_bPerm_one]

theorem phi_inj {g g' : Matrix.SpecialLinearGroup (Fin 2) K} {σ σ' : RingAut K}
    {B B' : GL (Fin 2) K} (h : phi K g σ B = phi K g' σ' B') : g = g' ∧ σ = σ' ∧ B = B' := by
  have hσ : σ = σ' := by
    refine RingEquiv.ext fun c => ?_
    have h1 := uniq_phi_smul g σ B c (![1, 0], 0)
    have h2 := uniq_phi_smul g' σ' B' c (![1, 0], 0)
    rw [h] at h1
    exact smul_left_injective K (uniq_phi_ne_zero g' σ' B') (h1.symm.trans h2)
  rw [← hσ] at h
  unfold phi at h
  have hkey : rhoSL K (g'⁻¹ * g) = bPerm K (glMap K σ (B' * B⁻¹)) := by
    have e1 : (rhoSL K g')⁻¹ * rhoSL K g
        = sigmaPerm K σ * bPerm K B' * (bPerm K B)⁻¹ * (sigmaPerm K σ)⁻¹ := by
      calc (rhoSL K g')⁻¹ * rhoSL K g
          = (rhoSL K g')⁻¹ * (rhoSL K g * sigmaPerm K σ * bPerm K B) * (bPerm K B)⁻¹ *
              (sigmaPerm K σ)⁻¹ := by group
        _ = (rhoSL K g')⁻¹ * (rhoSL K g' * sigmaPerm K σ * bPerm K B') * (bPerm K B)⁻¹ *
              (sigmaPerm K σ)⁻¹ := by rw [h]
        _ = sigmaPerm K σ * bPerm K B' * (bPerm K B)⁻¹ * (sigmaPerm K σ)⁻¹ := by group
    have hm : bPerm K (B' * B⁻¹) = bPerm K B' * (bPerm K B)⁻¹ := by
      rw [bPerm_mul, uniq_bPerm_inv]
    have e2 : sigmaPerm K σ * bPerm K B' * (bPerm K B)⁻¹ * (sigmaPerm K σ)⁻¹
        = bPerm K (glMap K σ (B' * B⁻¹)) := by
      calc sigmaPerm K σ * bPerm K B' * (bPerm K B)⁻¹ * (sigmaPerm K σ)⁻¹
          = sigmaPerm K σ * bPerm K (B' * B⁻¹) * (sigmaPerm K σ)⁻¹ := by rw [hm]; group
        _ = bPerm K (glMap K σ (B' * B⁻¹)) * sigmaPerm K σ * (sigmaPerm K σ)⁻¹ := by
              rw [sigmaPerm_bPerm]
        _ = bPerm K (glMap K σ (B' * B⁻¹)) := by group
    rw [map_mul, map_inv, e1, e2]
  obtain ⟨h1, hh1⟩ : ∃ h1 : Matrix.SpecialLinearGroup (Fin 2) K, h1 = g'⁻¹ * g := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : GL (Fin 2) K, C = glMap K σ (B' * B⁻¹) := ⟨_, rfl⟩
  have hk : rhoSL K h1 = bPerm K C := by rw [hh1, hC]; exact hkey
  have hE : ∀ v : UTilde K,
      ((h1 : Matrix (Fin 2) (Fin 2) K) *ᵥ v.1, (h1 : Matrix (Fin 2) (Fin 2) K) *ᵥ v.2) =
        ((C : Matrix (Fin 2) (Fin 2) K) 0 0 • v.1 + (C : Matrix (Fin 2) (Fin 2) K) 0 1 • v.2,
          (C : Matrix (Fin 2) (Fin 2) K) 1 0 • v.1 + (C : Matrix (Fin 2) (Fin 2) K) 1 1 • v.2) := by
    intro v
    rw [← rhoSL_apply, hk, bPerm_apply]
  have a1 : (h1 : Matrix (Fin 2) (Fin 2) K) 0 0 = (C : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    have := congrFun (congrArg Prod.fst (hE (![1, 0], 0))) 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have a2 : (h1 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have := congrFun (congrArg Prod.fst (hE (![1, 0], 0))) 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have a3 : (C : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have := congrFun (congrArg Prod.snd (hE (![1, 0], 0))) 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this.symm
  have a4 : (C : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    have := congrFun (congrArg Prod.fst (hE (0, ![1, 0]))) 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this.symm
  have a5 : (C : Matrix (Fin 2) (Fin 2) K) 1 1 = (C : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    have := congrFun (congrArg Prod.snd (hE (0, ![1, 0]))) 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, a1] using this.symm
  have a6 : (h1 : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    have := congrFun (congrArg Prod.fst (hE (![0, 1], 0))) 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have a7 : (h1 : Matrix (Fin 2) (Fin 2) K) 1 1 = (C : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    have := congrFun (congrArg Prod.fst (hE (![0, 1], 0))) 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hdet := Matrix.SpecialLinearGroup.det_coe h1
  rw [Matrix.det_fin_two, a1, a2, a6, a7] at hdet
  have hc : (C : Matrix (Fin 2) (Fin 2) K) 0 0 * (C : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    linear_combination hdet
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hc1 : (C : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have hsq : ((C : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) * ((C : Matrix (Fin 2) (Fin 2) K) 0 0 - 1)
        = 0 := by
      linear_combination hc + (1 - (C : Matrix (Fin 2) (Fin 2) K) 0 0) * h2
    have := mul_self_eq_zero.mp hsq
    linear_combination this
  have hM1 : (h1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a1, a2, a6, a7, hc1]
  have hSL1 : h1 = 1 := Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_one]; exact hM1)
  have hgg : g'⁻¹ * g = 1 := hh1.symm.trans hSL1
  have hg : g = g' := (inv_mul_eq_one.mp hgg).symm
  have hCM : (C : Matrix (Fin 2) (Fin 2) K) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a3, a4, a5, hc1]
  have hX : ∀ i j, σ (((B' * B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j) =
      (1 : Matrix (Fin 2) (Fin 2) K) i j := by
    intro i j
    have e : (C : Matrix (Fin 2) (Fin 2) K) i j =
        σ (((B' * B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j) := by
      rw [hC]; rfl
    rw [← e, hCM]
  have hMat : ((B' * B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    ext i j
    apply σ.injective
    rw [hX i j]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply, hij]
  have hB1 : B' * B⁻¹ = 1 := Units.ext hMat
  have hBB : B = B' := (mul_inv_eq_one.mp hB1).symm
  exact ⟨hg, hσ, hBB⟩

end CFSG.Quasithin.Vol2.Ch10Reselect
