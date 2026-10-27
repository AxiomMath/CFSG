module

public import CFSG.Quasithin.H13.AS91Sec8V1Defs

public section

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH CFSG.Quasithin.H.Mathieu CFSG.Monster.Code
open scoped Pointwise symmDiff

variable {Γ : Subgroup S24} {hΓ : Γ ≤ AutPerm}

theorem W11_inv (w : W11) : w⁻¹ = w :=
  inv_eq_of_mul_eq_one_right (W11_mul_self w)

theorem IsRightCocycle.map_one {D : ↥Γ → W11} (hD : IsRightCocycle Γ hΓ D) : D 1 = 1 := by
  have h := hD 1 1
  rw [mul_one, _root_.map_one (rho11 Γ hΓ), inv_one, MulAut.one_apply, W11_mul_self] at h
  exact h

theorem IsRightCocycle.map_inv {D : ↥Γ → W11} (hD : IsRightCocycle Γ hΓ D) (s : ↥Γ) :
    D s⁻¹ = rho11 Γ hΓ s (D s) := by
  have h := hD s s⁻¹
  rw [mul_inv_cancel, hD.map_one, _root_.map_inv (rho11 Γ hΓ), inv_inv] at h
  rw [eq_inv_of_mul_eq_one_right h.symm, W11_inv]

theorem IsRightCocycle.mul {D F : ↥Γ → W11} (hD : IsRightCocycle Γ hΓ D)
    (hF : IsRightCocycle Γ hΓ F) : IsRightCocycle Γ hΓ (fun s => D s * F s) := by
  intro s t
  show D (s * t) * F (s * t) = (rho11 Γ hΓ t)⁻¹ (D s * F s) * (D t * F t)
  rw [hD s t, hF s t, map_mul, mul_mul_mul_comm]

theorem isRightCocycle_coboundary (w : W11) : IsRightCocycle Γ hΓ (coboundary Γ hΓ w) := by
  intro s t
  have hst : (rho11 Γ hΓ (s * t))⁻¹ w = (rho11 Γ hΓ t)⁻¹ ((rho11 Γ hΓ s)⁻¹ w) := by
    rw [map_mul, mul_inv_rev, MulAut.mul_apply]
  simp only [coboundary, W11_inv]
  rw [hst, map_mul, mul_assoc, ← mul_assoc ((rho11 Γ hΓ t)⁻¹ w), W11_mul_self, one_mul]

theorem isRightCocycle_char (χ : ↥Γ →* Multiplicative (ZMod 2)) {w : W11}
    (hw : ∀ s, rho11 Γ hΓ s w = w) :
    IsRightCocycle Γ hΓ (fun s => if χ s = 1 then 1 else w) := by
  have hw' : ∀ s, (rho11 Γ hΓ s)⁻¹ w = w := fun s => by
    rw [← map_inv, hw]
  have h2 : ∀ a b : Multiplicative (ZMod 2), a ≠ 1 → b ≠ 1 → a * b = 1 := by decide
  intro s t
  simp only [map_mul]
  by_cases hs : χ s = 1 <;> by_cases ht : χ t = 1
  · simp [hs, ht]
  · simp [hs, ht]
  · simp [hs, ht, hw']
  · simp [hs, ht, h2 _ _ hs ht, hw', W11_mul_self]

theorem eY_symmDiff (S T : Finset (Fin 24)) : eY (S ∆ T) = eY S * eY T := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [toAdd_mul, Pi.add_apply, toAdd_eY, Finset.mem_symmDiff]
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT]
  decide

theorem setClass_symmDiff (S T : Finset (Fin 24)) :
    setClass (S ∆ T) = setClass S * setClass T := by
  rw [setClass, eY_symmDiff, map_mul]
  rfl

theorem even_card_singleton_symmDiff (a b : Fin 24) :
    Even (({a} : Finset (Fin 24)) ∆ {b}).card := by
  by_cases h : a = b
  · subst h
    simp
  · have hab : ({a} : Finset (Fin 24)) ∆ {b} = {a, b} := by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
      constructor
      · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩) <;> simp
      · rintro (rfl | rfl)
        · exact Or.inl ⟨rfl, h⟩
        · exact Or.inr ⟨rfl, Ne.symm h⟩
    rw [hab, Finset.card_pair h]
    decide

theorem isRightCocycle_dBeta : IsRightCocycle Γ hΓ (dBeta Γ) := by
  intro s t
  have hρ : ∀ (u : ↥Γ) (T : Finset (Fin 24)), Even T.card →
      rho11 Γ hΓ u (setClass T) = setClass ((u : S24) • T) := fun u T hT =>
    (setClass_smul (hΓ u.2) hT).symm
  simp only [dBeta]
  rw [← map_inv, hρ _ _ (even_card_singleton_symmDiff _ _), ← setClass_symmDiff]
  congr 1
  rw [Finset.smul_finset_symmDiff, Finset.smul_finset_singleton, Finset.smul_finset_singleton]
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_singleton, Subgroup.coe_mul, Subgroup.coe_inv,
    mul_inv_rev, Equiv.Perm.mul_apply, Equiv.Perm.smul_def]
  tauto

theorem IsRightCocycle.eq_of_eqOn {D F : ↥Γ → W11} (hD : IsRightCocycle Γ hΓ D)
    (hF : IsRightCocycle Γ hΓ F) {T : Set ↥Γ} (hT : Subgroup.closure T = ⊤)
    (h : ∀ s ∈ T, D s = F s) (s : ↥Γ) : D s = F s := by
  let K : Subgroup ↥Γ :=
    { carrier := {s | D s = F s}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [hD, hF, ha, hb]
      one_mem' := by
        simp only [Set.mem_setOf_eq]
        rw [hD.map_one, hF.map_one]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [hD.map_inv, hF.map_inv, ha] }
  have hle : Subgroup.closure T ≤ K := (Subgroup.closure_le K).2 h
  rw [hT] at hle
  exact hle (Subgroup.mem_top s)

end CFSG.Quasithin.H13.AS91.M24G
