module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev DVec (m : ℕ) : Type := Fin m → ZMod 3

noncomputable abbrev dBasis (m : ℕ) : Module.Basis (Fin m) (ZMod 3) (DVec m) :=
  Pi.basisFun (ZMod 3) (Fin m)

@[expose] noncomputable def dPerm (m : ℕ) (σ : Equiv.Perm (Fin m)) : DVec m ≃ₗ[ZMod 3] DVec m :=
  ZS.permMap 3 (dBasis m) σ

@[expose] noncomputable def dSign (m : ℕ) (a b : Fin m) : DVec m ≃ₗ[ZMod 3] DVec m :=
  ZS.diagMap 3 (dBasis m) (fun k => if k = a ∨ k = b then -1 else 1)

@[expose] noncomputable def dTau (m : ℕ) (ε : Bool) (a b : Fin m) : DVec m ≃ₗ[ZMod 3] DVec m :=
  dPerm m (Equiv.swap a b) * (if ε then dSign m a b else 1)

private lemma plh_dTau_false (m : ℕ) (a b : Fin m) :
    dTau m false a b = dPerm m (Equiv.swap a b) := by
  simp [dTau]

private lemma plh_dTau_true (m : ℕ) (a b : Fin m) :
    dTau m true a b = dPerm m (Equiv.swap a b) * dSign m a b := by
  simp [dTau]

theorem dPerm_apply (m : ℕ) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    dPerm m σ (dBasis m i) = dBasis m (σ i) := by
  rw [dPerm, ZS.permMap_apply_basis]

theorem dPerm_mul (m : ℕ) (σ τ : Equiv.Perm (Fin m)) :
    dPerm m (σ * τ) = dPerm m σ * dPerm m τ := by
  simp only [dPerm]
  rw [ZS.permMap_mul]

theorem dPerm_one (m : ℕ) : dPerm m 1 = 1 := by
  refine (dBasis m).ext' fun i => ?_
  rw [dPerm_apply]
  simp

private lemma plh_dPerm_inv (m : ℕ) (ρ : Equiv.Perm (Fin m)) :
    (dPerm m ρ)⁻¹ = dPerm m ρ⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← dPerm_mul, mul_inv_cancel, dPerm_one]

theorem dSign_apply (m : ℕ) (a b i : Fin m) :
    dSign m a b (dBasis m i) =
      (if i = a ∨ i = b then (-1 : ZMod 3) else 1) • dBasis m i := by
  rw [dSign, ZS.diagMap_apply_basis]
  by_cases h : i = a ∨ i = b <;> simp [h, Units.val_neg]

theorem dTau_apply_left (m : ℕ) (ε : Bool) {a b : Fin m} (hab : a ≠ b) :
    dTau m ε a b (dBasis m a) = (if ε then (-1 : ZMod 3) else 1) • dBasis m b := by
  cases ε
  · rw [plh_dTau_false, dPerm_apply, Equiv.swap_apply_left]
    simp
  · rw [plh_dTau_true, LinearEquiv.mul_apply, dSign_apply, map_smul, dPerm_apply,
      Equiv.swap_apply_left]
    simp

theorem dTau_apply_right (m : ℕ) (ε : Bool) {a b : Fin m} (hab : a ≠ b) :
    dTau m ε a b (dBasis m b) = (if ε then (-1 : ZMod 3) else 1) • dBasis m a := by
  cases ε
  · rw [plh_dTau_false, dPerm_apply, Equiv.swap_apply_right]
    simp
  · rw [plh_dTau_true, LinearEquiv.mul_apply, dSign_apply, map_smul, dPerm_apply,
      Equiv.swap_apply_right]
    simp [hab, hab.symm]

theorem dTau_apply_of_ne (m : ℕ) (ε : Bool) {a b i : Fin m} (hia : i ≠ a) (hib : i ≠ b) :
    dTau m ε a b (dBasis m i) = dBasis m i := by
  cases ε
  · rw [plh_dTau_false, dPerm_apply, Equiv.swap_apply_of_ne_of_ne hia hib]
  · rw [plh_dTau_true, LinearEquiv.mul_apply, dSign_apply, map_smul, dPerm_apply,
      Equiv.swap_apply_of_ne_of_ne hia hib]
    simp [hia, hib]

theorem dTau_symm (m : ℕ) (ε : Bool) (a b : Fin m) : dTau m ε a b = dTau m ε b a := by
  by_cases hab : a = b
  · subst hab
    rfl
  · refine (dBasis m).ext' fun i => ?_
    by_cases hia : i = a
    · subst hia
      rw [dTau_apply_left m ε hab, dTau_apply_right m ε (Ne.symm hab)]
    · by_cases hib : i = b
      · subst hib
        rw [dTau_apply_right m ε hab, dTau_apply_left m ε (Ne.symm hab)]
      · rw [dTau_apply_of_ne m ε hia hib, dTau_apply_of_ne m ε hib hia]

private lemma plh_sign_comp (m : ℕ) (ρ : Equiv.Perm (Fin m)) (a b : Fin m) :
    (fun k => if k = a ∨ k = b then (-1 : (ZMod 3)ˣ) else 1) ∘ ρ.symm =
      fun k => if k = ρ a ∨ k = ρ b then (-1 : (ZMod 3)ˣ) else 1 := by
  funext k
  have hiff : ρ.symm k = a ∨ ρ.symm k = b ↔ k = ρ a ∨ k = ρ b := by
    constructor
    · rintro (h | h)
      · exact Or.inl ((Equiv.apply_symm_apply ρ k).symm.trans (congrArg ρ h))
      · exact Or.inr ((Equiv.apply_symm_apply ρ k).symm.trans (congrArg ρ h))
    · rintro (h | h)
      · exact Or.inl ((congrArg ρ.symm h).trans (Equiv.symm_apply_apply ρ a))
      · exact Or.inr ((congrArg ρ.symm h).trans (Equiv.symm_apply_apply ρ b))
  simp only [Function.comp_apply]
  by_cases h : ρ.symm k = a ∨ ρ.symm k = b
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun hh => h (hiff.mpr hh))]

private lemma plh_conj_mul {G : Type*} [Group G] (A B C : G) :
    A * B * A⁻¹ * (A * C * A⁻¹) = A * (B * C) * A⁻¹ := by
  rw [mul_assoc (A * B) A⁻¹ ((A * C) * A⁻¹), ← mul_assoc A⁻¹ (A * C) A⁻¹,
    ← mul_assoc A⁻¹ A C, inv_mul_cancel, one_mul, mul_assoc A B (C * A⁻¹),
    ← mul_assoc B C A⁻¹, mul_assoc A (B * C) A⁻¹]

private lemma plh_dPerm_conj_swap (m : ℕ) (ρ : Equiv.Perm (Fin m)) (a b : Fin m) :
    dPerm m ρ * dPerm m (Equiv.swap a b) * (dPerm m ρ)⁻¹ =
      dPerm m (Equiv.swap (ρ a) (ρ b)) := by
  rw [plh_dPerm_inv, ← dPerm_mul, ← dPerm_mul, ← Equiv.swap_apply_apply ρ a b]

private lemma plh_dSign_conj (m : ℕ) (ρ : Equiv.Perm (Fin m)) (a b : Fin m) :
    dPerm m ρ * dSign m a b * (dPerm m ρ)⁻¹ = dSign m (ρ a) (ρ b) := by
  rw [dPerm, dSign, dSign, ZS.permMap_mul_diagMap_mul_inv]
  exact congrArg (fun d => ZS.diagMap 3 (dBasis m) d) (plh_sign_comp m ρ a b)

theorem dPerm_conj_dTau (m : ℕ) (ρ : Equiv.Perm (Fin m)) (ε : Bool) (a b : Fin m) :
    dPerm m ρ * dTau m ε a b * (dPerm m ρ)⁻¹ = dTau m ε (ρ a) (ρ b) := by
  cases ε
  · simp only [plh_dTau_false]
    rw [plh_dPerm_conj_swap]
  · simp only [plh_dTau_true]
    rw [← plh_conj_mul, plh_dPerm_conj_swap, plh_dSign_conj]

end CFSG.StandardType.QTwo

end
