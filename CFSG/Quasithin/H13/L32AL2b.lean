module

public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicInversionAlternatingFive

public section

namespace CFSG.Quasithin.H13.L32A.L2

open Equiv

theorem perm_even_inv_five : ∀ s : Perm (Fin 5), s ^ 2 = 1 → s ≠ 1 → Perm.sign s = 1 →
    ∃ x : Perm (Fin 5), Perm.sign x = 1 ∧ x ^ 5 = 1 ∧ x ≠ 1 ∧ s * x * s⁻¹ = x⁻¹ := by
  decide +kernel

theorem perm_odd_inv_three : ∀ s : Perm (Fin 5), s ^ 2 = 1 → Perm.sign s ≠ 1 →
    ∃ x : Perm (Fin 5), Perm.sign x = 1 ∧ x ^ 3 = 1 ∧ x ≠ 1 ∧ s * x * s⁻¹ = x⁻¹ := by
  decide +kernel

theorem perm_odd_inv_conj : ∀ s : Perm (Fin 5), s ^ 2 = 1 → Perm.sign s ≠ 1 →
    ∀ x : Perm (Fin 5), Perm.sign x = 1 → x ^ 3 = 1 → x ≠ 1 →
    ∃ g : Perm (Fin 5), Perm.sign g = 1 ∧ s * (g * x * g⁻¹) * s⁻¹ = (g * x * g⁻¹)⁻¹ := by
  decide +kernel

theorem alt5_involution_cases {X : Type} [Group X] (φ : X ≃* alternatingGroup (Fin 5))
    (σ : MulAut X) (hσ : σ * σ = 1) :
    σ = 1 ∨ (∃ x : X, x ^ 5 = 1 ∧ x ≠ 1 ∧ σ x = x⁻¹) ∨
      ((∃ x : X, x ^ 3 = 1 ∧ x ≠ 1 ∧ σ x = x⁻¹) ∧
        ∀ x : X, x ^ 3 = 1 → x ≠ 1 → ∃ g : X, σ (g * x * g⁻¹) = (g * x * g⁻¹)⁻¹) := by
  set E := CFSG.Semidihedral.Principal.CyclicAlternatingFive.autEquiv with hE
  set α : MulAut (alternatingGroup (Fin 5)) := MulAut.congr φ σ with hα
  set s : Perm (Fin 5) := E.symm α with hs
  have hαs : α = E s := by rw [hs, MulEquiv.apply_symm_apply]
  have hαapp : ∀ a : alternatingGroup (Fin 5), ((α a : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
      s * (a : Perm (Fin 5)) * s⁻¹ := fun a => by
    rw [hαs, hE, CFSG.Semidihedral.Principal.CyclicAlternatingFive.autEquiv_apply]
    rfl
  have hσα : ∀ x : X, σ x = φ.symm (α (φ x)) := fun x => by
    rw [hα, MulAut.congr_apply]
    simp
  have hs2 : s ^ 2 = 1 := by
    have h1 : α * α = 1 := by
      rw [hα, ← map_mul, hσ, map_one]
    have h2 : E (s ^ 2) = 1 := by rw [pow_two, map_mul, ← hαs, h1]
    exact E.injective (h2.trans (map_one E).symm)
  have hinv : ∀ (x : Perm (Fin 5)) (hx : Perm.sign x = 1), s * x * s⁻¹ = x⁻¹ →
      σ (φ.symm ⟨x, Perm.mem_alternatingGroup.mpr hx⟩) =
        (φ.symm ⟨x, Perm.mem_alternatingGroup.mpr hx⟩)⁻¹ := by
    intro x hx hsx
    rw [hσα, MulEquiv.apply_symm_apply, ← map_inv]
    congr 1
    apply Subtype.ext
    rw [hαapp, hsx]
    rfl
  have hpow : ∀ (x : Perm (Fin 5)) (hx : Perm.sign x = 1) (n : ℕ), x ^ n = 1 →
      (φ.symm ⟨x, Perm.mem_alternatingGroup.mpr hx⟩) ^ n = 1 := by
    intro x hx n hn
    rw [← map_pow]
    have : (⟨x, Perm.mem_alternatingGroup.mpr hx⟩ : alternatingGroup (Fin 5)) ^ n = 1 :=
      Subtype.ext (by simpa using hn)
    rw [this, map_one]
  have hne : ∀ (x : Perm (Fin 5)) (hx : Perm.sign x = 1), x ≠ 1 →
      φ.symm ⟨x, Perm.mem_alternatingGroup.mpr hx⟩ ≠ 1 := by
    intro x hx hx1 h
    apply hx1
    have h2 := congrArg φ h
    rw [MulEquiv.apply_symm_apply, map_one] at h2
    exact congrArg Subtype.val h2
  by_cases hs1 : s = 1
  · left
    apply MulEquiv.ext
    intro x
    rw [hσα, MulAut.one_apply]
    have : α (φ x) = φ x := by
      apply Subtype.ext
      rw [hαapp, hs1]
      simp
    rw [this, MulEquiv.symm_apply_apply]
  by_cases hsign : Perm.sign s = 1
  · right; left
    obtain ⟨x, hx, hx5, hx1, hsx⟩ := perm_even_inv_five s hs2 hs1 hsign
    exact ⟨_, hpow x hx 5 hx5, hne x hx hx1, hinv x hx hsx⟩
  · right; right
    refine ⟨?_, fun y hy3 hy1 => ?_⟩
    · obtain ⟨x, hx, hx3, hx1, hsx⟩ := perm_odd_inv_three s hs2 hsign
      exact ⟨_, hpow x hx 3 hx3, hne x hx hx1, hinv x hx hsx⟩
    · set a := φ y with ha
      have ha3 : (a : Perm (Fin 5)) ^ 3 = 1 := by
        have : a ^ 3 = 1 := by rw [ha, ← map_pow, hy3, map_one]
        simpa using congrArg Subtype.val this
      have ha1 : (a : Perm (Fin 5)) ≠ 1 := fun h => hy1 (by
        have : a = 1 := Subtype.ext h
        rw [ha] at this
        exact φ.injective (this.trans (map_one φ).symm))
      obtain ⟨g, hg, hsg⟩ := perm_odd_inv_conj s hs2 hsign a
        (Perm.mem_alternatingGroup.mp a.2) ha3 ha1
      set gb : alternatingGroup (Fin 5) := ⟨g, Perm.mem_alternatingGroup.mpr hg⟩
      refine ⟨φ.symm gb, ?_⟩
      have hga : Perm.sign (g * (a : Perm (Fin 5)) * g⁻¹) = 1 := by
        rw [map_mul, map_mul, map_inv, hg, Perm.mem_alternatingGroup.mp a.2]
        simp
      have hconj : φ.symm gb * y * (φ.symm gb)⁻¹ =
          φ.symm ⟨g * a * g⁻¹, Perm.mem_alternatingGroup.mpr hga⟩ := by
        apply φ.injective
        rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← ha]
        rfl
      rw [hconj]
      exact hinv _ hga hsg

end CFSG.Quasithin.H13.L32A.L2
