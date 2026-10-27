module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtCover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.JonesParshall Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

private noncomputable def w183Fun {Γ : Type} {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    (Φ : N ≃ₗ[ZMod 2] Module.Dual (ZMod 2) N) :
    (Γ → N) ≃ₗ[ZMod 2] (Γ → Module.Dual (ZMod 2) N) :=
  LinearEquiv.piCongrRight fun _ => Φ

private lemma w183_dual_heq {Γ : Type} [Group Γ] {N : Type} [AddCommGroup N]
    [Module (ZMod 2) N] (ρ : Representation (ZMod 2) Γ N)
    (Φ : N ≃ₗ[ZMod 2] Module.Dual (ZMod 2) N) (β : LinearMap.BilinForm (ZMod 2) N)
    (hΦ : ∀ x y : N, Φ x y = β y x)
    (hinv : ∀ (g : Γ) (x y : N), β (ρ g x) (ρ g y) = β x y) :
    ∀ (g : Γ) (x : N), (Representation.dual ρ) g (Φ x) = Φ (ρ g x) := by
  intro g x
  refine LinearMap.ext fun y => ?_
  rw [Representation.dual_apply]
  show Φ x (ρ g⁻¹ y) = Φ (ρ g x) y
  rw [hΦ, hΦ]
  have h := hinv g (ρ g⁻¹ y) x
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] at h
  exact h.symm

private lemma w183_z1_map {Γ : Type} [Group Γ] {N : Type} [AddCommGroup N]
    [Module (ZMod 2) N] (ρ : Representation (ZMod 2) Γ N)
    (Φ : N ≃ₗ[ZMod 2] Module.Dual (ZMod 2) N)
    (heq : ∀ (g : Γ) (x : N), (Representation.dual ρ) g (Φ x) = Φ (ρ g x)) :
    ∀ f : Γ → N, f ∈ Z1 ρ ↔ w183Fun (Γ := Γ) Φ f ∈ Z1 (Representation.dual ρ) := by
  intro f
  change (∀ g h, f (g * h) = f g + ρ g (f h)) ↔
    (∀ g h, w183Fun (Γ := Γ) Φ f (g * h) =
      w183Fun (Γ := Γ) Φ f g + (Representation.dual ρ) g (w183Fun (Γ := Γ) Φ f h))
  constructor
  · intro hf g h
    simp only [w183Fun, LinearEquiv.piCongrRight_apply]
    rw [hf g h, Φ.map_add, ← heq g (f h)]
  · intro hf g h
    have hc := hf g h
    simp only [w183Fun, LinearEquiv.piCongrRight_apply] at hc
    rw [heq g (f h), ← Φ.map_add] at hc
    exact Φ.injective hc

private lemma w183_b1_map {Γ : Type} [Group Γ] {N : Type} [AddCommGroup N]
    [Module (ZMod 2) N] (ρ : Representation (ZMod 2) Γ N)
    (Φ : N ≃ₗ[ZMod 2] Module.Dual (ZMod 2) N)
    (heq : ∀ (g : Γ) (x : N), (Representation.dual ρ) g (Φ x) = Φ (ρ g x)) :
    ∀ f : Γ → N, f ∈ B1 ρ ↔ w183Fun (Γ := Γ) Φ f ∈ B1 (Representation.dual ρ) := by
  intro f
  simp only [B1, LinearMap.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨Φ v, ?_⟩
    funext g
    simp only [coboundary, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, w183Fun,
      LinearEquiv.piCongrRight_apply]
    rw [heq g v]
    exact (Φ.map_sub (ρ g v) v).symm
  · rintro ⟨w, hw⟩
    refine ⟨Φ.symm w, funext fun g => ?_⟩
    have h := congrFun hw g
    simp only [coboundary, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, w183Fun,
      LinearEquiv.piCongrRight_apply] at h
    have h2 : Φ ((ρ g) (Φ.symm w) - Φ.symm w) = (ρ.dual g) w - w :=
      (Φ.map_sub (ρ g (Φ.symm w)) (Φ.symm w)).trans <| by
        change Φ (ρ g (Φ.symm w)) - Φ (Φ.symm w) = (ρ.dual g) w - w
        rw [← heq g (Φ.symm w)]
        simp only [LinearEquiv.apply_symm_apply]
    simpa only [coboundary, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply] using
      Φ.injective (h2.trans h)

private lemma w183_z1_map_eq {Γ : Type} [Group Γ] {N : Type} [AddCommGroup N]
    [Module (ZMod 2) N] (ρ : Representation (ZMod 2) Γ N)
    (Φ : N ≃ₗ[ZMod 2] Module.Dual (ZMod 2) N)
    (heq : ∀ (g : Γ) (x : N), (Representation.dual ρ) g (Φ x) = Φ (ρ g x)) :
    (Z1 ρ).map (w183Fun (Γ := Γ) Φ : (Γ → N) →ₗ[ZMod 2]
      (Γ → Module.Dual (ZMod 2) N)) = Z1 (Representation.dual ρ) := by
  apply le_antisymm
  · rintro f ⟨y, hy, rfl⟩
    exact (w183_z1_map ρ Φ heq y).mp hy
  · intro f hf
    refine ⟨(w183Fun (Γ := Γ) Φ).symm f, ?_, by simp⟩
    exact (w183_z1_map ρ Φ heq _).mpr (by simpa using hf)

private noncomputable def w183_z1_equiv {Γ : Type} [Group Γ] {N : Type} [AddCommGroup N]
    [Module (ZMod 2) N] (ρ : Representation (ZMod 2) Γ N)
    (Φ : N ≃ₗ[ZMod 2] Module.Dual (ZMod 2) N)
    (heq : ∀ (g : Γ) (x : N), (Representation.dual ρ) g (Φ x) = Φ (ρ g x)) :
    ↥(Z1 ρ) ≃ₗ[ZMod 2] ↥(Z1 (Representation.dual ρ)) :=
  (w183Fun (Γ := Γ) Φ).ofSubmodules (Z1 ρ) (Z1 (Representation.dual ρ))
    (w183_z1_map_eq ρ Φ heq)

private lemma w183_z1_equiv_coe {Γ : Type} [Group Γ] {N : Type} [AddCommGroup N]
    [Module (ZMod 2) N] (ρ : Representation (ZMod 2) Γ N)
    (Φ : N ≃ₗ[ZMod 2] Module.Dual (ZMod 2) N)
    (heq : ∀ (g : Γ) (x : N), (Representation.dual ρ) g (Φ x) = Φ (ρ g x))
    (f : ↥(Z1 ρ)) :
    ((w183_z1_equiv ρ Φ heq f : ↥(Z1 (Representation.dual ρ))) :
        Γ → Module.Dual (ZMod 2) N) = w183Fun (Γ := Γ) Φ (f : Γ → N) := by
  simp only [w183_z1_equiv, LinearEquiv.ofSubmodules_apply]

private noncomputable def w183_h1_dual_equiv {Γ : Type} [Group Γ] {N : Type} [AddCommGroup N]
    [Module (ZMod 2) N] (ρ : Representation (ZMod 2) Γ N)
    (Φ : N ≃ₗ[ZMod 2] Module.Dual (ZMod 2) N)
    (heq : ∀ (g : Γ) (x : N), (Representation.dual ρ) g (Φ x) = Φ (ρ g x)) :
    H1 (Representation.dual ρ) ≃ₗ[ZMod 2] H1 ρ := by
  have hB := w183_b1_map ρ Φ heq
  let eZ : ↥(Z1 ρ) ≃ₗ[ZMod 2] ↥(Z1 (Representation.dual ρ)) := w183_z1_equiv ρ Φ heq
  let P : Submodule (ZMod 2) ↥(Z1 ρ) := (B1 ρ).comap (Z1 ρ).subtype
  let Q : Submodule (ZMod 2) ↥(Z1 (Representation.dual ρ)) :=
    (B1 (Representation.dual ρ)).comap (Z1 (Representation.dual ρ)).subtype
  have hf : P.map (eZ : ↥(Z1 ρ) →ₗ[ZMod 2] ↥(Z1 (Representation.dual ρ))) = Q := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      change ((eZ y : ↥(Z1 (Representation.dual ρ))) : Γ → Module.Dual (ZMod 2) N) ∈
        B1 (Representation.dual ρ)
      rw [w183_z1_equiv_coe ρ Φ heq y]
      exact (hB (y : Γ → N)).mp hy
    · intro x hx
      refine ⟨eZ.symm x, ?_, eZ.apply_symm_apply x⟩
      refine (hB ((eZ.symm x : ↥(Z1 ρ)) : Γ → N)).mpr ?_
      have hcoe : w183Fun (Γ := Γ) Φ ((eZ.symm x : ↥(Z1 ρ)) : Γ → N) =
          (x : Γ → Module.Dual (ZMod 2) N) := by
        rw [← w183_z1_equiv_coe ρ Φ heq (eZ.symm x), eZ.apply_symm_apply x]
      rw [hcoe]
      exact hx
  exact (Submodule.Quotient.equiv _ _ eZ hf).symm

theorem s16nt_h1_dual_of_invariant_form {Γ : Type} [Group Γ] {N : Type} [AddCommGroup N]
    [Module (ZMod 2) N] [Finite N] (ρ : Representation (ZMod 2) Γ N)
    (β : LinearMap.BilinForm (ZMod 2) N) (hβ : β.Nondegenerate)
    (hinv : ∀ (g : Γ) (x y : N), β (ρ g x) (ρ g y) = β x y) :
    Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1 (Representation.dual ρ)) =
      Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1 ρ) := by
  classical
  haveI : FiniteDimensional (ZMod 2) N := Module.Finite.of_finite
  let Φ : N ≃ₗ[ZMod 2] Module.Dual (ZMod 2) N := β.flip.toDual hβ.flip
  have hΦ : ∀ x y : N, Φ x y = β y x := fun x y => LinearMap.BilinForm.toDual_def hβ.flip
  have heq := w183_dual_heq ρ Φ β hΦ hinv
  exact (w183_h1_dual_equiv ρ Φ heq).finrank_eq

theorem s16nt_h1_dual_natRep {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] [Algebra (ZMod 2) K] (Γ : Subgroup (Matrix.GeneralLinearGroup ι K))
    (β : LinearMap.BilinForm (ZMod 2) (ι → K)) (hβ : β.Nondegenerate)
    (hinv : ∀ g ∈ Γ, ∀ x y : ι → K,
      β (((g : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec x)
        (((g : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec y) = β x y) :
    Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1
      (Representation.dual (s16ntNatRep Γ))) =
      Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1 (s16ntNatRep Γ)) :=
  s16nt_h1_dual_of_invariant_form (s16ntNatRep Γ) β hβ fun g x y => hinv g g.2 x y

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
