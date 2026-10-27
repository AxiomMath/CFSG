module

public import CFSG.Quasithin.Background.P3OrthoOm4

public section

namespace CFSG.RankThree.GF2n.Stroth80.SL2Coord

open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open CFSG.Quasithin.G11.P3Ortho.Om4
open TauCeti.QuadraticMap
open scoped commutatorElement

variable {K : Type} [Field K]

@[expose] def conjEquiv {E M : Type} [AddCommGroup E] [Module K E] [AddCommGroup M] [Module K M]
    (psi : E ≃ₗ[K] M) : (E ≃ₗ[K] E) ≃* (M ≃ₗ[K] M) where
  toFun g := psi.symm.trans (g.trans psi)
  invFun h := psi.trans (h.trans psi.symm)
  left_inv g := by
    ext x
    simp
  right_inv h := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp

theorem conjEquiv_apply {E M : Type} [AddCommGroup E] [Module K E] [AddCommGroup M] [Module K M]
    (psi : E ≃ₗ[K] M) (g : E ≃ₗ[K] E) (x : M) :
    conjEquiv psi g x = psi (g (psi.symm x)) := rfl

section Omega

variable [Finite K] [CharP K 2] {E : Type} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

theorem exists_omega_equiv (f : QuadraticForm K E) (hnd : f.polarBilin.Nondegenerate)
    (hdim : Module.finrank K E = 4) (S : Submodule K E) (hS2 : Module.finrank K S = 2)
    (hS : ∀ x ∈ S, f x = 0) (h4 : 4 ≤ Nat.card K) :
    ∃ ρ : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →*
        (E ≃ₗ[K] E),
      Function.Injective ρ ∧ ρ.range = ⁅orthogonalGroup f, orthogonalGroup f⁆ ∧
        ρ.range ≤ orthogonalGroup f ∧
        ∃ t₀ ∈ orthogonalGroup f, ∀ T ∈ orthogonalGroup f, T ∈ ρ.range ∨ T * t₀ ∈ ρ.range := by
  obtain ⟨psi, e, hpsi, he1, he2⟩ := split_four_determinant_form_isometry f hnd hdim S hS2 hS
  let ρ : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →*
      (E ≃ₗ[K] E) :=
    (orthogonalGroup f).subtype.comp (e.symm.toMonoidHom.comp specialRho)
  have hinj : Function.Injective ρ :=
    Subtype.val_injective.comp (e.symm.injective.comp specialRho_injective)
  have hC : ∀ g : E ≃ₗ[K] E, g ∈ orthogonalGroup f ↔
      conjEquiv psi g ∈ orthogonalGroup (determinantForm K) := by
    intro g
    rw [mem_orthogonalGroup_iff, mem_orthogonalGroup_iff]
    constructor
    · intro h X
      rw [determinantForm_apply, determinantForm_apply]
      have h1 := h (psi.symm X)
      rw [hpsi, hpsi] at h1
      simpa [conjEquiv_apply] using h1
    · intro h v
      have h1 := h (psi v)
      rw [determinantForm_apply, determinantForm_apply] at h1
      rw [hpsi, hpsi]
      simpa [conjEquiv_apply] using h1
  have hCO : (orthogonalGroup f).map (conjEquiv psi).toMonoidHom =
      orthogonalGroup (determinantForm K) := by
    ext h
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (hC g).mp hg
    · intro hh
      refine ⟨(conjEquiv psi).symm h, ?_, by simp⟩
      exact (hC _).mpr (by simpa using hh)
  have hCρ : ∀ z, conjEquiv psi (ρ z) = rho' K z := by
    intro z
    refine LinearEquiv.ext fun X => ?_
    show psi ((e.symm (specialRho z)).val (psi.symm X)) = (rho' K z) X
    rw [he2]
    simp [rho']
  refine ⟨ρ, hinj, ?_, ?_, (e.symm tau).val, (e.symm tau).2, ?_⟩
  · apply Subgroup.map_injective (f := (conjEquiv psi).toMonoidHom) (conjEquiv psi).injective
    have h1 : ρ.range.map (conjEquiv psi).toMonoidHom = (rho' K).range := by
      ext h
      constructor
      · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
        exact ⟨z, (hCρ z).symm⟩
      · rintro ⟨z, rfl⟩
        exact ⟨ρ z, ⟨z, rfl⟩, hCρ z⟩
    rw [h1, ← commutator_eq_range h4, Subgroup.map_commutator, hCO]
  · rintro _ ⟨z, rfl⟩
    exact (e.symm (specialRho z)).2
  · intro T hT
    rcases mem_specialImage_or_mul_tau (e ⟨T, hT⟩) with ⟨z, hz⟩ | ⟨z, hz⟩
    · left
      refine ⟨z, ?_⟩
      have h1 := congrArg (fun y => (e.symm y).val) hz
      simpa [ρ] using h1
    · right
      refine ⟨z, ?_⟩
      have h1 := congrArg (fun y => (e.symm y).val) hz
      simpa [ρ] using h1

end Omega

section SemiConj

variable {E : Type} [AddCommGroup E] [Module K E]

theorem semi_symm_smul (σ : K ≃+* K) (T : E ≃+ E) (hT : ∀ (c : K) e, T (c • e) = σ c • T e)
    (c : K) (e : E) : T.symm (c • e) = σ.symm c • T.symm e := by
  apply T.injective
  rw [AddEquiv.apply_symm_apply, hT, RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

@[expose] def semiConjFun (σ : K ≃+* K) (T : E ≃+ E) (hT : ∀ (c : K) e, T (c • e) = σ c • T e)
    (g : E ≃ₗ[K] E) : E ≃ₗ[K] E where
  toFun e := T (g (T.symm e))
  invFun e := T (g.symm (T.symm e))
  map_add' x y := by simp [map_add]
  map_smul' c x := by
    simp only [RingHom.id_apply]
    rw [semi_symm_smul σ T hT, map_smul, hT, RingEquiv.apply_symm_apply]
  left_inv x := by simp
  right_inv x := by simp

theorem semiConjFun_apply (σ : K ≃+* K) (T : E ≃+ E) (hT : ∀ (c : K) e, T (c • e) = σ c • T e)
    (g : E ≃ₗ[K] E) (x : E) : semiConjFun σ T hT g x = T (g (T.symm x)) := rfl

@[expose] def semiConj (σ : K ≃+* K) (T : E ≃+ E) (hT : ∀ (c : K) e, T (c • e) = σ c • T e) :
    (E ≃ₗ[K] E) ≃* (E ≃ₗ[K] E) where
  toFun := semiConjFun σ T hT
  invFun := semiConjFun σ.symm T.symm (semi_symm_smul σ T hT)
  left_inv g := by
    refine LinearEquiv.ext fun x => ?_
    simp [semiConjFun_apply]
  right_inv g := by
    refine LinearEquiv.ext fun x => ?_
    simp [semiConjFun_apply]
  map_mul' g h := by
    refine LinearEquiv.ext fun x => ?_
    simp [semiConjFun_apply]

theorem semiConj_apply (σ : K ≃+* K) (T : E ≃+ E) (hT : ∀ (c : K) e, T (c • e) = σ c • T e)
    (g : E ≃ₗ[K] E) (x : E) : semiConj σ T hT g x = T (g (T.symm x)) := rfl

theorem semiConj_mem_orthogonalGroup_iff (σ : K ≃+* K) (T : E ≃+ E)
    (hT : ∀ (c : K) e, T (c • e) = σ c • T e) (f : QuadraticForm K E) (a : K) (ha : a ≠ 0)
    (hf : ∀ e, f (T e) = a * σ (f e)) (g : E ≃ₗ[K] E) :
    semiConj σ T hT g ∈ orthogonalGroup f ↔ g ∈ orthogonalGroup f := by
  rw [mem_orthogonalGroup_iff, mem_orthogonalGroup_iff]
  constructor
  · intro h y
    have h1 := h (T y)
    rw [semiConj_apply, AddEquiv.symm_apply_apply, hf, hf] at h1
    have h2 := mul_left_cancel₀ ha h1
    exact σ.injective h2
  · intro h x
    rw [semiConj_apply, hf, h, ← hf, AddEquiv.apply_symm_apply]

theorem map_semiConj_commutator (σ : K ≃+* K) (T : E ≃+ E)
    (hT : ∀ (c : K) e, T (c • e) = σ c • T e) (f : QuadraticForm K E) (a : K) (ha : a ≠ 0)
    (hf : ∀ e, f (T e) = a * σ (f e)) :
    ⁅orthogonalGroup f, orthogonalGroup f⁆.map (semiConj σ T hT).toMonoidHom =
      ⁅orthogonalGroup f, orthogonalGroup f⁆ := by
  have hO : (orthogonalGroup f).map (semiConj σ T hT).toMonoidHom = orthogonalGroup f := by
    ext h
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (semiConj_mem_orthogonalGroup_iff σ T hT f a ha hf g).mpr hg
    · intro hh
      refine ⟨(semiConj σ T hT).symm h, ?_, by simp⟩
      exact (semiConj_mem_orthogonalGroup_iff σ T hT f a ha hf _).mp (by simpa using hh)
  rw [Subgroup.map_commutator, hO]

end SemiConj

end CFSG.RankThree.GF2n.Stroth80.SL2Coord
