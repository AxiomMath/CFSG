module

import CFSG.Quasithin.Background.HFCode22Dual
public import CFSG.Quasithin.Background.G11Defs
public import CFSG.Quasithin.Background.SmithB45MatM22

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup CFSG.Quasithin.H.Mathieu CFSG.Quasithin.G11
open CFSG.Quasithin.B45Mat.M22 (G22)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [local instance] CFSG.Quasithin.dualGrpCommGroup

noncomputable section

section Certificates


private theorem w183_mulAutMat_mulVec (f : MulAut W10) (x : Fin 10 → ZMod 2) :
    (CFSG.Quasithin.B45Mat.mulAutMat 10 f).mulVec x =
      Multiplicative.toAdd (f (Multiplicative.ofAdd x)) := by
  change (LinearMap.toMatrix'
      (AddMonoidHom.toZModLinearMap 2
        (AddMonoidHom.toMultiplicative.symm f.toMonoidHom))).mulVec x = _
  rw [LinearMap.toMatrix'_mulVec]
  rfl

private noncomputable def w183Phi2Add (x : Fin 10 → ZMod 2) :
    (Fin 10 → ZMod 2) →+ ZMod 2 where
  toFun y := pair22 (Multiplicative.ofAdd y) (Multiplicative.ofAdd x)
  map_zero' := by rw [ofAdd_zero, pair22_one_left]
  map_add' y z := by rw [ofAdd_add, pair22_mul_left]

private noncomputable def w183Phi2Map :
    (Fin 10 → ZMod 2) →ₗ[ZMod 2] Module.Dual (ZMod 2) (Fin 10 → ZMod 2) :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := fun x => AddMonoidHom.toZModLinearMap 2 (w183Phi2Add x)
      map_zero' := by
        apply LinearMap.ext
        intro y
        show pair22 (Multiplicative.ofAdd y) (Multiplicative.ofAdd 0) = 0
        rw [ofAdd_zero, pair22_one_right]
      map_add' x z := by
        apply LinearMap.ext
        intro y
        show pair22 (Multiplicative.ofAdd y) (Multiplicative.ofAdd (x + z)) =
          pair22 (Multiplicative.ofAdd y) (Multiplicative.ofAdd x) +
            pair22 (Multiplicative.ofAdd y) (Multiplicative.ofAdd z)
        rw [ofAdd_add, pair22_mul_right] }

private theorem w183Phi2Map_apply (x y : Fin 10 → ZMod 2) :
    w183Phi2Map x y = pair22 (Multiplicative.ofAdd y) (Multiplicative.ofAdd x) := rfl

private theorem w183Phi2Map_injective : Function.Injective w183Phi2Map := by
  intro x z h
  have h' : w183Phi2Map (x - z) = 0 := by rw [map_sub, h, sub_self]
  have h1 : dual22Hom (Multiplicative.ofAdd (x - z)) = 1 := by
    apply MonoidHom.ext
    intro (u : W10)
    obtain ⟨y, rfl⟩ := Multiplicative.ofAdd.surjective u
    have h2 : pair22 (Multiplicative.ofAdd y) (Multiplicative.ofAdd (x - z)) = 0 := by
      have := congrArg (fun f : Module.Dual (ZMod 2) (Fin 10 → ZMod 2) => f y) h'
      rwa [w183Phi2Map_apply] at this
    rw [dual22Hom_apply, h2]
    rfl
  have h3 : Multiplicative.ofAdd (x - z) = 1 := by
    apply dual22Hom_injective
    rw [map_one]
    exact h1
  have h4 : x - z = 0 := by
    have := congrArg Multiplicative.toAdd h3
    rw [toAdd_ofAdd, toAdd_one] at this
    exact this
  exact sub_eq_zero.mp h4

private theorem w183Phi2Map_finrank :
    Module.finrank (ZMod 2) (Fin 10 → ZMod 2) =
      Module.finrank (ZMod 2) (Module.Dual (ZMod 2) (Fin 10 → ZMod 2)) :=
  Subspace.dual_finrank_eq.symm

private noncomputable def w183Phi2 :
    (Fin 10 → ZMod 2) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (Fin 10 → ZMod 2) :=
  LinearEquiv.ofInjectiveOfFinrankEq w183Phi2Map w183Phi2Map_injective w183Phi2Map_finrank

private theorem w183Phi2_apply (x : Fin 10 → ZMod 2) :
    w183Phi2 x = w183Phi2Map x := rfl

private theorem w183_sigmaA_apply (g : G22) (y : Fin 10 → ZMod 2) :
    (CFSG.CharacterTheory.SteinbergBY.matrixBaseChange (RingHom.id (ZMod 2))
        CFSG.Quasithin.B45Mat.M22.rep10a) g y =
      Multiplicative.toAdd
        (rho10 mog22 mog22_le_mog22plus (CFSG.Quasithin.B45Mat.M22.psiS22 g)
          (Multiplicative.ofAdd y)) := by
  rw [CFSG.CharacterTheory.SteinbergBY.matrixBaseChange_apply,
    CFSG.Quasithin.B45Mat.M22.rep10a_apply]
  rw [show (⇑(RingHom.id (ZMod 2)) : ZMod 2 → ZMod 2) = id from rfl, Matrix.map_id]
  exact w183_mulAutMat_mulVec _ _

private theorem w183_sigmaB_apply (g : G22) (y : Fin 10 → ZMod 2) :
    (CFSG.CharacterTheory.SteinbergBY.matrixBaseChange (RingHom.id (ZMod 2))
        CFSG.Quasithin.B45Mat.M22.rep10b) g y =
      Multiplicative.toAdd
        (rhoC10 mog22 mog22_le_mog22plus (CFSG.Quasithin.B45Mat.M22.psiS22 g)
          (Multiplicative.ofAdd y)) := by
  rw [CFSG.CharacterTheory.SteinbergBY.matrixBaseChange_apply,
    CFSG.Quasithin.B45Mat.M22.rep10b_apply]
  rw [show (⇑(RingHom.id (ZMod 2)) : ZMod 2 → ZMod 2) = id from rfl, Matrix.map_id]
  exact w183_mulAutMat_mulVec _ _

private theorem w183Phi2_intertwines (g : G22) (y : Fin 10 → ZMod 2) :
    w183Phi2 ((CFSG.CharacterTheory.SteinbergBY.matrixBaseChange (RingHom.id (ZMod 2))
        CFSG.Quasithin.B45Mat.M22.rep10a) g y) =
      (Representation.dual (CFSG.CharacterTheory.SteinbergBY.matrixBaseChange
        (RingHom.id (ZMod 2)) CFSG.Quasithin.B45Mat.M22.rep10b)) g (w183Phi2 y) := by
  apply LinearMap.ext
  intro z
  rw [w183Phi2_apply, w183Phi2_apply, Representation.dual_apply]
  simp only [Module.Dual.transpose_apply, LinearMap.comp_apply]
  rw [w183Phi2Map_apply, w183Phi2Map_apply, w183_sigmaA_apply]
  have hb : ((CFSG.CharacterTheory.SteinbergBY.matrixBaseChange (RingHom.id (ZMod 2))
      CFSG.Quasithin.B45Mat.M22.rep10b) g⁻¹) z =
      Multiplicative.toAdd
        ((rhoC10 mog22 mog22_le_mog22plus (CFSG.Quasithin.B45Mat.M22.psiS22 g))⁻¹
          (Multiplicative.ofAdd z)) := by
    rw [w183_sigmaB_apply, map_inv, map_inv]
  rw [hb]
  have h := pair22_rho mog22 mog22_le_mog22plus (CFSG.Quasithin.B45Mat.M22.psiS22 g)
    ((rhoC10 mog22 mog22_le_mog22plus (CFSG.Quasithin.B45Mat.M22.psiS22 g))⁻¹
      (Multiplicative.ofAdd z)) (Multiplicative.ofAdd y)
  rw [MulAut.apply_inv_self] at h
  simpa using h

private noncomputable def w183StdDual2 :
    (CFSG.CharacterTheory.SteinbergBY.matrixBaseChange (RingHom.id (ZMod 2))
        CFSG.Quasithin.B45Mat.M22.rep10a).Equiv
      (Representation.dual (CFSG.CharacterTheory.SteinbergBY.matrixBaseChange
        (RingHom.id (ZMod 2)) CFSG.Quasithin.B45Mat.M22.rep10b)) :=
  Representation.Equiv.mk w183Phi2 (fun g => by
    apply LinearMap.ext
    intro y
    exact w183Phi2_intertwines g y)

private noncomputable def w183DoubleDual {Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q]
    [Finite Q] (τ : Representation (ZMod 2) G22 Q) : τ.Equiv τ.dual.dual :=
  Representation.Equiv.mk (Module.evalEquiv (ZMod 2) Q) (fun g => by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro f
    simp [Module.evalEquiv_apply, Module.Dual.eval_apply, Representation.dual_apply,
      Module.Dual.transpose_apply, LinearMap.comp_apply])

private noncomputable def w183DualEquiv {Q R : Type} [AddCommGroup Q] [Module (ZMod 2) Q]
    [AddCommGroup R] [Module (ZMod 2) R]
    {τ : Representation (ZMod 2) G22 Q} {σ : Representation (ZMod 2) G22 R}
    (E : τ.Equiv σ) : (σ.dual).Equiv τ.dual :=
  Representation.Equiv.mk E.toLinearEquiv.dualMap (fun g => by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, Representation.dual_apply, Module.Dual.transpose_apply,
      LinearEquiv.dualMap_apply]
    exact (congrArg f
      (Representation.IntertwiningMap.isIntertwining τ σ E.toIntertwiningMap (g⁻¹) x)).symm)

private noncomputable def w183StdDual1 :
    (CFSG.CharacterTheory.SteinbergBY.matrixBaseChange (RingHom.id (ZMod 2))
        CFSG.Quasithin.B45Mat.M22.rep10b).Equiv
      (Representation.dual (CFSG.CharacterTheory.SteinbergBY.matrixBaseChange
        (RingHom.id (ZMod 2)) CFSG.Quasithin.B45Mat.M22.rep10a)) :=
  (w183DoubleDual (CFSG.CharacterTheory.SteinbergBY.matrixBaseChange (RingHom.id (ZMod 2))
    CFSG.Quasithin.B45Mat.M22.rep10b)).trans (w183DualEquiv w183StdDual2)

private theorem w183_not_equiv_rep1 {Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q]
    (τ : Representation (ZMod 2) G22 Q) (n : ∃ g, τ g ≠ 1) :
    ¬ Nonempty (τ.Equiv (CFSG.CharacterTheory.SteinbergBY.matrixBaseChange
      (RingHom.id (ZMod 2)) CFSG.Quasithin.B45Mat.M22.rep1)) := by
  rintro ⟨E⟩
  obtain ⟨g, hg⟩ := n
  apply hg
  ext x
  apply E.injective
  have h := Representation.IntertwiningMap.isIntertwining τ
    (CFSG.CharacterTheory.SteinbergBY.matrixBaseChange (RingHom.id (ZMod 2))
      CFSG.Quasithin.B45Mat.M22.rep1) E.toIntertwiningMap g x
  have htriv : (CFSG.CharacterTheory.SteinbergBY.matrixBaseChange (RingHom.id (ZMod 2))
      CFSG.Quasithin.B45Mat.M22.rep1) g = 1 := by
    apply LinearMap.ext
    intro v
    rw [CFSG.CharacterTheory.SteinbergBY.matrixBaseChange_apply]
    simp [CFSG.Quasithin.B45Mat.M22.rep1]
  rw [htriv] at h
  simpa using h

private theorem w183_isIrreducible_comp {G G' k V : Type} [Group G] [Group G'] [Field k]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (f : G' ≃* G)
    (h : ρ.IsIrreducible) : Representation.IsIrreducible (ρ.comp f.toMonoidHom) :=
  CFSG.Theory.Representation.RepEquiv.irreducible_of_group_iso f.symm (fun g v => by simp) h

private theorem w183_two_irr_std {Q₁ Q₂ : Type} [AddCommGroup Q₁] [Module (ZMod 2) Q₁]
    [Finite Q₁] [AddCommGroup Q₂] [Module (ZMod 2) Q₂] [Finite Q₂]
    (τ₁ : Representation (ZMod 2) G22 Q₁) (τ₂ : Representation (ZMod 2) G22 Q₂)
    (h₁ : τ₁.IsIrreducible) (h₂ : τ₂.IsIrreducible)
    (d₁ : Module.finrank (ZMod 2) Q₁ = 10) (d₂ : Module.finrank (ZMod 2) Q₂ = 10)
    (n₁ : ∃ g, τ₁ g ≠ 1) (n₂ : ∃ g, τ₂ g ≠ 1) :
    Nonempty (τ₂.Equiv τ₁) ∨ Nonempty (τ₂.Equiv τ₁.dual) := by
  haveI : FiniteDimensional (ZMod 2) Q₁ := Module.Finite.of_finite
  haveI : FiniteDimensional (ZMod 2) Q₂ := Module.Finite.of_finite
  have hc₁ := CFSG.Quasithin.B45Mat.M22.m22_binary_cases Q₁ τ₁ h₁ (by rw [d₁]; norm_num)
  have hc₂ := CFSG.Quasithin.B45Mat.M22.m22_binary_cases Q₂ τ₂ h₂ (by rw [d₂]; norm_num)
  rcases hc₁ with h1t | h1a | h1b
  · exact absurd h1t (w183_not_equiv_rep1 τ₁ n₁)
  · rcases hc₂ with h2t | h2a | h2b
    · exact absurd h2t (w183_not_equiv_rep1 τ₂ n₂)
    · obtain ⟨E₁⟩ := h1a
      obtain ⟨E₂⟩ := h2a
      exact Or.inl ⟨E₂.trans E₁.symm⟩
    · obtain ⟨E₁⟩ := h1a
      obtain ⟨E₂⟩ := h2b
      exact Or.inr ⟨E₂.trans (w183StdDual1.trans (w183DualEquiv E₁))⟩
  · rcases hc₂ with h2t | h2a | h2b
    · exact absurd h2t (w183_not_equiv_rep1 τ₂ n₂)
    · obtain ⟨E₁⟩ := h1b
      obtain ⟨E₂⟩ := h2a
      exact Or.inr ⟨E₂.trans (w183StdDual2.trans (w183DualEquiv E₁))⟩
    · obtain ⟨E₁⟩ := h1b
      obtain ⟨E₂⟩ := h2b
      exact Or.inl ⟨E₂.trans E₁.symm⟩

end Certificates

theorem s16nt_m22_two_irr
    {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂]
    (e₁ : Γ₁ ≃* ↥CFSG.Blueprint.NativeSporadic.M22)
    (e₂ : Γ₂ ≃* ↥CFSG.Blueprint.NativeSporadic.M22) {Q₁ Q₂ : Type} [AddCommGroup Q₁]
    [Module (ZMod 2) Q₁] [Finite Q₁] [AddCommGroup Q₂] [Module (ZMod 2) Q₂] [Finite Q₂]
    (ρ₁ : Representation (ZMod 2) Γ₁ Q₁) (ρ₂ : Representation (ZMod 2) Γ₂ Q₂)
    (h₁ : ρ₁.IsIrreducible) (h₂ : ρ₂.IsIrreducible) (d₁ : Module.finrank (ZMod 2) Q₁ = 10)
    (d₂ : Module.finrank (ZMod 2) Q₂ = 10) (n₁ : ∃ g, ρ₁ g ≠ 1) (n₂ : ∃ g, ρ₂ g ≠ 1) :
    ∃ ψ : Γ₂ ≃* Γ₁,
      (∃ L : Q₂ ≃ₗ[ZMod 2] Q₁, ∀ (g : Γ₂) (x : Q₂), L (ρ₂ g x) = ρ₁ (ψ g) (L x)) ∨
      (∃ L : Q₂ ≃ₗ[ZMod 2] Module.Dual (ZMod 2) Q₁,
        ∀ (g : Γ₂) (x : Q₂), L (ρ₂ g x) = Representation.dual ρ₁ (ψ g) (L x)) := by
  let τ₁ : Representation (ZMod 2) G22 Q₁ := ρ₁.comp e₁.symm.toMonoidHom
  let τ₂ : Representation (ZMod 2) G22 Q₂ := ρ₂.comp e₂.symm.toMonoidHom
  have hτ₁ : τ₁.IsIrreducible := w183_isIrreducible_comp ρ₁ e₁.symm h₁
  have hτ₂ : τ₂.IsIrreducible := w183_isIrreducible_comp ρ₂ e₂.symm h₂
  have hn₁ : ∃ g : G22, τ₁ g ≠ 1 := by
    obtain ⟨g, hg⟩ := n₁
    exact ⟨e₁ g, by simpa [τ₁] using hg⟩
  have hn₂ : ∃ g : G22, τ₂ g ≠ 1 := by
    obtain ⟨g, hg⟩ := n₂
    exact ⟨e₂ g, by simpa [τ₂] using hg⟩
  have key := w183_two_irr_std τ₁ τ₂ hτ₁ hτ₂ d₁ d₂ hn₁ hn₂
  refine ⟨e₂.trans e₁.symm, ?_⟩
  rcases key with h | h
  · obtain ⟨E⟩ := h
    left
    refine ⟨E.toLinearEquiv, fun g x => ?_⟩
    change E.toLinearEquiv (ρ₂ g x) = ρ₁ (e₁.symm (e₂ g)) (E.toLinearEquiv x)
    have h := Representation.IntertwiningMap.isIntertwining
      (ρ₂.comp e₂.symm.toMonoidHom) (ρ₁.comp e₁.symm.toMonoidHom) E.toIntertwiningMap
      (e₂ g) x
    rw [Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.toLinearEquiv_apply]
    simp only [MonoidHom.comp_apply] at h
    have he₂ : e₂.symm.toMonoidHom (e₂ g) = g := by simpa using e₂.symm_apply_apply g
    rw [he₂] at h
    exact h
  · obtain ⟨E⟩ := h
    right
    refine ⟨E.toLinearEquiv, fun g x => ?_⟩
    change E.toLinearEquiv (ρ₂ g x) =
      (Representation.dual ρ₁) (e₁.symm (e₂ g)) (E.toLinearEquiv x)
    have h := Representation.IntertwiningMap.isIntertwining
      (ρ₂.comp e₂.symm.toMonoidHom) (Representation.dual (ρ₁.comp e₁.symm.toMonoidHom))
      E.toIntertwiningMap (e₂ g) x
    rw [Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.toLinearEquiv_apply]
    simp only [MonoidHom.comp_apply, Representation.dual_apply, map_inv] at h
    have he₂ : e₂.symm.toMonoidHom (e₂ g) = g := by simpa using e₂.symm_apply_apply g
    rw [he₂] at h
    have he₁ : e₁.symm.toMonoidHom (e₂ g) = e₁.symm (e₂ g) := rfl
    rw [he₁] at h
    simpa only [Representation.dual_apply] using h

end

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
