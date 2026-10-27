module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration

public section

namespace CFSG.Quasithin.G11.P4GL

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification Matrix

theorem scalars_trivial (n : ℕ) : scalars n (ZMod 2) = ⊥ := by
  refine eq_bot_iff.2 ?_
  rintro A ⟨c, -, hA⟩
  rw [Subgroup.mem_bot]
  have hc : c = 1 := Subsingleton.elim c 1
  ext i j
  rw [hA, hc]
  simp

theorem proj_inj (n : ℕ) : Function.Injective (proj n (ZMod 2)) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_proj, scalars_trivial]

@[expose] noncomputable def slEquiv (n : ℕ) :
    Matrix.SpecialLinearGroup (Fin n) (ZMod 2) ≃* GL (Fin n) (ZMod 2) :=
  MulEquiv.ofBijective
    (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) →* _)
    ⟨Matrix.SpecialLinearGroup.toGL_injective, fun A => by
      have hdet : (A : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := by
        have h1 : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
        have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
        simpa using h2
      refine ⟨⟨(A : Matrix (Fin n) (Fin n) (ZMod 2)), hdet⟩, ?_⟩
      apply Units.ext
      rfl⟩

theorem fieldAut_trivial (n : ℕ) (σ : ZMod 2 ≃+* ZMod 2) : fieldAut n (ZMod 2) σ = 1 := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := proj_surjective n (ZMod 2) x
  rw [fieldAut_proj]
  have hσ : σ.toRingHom = RingHom.id _ := Subsingleton.elim _ _
  have hmap : Matrix.SpecialLinearGroup.map (RingHom.id (ZMod 2)) g = g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rfl
  rw [hσ, hmap]
  rfl

theorem descendAut_inj (n : ℕ) : Function.Injective (descendAut n (ZMod 2)) := by
  intro e e' h
  refine MulEquiv.ext fun g => ?_
  have := congrArg (fun φ : MulAut (projectiveSL n (ZMod 2)) => φ (proj n (ZMod 2) g)) h
  simp only [descendAut_proj] at this
  exact proj_inj n this

theorem aut_SL_cases {n : ℕ} (hn : 3 ≤ n)
    (α : MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) :
    (∃ A : GL (Fin n) (ZMod 2),
        α = CatalogueBHigherLinearAction.slConjugation n (ZMod 2) A) ∨
      (∃ A : GL (Fin n) (ZMod 2),
        α = CatalogueBHigherLinearAction.slConjugation n (ZMod 2) A *
          CatalogueBGraphForm.slGraphAut n (ZMod 2)) := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := ZMod 2) (n := n) hn
  obtain ⟨A, σ, ε, hε, h⟩ := hgen (descendAut n (ZMod 2) α)
  rw [fieldAut_trivial, mul_one] at h
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · left
    rw [pow_zero, mul_one] at h
    exact ⟨A, descendAut_inj n (by rw [h]; rfl)⟩
  · right
    rw [pow_one] at h
    exact ⟨A, descendAut_inj n (by rw [h, map_mul]; rfl)⟩

theorem congr_slConj (n : ℕ) (A : GL (Fin n) (ZMod 2)) :
    MulAut.congr (slEquiv n) (CatalogueBHigherLinearAction.slConjugation n (ZMod 2) A) =
      MulAut.conj A := by
  refine MulEquiv.ext fun h => ?_
  obtain ⟨g, rfl⟩ := (slEquiv n).surjective h
  rw [MulAut.congr_apply, MulAut.conj_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  exact CatalogueBHigherLinearAction.toGL_slConjugation n (ZMod 2) A g

theorem congr_slGraph (n : ℕ) :
    MulAut.congr (slEquiv n) (CatalogueBGraphForm.slGraphAut n (ZMod 2)) =
      CatalogueBGraphForm.glGraphAut n (ZMod 2) := by
  refine MulEquiv.ext fun h => ?_
  obtain ⟨g, rfl⟩ := (slEquiv n).surjective h
  rw [MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  exact CatalogueBGraphForm.toGL_slGraphAut n (ZMod 2) g

theorem aut_GL_cases {n : ℕ} (hn : 3 ≤ n) (α : MulAut (GL (Fin n) (ZMod 2))) :
    (∃ s : GL (Fin n) (ZMod 2), α = MulAut.conj s) ∨
      (∃ s : GL (Fin n) (ZMod 2),
        α = MulAut.conj s * CatalogueBGraphForm.glGraphAut n (ZMod 2)) := by
  have hα : MulAut.congr (slEquiv n) ((MulAut.congr (slEquiv n)).symm α) = α :=
    (MulAut.congr (slEquiv n)).apply_symm_apply α
  rcases aut_SL_cases hn ((MulAut.congr (slEquiv n)).symm α) with ⟨A, hA⟩ | ⟨A, hA⟩
  · left
    refine ⟨A, ?_⟩
    rw [← hα, hA, congr_slConj]
  · right
    refine ⟨A, ?_⟩
    rw [← hα, hA, map_mul, congr_slConj, congr_slGraph]

end CFSG.Quasithin.G11.P4GL
