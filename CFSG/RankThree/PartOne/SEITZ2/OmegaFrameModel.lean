module

public import CFSG.RankThree.PartOne.SEITZ2.OmegaFrame
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataSemilinear

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

section Transport

variable {K V V' : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V']
  [Module K V'] {Q : QuadraticForm K V} {Q' : QuadraticForm K V'} {b c : K}

theorem polar_map_equiv (φ : V' ≃ₗ[K] V) (hφ : ∀ v, Q (φ v) = Q' v) (x y : V') :
    polar Q (φ x) (φ y) = polar Q' x y := by
  unfold QuadraticMap.polar
  rw [← map_add φ, hφ, hφ, hφ]

@[expose] noncomputable def OmegaFrame.map (F : OmegaFrame Q' b c) (φ : V' ≃ₗ[K] V)
    (hφ : ∀ v, Q (φ v) = Q' v) : OmegaFrame Q b c where
  e i := φ (F.e i)
  f i := φ (F.f i)
  t s := φ (F.t s)
  Q_e i := by rw [hφ]; exact F.Q_e i
  Q_f i := by rw [hφ]; exact F.Q_f i
  Q_t₀ := by rw [hφ]; exact F.Q_t₀
  Q_t₁ := by rw [hφ]; exact F.Q_t₁
  polar_ee i j := by rw [polar_map_equiv φ hφ]; exact F.polar_ee i j
  polar_ff i j := by rw [polar_map_equiv φ hφ]; exact F.polar_ff i j
  polar_ef i j := by rw [polar_map_equiv φ hφ]; exact F.polar_ef i j
  polar_et i s := by rw [polar_map_equiv φ hφ]; exact F.polar_et i s
  polar_ft i s := by rw [polar_map_equiv φ hφ]; exact F.polar_ft i s
  polar_t := by rw [polar_map_equiv φ hφ]; exact F.polar_t
  b_ne := F.b_ne
  expand v := by
    have key : ∀ x, polar Q v (φ x) = polar Q' (φ.symm v) x := fun x => by
      rw [← polar_map_equiv φ hφ, LinearEquiv.apply_symm_apply]
    conv_lhs => rw [← φ.apply_symm_apply v, F.expand (φ.symm v)]
    simp only [map_add, map_sum, map_smul, key]

theorem OmegaFrame.map_coef (F : OmegaFrame Q' b c) (φ : V' ≃ₗ[K] V)
    (hφ : ∀ v, Q (φ v) = Q' v) (v : V) (α : Fin 3 ⊕ Fin 3 ⊕ Fin 2) :
    (F.map φ hφ).coef v α = F.coef (φ.symm v) α := by
  have key : ∀ x, polar Q v (φ x) = polar Q' (φ.symm v) x := fun x => by
    rw [← polar_map_equiv φ hφ, LinearEquiv.apply_symm_apply]
  rcases α with i | i | s
  · exact key (F.f i)
  · exact key (F.e i)
  · fin_cases s
    · exact congrArg (b⁻¹ * ·) (key (F.t 1))
    · exact congrArg (b⁻¹ * ·) (key (F.t 0))

theorem OmegaFrame.map_vec (F : OmegaFrame Q' b c) (φ : V' ≃ₗ[K] V)
    (hφ : ∀ v, Q (φ v) = Q' v) (α : Fin 3 ⊕ Fin 3 ⊕ Fin 2) :
    (F.map φ hφ).vec α = φ (F.vec α) := by
  rcases α with i | i | s <;> rfl

end Transport

section Std

variable (F : Type) [Field F] (b c : F)

theorem std_Q_e (i : Fin (4 - 1)) :
    quadMinus 4 F b c (Pi.single (.inl i) 1 : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) = 0 := by
  rw [quadMinus_apply]
  simp [Pi.single_apply]

theorem std_Q_f (i : Fin (4 - 1)) :
    quadMinus 4 F b c
      (Pi.single (.inr (.inl i)) 1 : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) = 0 := by
  rw [quadMinus_apply]
  simp [Pi.single_apply]

theorem std_Q_t₀ :
    quadMinus 4 F b c
      (Pi.single (.inr (.inr 0)) 1 : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) = 1 := by
  rw [quadMinus_apply]
  simp

theorem std_Q_t₁ :
    quadMinus 4 F b c (Pi.single (.inr (.inr 1)) 1 : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) =
      c := by
  rw [quadMinus_apply]
  simp

theorem std_polar_ee (i j : Fin (4 - 1)) :
    polar (quadMinus 4 F b c) (Pi.single (.inl i) 1 : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F)
      (Pi.single (.inl j) 1) = 0 := by
  rw [polar_quadMinus_single_inl]
  simp

theorem std_polar_ff (i j : Fin (4 - 1)) :
    polar (quadMinus 4 F b c) (Pi.single (.inr (.inl i)) 1 :
      Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) (Pi.single (.inr (.inl j)) 1) = 0 := by
  rw [polar_quadMinus_single_inr_inl]
  simp

theorem std_polar_ef (i j : Fin (4 - 1)) :
    polar (quadMinus 4 F b c) (Pi.single (.inl i) 1 : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F)
      (Pi.single (.inr (.inl j)) 1) = if i = j then 1 else 0 := by
  rw [polar_quadMinus_single_inr_inl]
  simp [Pi.single_apply, eq_comm]

theorem std_polar_et (i : Fin (4 - 1)) (s : Fin 2) :
    polar (quadMinus 4 F b c) (Pi.single (.inl i) 1 : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F)
      (Pi.single (.inr (.inr s)) 1) = 0 := by
  revert s
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · rw [polar_quadMinus_single_inr_inr_zero]
    simp
  · rw [polar_quadMinus_single_inr_inr_one]
    simp

theorem std_polar_ft (i : Fin (4 - 1)) (s : Fin 2) :
    polar (quadMinus 4 F b c) (Pi.single (.inr (.inl i)) 1 :
      Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) (Pi.single (.inr (.inr s)) 1) = 0 := by
  revert s
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · rw [polar_quadMinus_single_inr_inr_zero]
    simp
  · rw [polar_quadMinus_single_inr_inr_one]
    simp

theorem std_polar_t :
    polar (quadMinus 4 F b c) (Pi.single (.inr (.inr 0)) 1 :
      Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) (Pi.single (.inr (.inr 1)) 1) = b := by
  rw [polar_quadMinus_single_inr_inr_one]
  simp

theorem std_expand [CharP F 2] (hb : b ≠ 0) (v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) :
    v = ∑ i : Fin (4 - 1), polar (quadMinus 4 F b c) v (Pi.single (.inr (.inl i)) 1) •
        (Pi.single (.inl i) 1 : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) +
      ∑ i : Fin (4 - 1), polar (quadMinus 4 F b c) v (Pi.single (.inl i) 1) •
        (Pi.single (.inr (.inl i)) 1 : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) +
      (b⁻¹ * polar (quadMinus 4 F b c) v (Pi.single (.inr (.inr 1)) 1)) •
        (Pi.single (.inr (.inr 0)) 1 : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) +
      (b⁻¹ * polar (quadMinus 4 F b c) v (Pi.single (.inr (.inr 0)) 1)) •
        (Pi.single (.inr (.inr 1)) 1 : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hbb : b⁻¹ * b = 1 := inv_mul_cancel₀ hb
  have p0 : polar (quadMinus 4 F b c) v (Pi.single (.inr (.inr 0)) 1) =
      b * v (.inr (.inr 1)) := by
    rw [polar_quadMinus_single_inr_inr_zero, h2, zero_mul, zero_add]
  have p1 : polar (quadMinus 4 F b c) v (Pi.single (.inr (.inr 1)) 1) =
      b * v (.inr (.inr 0)) := by
    rw [polar_quadMinus_single_inr_inr_one, h2, zero_mul, zero_mul, add_zero]
  simp only [polar_quadMinus_single_inr_inl, polar_quadMinus_single_inl, p0, p1]
  funext x
  rcases x with j | j | s
  · simp [Pi.single_apply]
  · simp [Pi.single_apply]
  · fin_cases s
    · simp [← mul_assoc, hbb]
    · simp [← mul_assoc, hbb]

@[expose] noncomputable def OmegaFrame.std [CharP F 2] (hb : b ≠ 0) :
    OmegaFrame (quadMinus 4 F b c) b c where
  e i := Pi.single (.inl i) 1
  f i := Pi.single (.inr (.inl i)) 1
  t s := Pi.single (.inr (.inr s)) 1
  Q_e := std_Q_e F b c
  Q_f := std_Q_f F b c
  Q_t₀ := std_Q_t₀ F b c
  Q_t₁ := std_Q_t₁ F b c
  polar_ee := std_polar_ee F b c
  polar_ff := std_polar_ff F b c
  polar_ef := std_polar_ef F b c
  polar_et := std_polar_et F b c
  polar_ft := std_polar_ft F b c
  polar_t := std_polar_t F b c
  b_ne := hb
  expand := std_expand F b c hb

variable [CharP F 2] (hb : b ≠ 0)

theorem OmegaFrame.std_coef (v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F)
    (α : Fin 3 ⊕ Fin 3 ⊕ Fin 2) : (OmegaFrame.std F b c hb).coef v α = v α := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hbb : b⁻¹ * b = 1 := inv_mul_cancel₀ hb
  rcases α with i | i | s
  · exact polar_quadMinus_single_inr_inl 4 F b c v i
  · exact polar_quadMinus_single_inl 4 F b c v i
  · fin_cases s
    · show b⁻¹ * polar (quadMinus 4 F b c) v (Pi.single (.inr (.inr 1)) 1) = _
      rw [polar_quadMinus_single_inr_inr_one, h2, zero_mul, zero_mul, add_zero, ← mul_assoc, hbb,
        one_mul]
      rfl
    · show b⁻¹ * polar (quadMinus 4 F b c) v (Pi.single (.inr (.inr 0)) 1) = _
      rw [polar_quadMinus_single_inr_inr_zero, h2, zero_mul, zero_add, ← mul_assoc, hbb, one_mul]
      rfl

omit [CharP F 2] in
theorem omegaIsometry (v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) :
    coordinateQuadMinus 4 F (by norm_num) b c
      (reindexVectorEquiv (minusIndexEquiv 4 (by norm_num)) v) = quadMinus 4 F b c v :=
  reindexQuadraticForm_map _ _ v

@[expose] noncomputable def omegaFrame :
    OmegaFrame (coordinateQuadMinus 4 F (by norm_num) b c) b c :=
  (OmegaFrame.std F b c hb).map (reindexVectorEquiv (minusIndexEquiv 4 (by norm_num)))
    (omegaIsometry F b c)

theorem omegaFrame_coef (v : Fin (2 * 4) → F) (α : Fin 3 ⊕ Fin 3 ⊕ Fin 2) :
    (omegaFrame F b c hb).coef v α = v (minusIndexEquiv 4 (by norm_num) α) := by
  rw [omegaFrame, OmegaFrame.map_coef, OmegaFrame.std_coef]
  rfl

theorem omegaFrame_vec (α : Fin 3 ⊕ Fin 3 ⊕ Fin 2) :
    (omegaFrame F b c hb).vec α = Pi.single (minusIndexEquiv 4 (by norm_num) α) 1 := by
  rw [omegaFrame, OmegaFrame.map_vec]
  funext j
  have hv : (OmegaFrame.std F b c hb).vec α = Pi.single α 1 := by
    rcases α with i | i | s <;> rfl
  rw [reindexVectorEquiv_apply]
  show (OmegaFrame.std F b c hb).vec α _ = _
  rw [hv, Pi.single_apply, Pi.single_apply]
  simp [Equiv.symm_apply_eq]

end Std

section Rational

variable {K : Type} [Field K] [CharP K 2] (b c : K) (hb : b ≠ 0)

theorem omegaFrame_isRat_iff (k : Subfield K) (v : Fin (2 * 4) → K) :
    (omegaFrame K b c hb).IsRat k v ↔ ∀ j, v j ∈ k := by
  constructor
  · intro h j
    have := h ((minusIndexEquiv 4 (by norm_num)).symm j)
    rwa [omegaFrame_coef, Equiv.apply_symm_apply] at this
  · intro h α
    rw [omegaFrame_coef]
    exact h _

end Rational

end CFSG.RankThree.PartOne.SEITZ2
