module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxSL2

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Matrix
open CFSG.RankThree.PartOne.CTP (u2 l2 u2_coe l2_coe)

section Plane

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  (P P' : HypPair Q)

theorem polar_facts (h : P.Orth P') :
    polar Q P.e P.e = 0 ∧ polar Q P.e P'.e = 0 ∧ polar Q P.e P.f = 1 ∧ polar Q P.e P'.f = 0 ∧
    polar Q P.f P.e = 1 ∧ polar Q P.f P.f = 0 ∧ polar Q P.f P'.e = 0 ∧ polar Q P.f P'.f = 0 ∧
    polar Q P'.e P.e = 0 ∧ polar Q P'.e P.f = 0 ∧ polar Q P'.e P'.e = 0 ∧ polar Q P'.e P'.f = 1 ∧
    polar Q P'.f P.e = 0 ∧ polar Q P'.f P.f = 0 ∧ polar Q P'.f P'.e = 1 ∧ polar Q P'.f P'.f = 0 :=
  ⟨P.polar_ee, h.ee, P.polar_ef, h.ef, P.polar_fe, P.polar_ff, h.fe, h.ff, h.symm.ee, h.symm.ef,
    P'.polar_ee, P'.polar_ef, h.symm.fe, h.symm.ff, P'.polar_fe, P'.polar_ff⟩

variable (g : SpecialLinearGroup (Fin 2) K)

@[expose] def planeA₁ (v : V) : K :=
  ((g : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) * polar Q v P.f +
    (g : Matrix (Fin 2) (Fin 2) K) 0 1 * polar Q v P'.e

@[expose] def planeA₂ (v : V) : K :=
  ((g : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) * polar Q v P'.f +
    (g : Matrix (Fin 2) (Fin 2) K) 0 1 * polar Q v P.e

@[expose] def planeC₁ (v : V) : K :=
  (g : Matrix (Fin 2) (Fin 2) K) 1 0 * polar Q v P'.f +
    ((g : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) * polar Q v P.e

@[expose] def planeC₂ (v : V) : K :=
  (g : Matrix (Fin 2) (Fin 2) K) 1 0 * polar Q v P.f +
    ((g : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) * polar Q v P'.e

@[expose] noncomputable def planeLin : V →ₗ[K] V where
  toFun v := v + planeA₁ P P' g v • P.e + planeA₂ P P' g v • P'.e + planeC₁ P P' g v • P.f +
    planeC₂ P P' g v • P'.f
  map_add' x y := by
    simp only [planeA₁, planeA₂, planeC₁, planeC₂, polar_add_left]
    module
  map_smul' c x := by
    simp only [planeA₁, planeA₂, planeC₁, planeC₂, polar_smul_left_eq,
      RingHom.id_apply]
    module

theorem planeLin_apply (v : V) :
    planeLin P P' g v = v + planeA₁ P P' g v • P.e + planeA₂ P P' g v • P'.e +
      planeC₁ P P' g v • P.f + planeC₂ P P' g v • P'.f := rfl

variable {P P'}

theorem polar_planeLin_e (h : P.Orth P') (v : V) :
    polar Q (planeLin P P' g v) P.e =
      (g : Matrix (Fin 2) (Fin 2) K) 1 0 * polar Q v P'.f +
        (g : Matrix (Fin 2) (Fin 2) K) 1 1 * polar Q v P.e := by
  obtain ⟨ee, ee', ef, ef', fe, ff, fe', ff', e'e, e'f, e'e', e'f', f'e, f'f, f'e', f'f'⟩ :=
    polar_facts P P' h
  simp only [planeLin_apply, polar_add_left, polar_smul_left_eq, ee, e'e, fe, f'e, planeC₁]
  ring

theorem polar_planeLin_e' (h : P.Orth P') (v : V) :
    polar Q (planeLin P P' g v) P'.e =
      (g : Matrix (Fin 2) (Fin 2) K) 1 0 * polar Q v P.f +
        (g : Matrix (Fin 2) (Fin 2) K) 1 1 * polar Q v P'.e := by
  obtain ⟨ee, ee', ef, ef', fe, ff, fe', ff', e'e, e'f, e'e', e'f', f'e, f'f, f'e', f'f'⟩ :=
    polar_facts P P' h
  simp only [planeLin_apply, polar_add_left, polar_smul_left_eq, ee', e'e', fe', f'e', planeC₂]
  ring

theorem polar_planeLin_f (h : P.Orth P') (v : V) :
    polar Q (planeLin P P' g v) P.f =
      (g : Matrix (Fin 2) (Fin 2) K) 0 0 * polar Q v P.f +
        (g : Matrix (Fin 2) (Fin 2) K) 0 1 * polar Q v P'.e := by
  obtain ⟨ee, ee', ef, ef', fe, ff, fe', ff', e'e, e'f, e'e', e'f', f'e, f'f, f'e', f'f'⟩ :=
    polar_facts P P' h
  simp only [planeLin_apply, polar_add_left, polar_smul_left_eq, ef, e'f, ff, f'f, planeA₁]
  ring

theorem polar_planeLin_f' (h : P.Orth P') (v : V) :
    polar Q (planeLin P P' g v) P'.f =
      (g : Matrix (Fin 2) (Fin 2) K) 0 0 * polar Q v P'.f +
        (g : Matrix (Fin 2) (Fin 2) K) 0 1 * polar Q v P.e := by
  obtain ⟨ee, ee', ef, ef', fe, ff, fe', ff', e'e, e'f, e'e', e'f', f'e, f'f, f'e', f'f'⟩ :=
    polar_facts P P' h
  simp only [planeLin_apply, polar_add_left, polar_smul_left_eq, ef', e'f', ff', f'f', planeA₂]
  ring

theorem sl2_mul_apply (g g' : SpecialLinearGroup (Fin 2) K) (i j : Fin 2) :
    ((g * g' : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j =
      (g : Matrix (Fin 2) (Fin 2) K) i 0 * (g' : Matrix (Fin 2) (Fin 2) K) 0 j +
        (g : Matrix (Fin 2) (Fin 2) K) i 1 * (g' : Matrix (Fin 2) (Fin 2) K) 1 j := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem planeLin_one : planeLin P P' (1 : SpecialLinearGroup (Fin 2) K) = 1 := by
  apply LinearMap.ext
  intro v
  simp [planeLin_apply, planeA₁, planeA₂, planeC₁, planeC₂]

theorem planeLin_mul (h : P.Orth P') (g g' : SpecialLinearGroup (Fin 2) K) :
    planeLin P P' (g * g') = planeLin P P' g ∘ₗ planeLin P P' g' := by
  apply LinearMap.ext
  intro v
  rw [LinearMap.comp_apply]
  conv_rhs => rw [planeLin_apply, planeA₁, planeA₂, planeC₁, planeC₂]
  rw [polar_planeLin_f g' h, polar_planeLin_f' g' h, polar_planeLin_e g' h,
    polar_planeLin_e' g' h]
  conv_rhs => rw [planeLin_apply]
  simp only [planeLin_apply, planeA₁, planeA₂, planeC₁, planeC₂, sl2_mul_apply]
  module

theorem planeLin_isometry [CharP K 2] (h : P.Orth P') (v : V) :
    Q (planeLin P P' g v) = Q v := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hdet : (g : Matrix (Fin 2) (Fin 2) K) 0 0 * (g : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) K) 0 1 * (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
    have := g.2
    rw [Matrix.det_fin_two] at this
    exact this
  obtain ⟨-, ee', ef, ef', -, -, -, ff', -, e'f, -, e'f', -, -, -, -⟩ := polar_facts P P' h
  rw [planeLin_apply]
  simp only [QuadraticMap.map_add Q, map_smul_eq_sq, polar_add_left,
    polar_smul_left_eq, polar_smul_right_eq, P.Q_e, P.Q_f, P'.Q_e, P'.Q_f, ee', ef, ef', ff',
    e'f, e'f', planeA₁, planeA₂, planeC₁, planeC₂]
  set α := (g : Matrix (Fin 2) (Fin 2) K) 0 0
  set β := (g : Matrix (Fin 2) (Fin 2) K) 0 1
  set γ := (g : Matrix (Fin 2) (Fin 2) K) 1 0
  set δ := (g : Matrix (Fin 2) (Fin 2) K) 1 1
  set x₁ := polar Q v P.f
  set x₂ := polar Q v P'.f
  set y₁ := polar Q v P.e
  set y₂ := polar Q v P'.e
  linear_combination (x₁ * y₁ + x₂ * y₂) * hdet +
    (β * γ * (x₁ * y₁ + x₂ * y₂) + α * γ * x₁ * x₂ + β * δ * y₁ * y₂) * h2

@[expose] noncomputable def planeEnd (h : P.Orth P') :
    SpecialLinearGroup (Fin 2) K →* Module.End K V where
  toFun := planeLin P P'
  map_one' := planeLin_one
  map_mul' g g' := by
    rw [planeLin_mul h]
    rfl

@[expose] noncomputable def planeHom (h : P.Orth P') :
    SpecialLinearGroup (Fin 2) K →* (V ≃ₗ[K] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).toMonoidHom.comp
    (planeEnd h).toHomUnits

theorem planeHom_apply (h : P.Orth P') (v : V) : planeHom h g v = planeLin P P' g v := rfl

theorem planeHom_mem_orthogonalGroup [CharP K 2] (h : P.Orth P') :
    planeHom h g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
    rw [planeHom_apply]
    exact planeLin_isometry g h v

theorem planeHom_u2 [CharP K 2] (h : P.Orth P') (t : K) :
    planeHom h (u2 t) = eichler Q P.e (t • P'.e) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨ee, ee', ef, ef', fe, ff, fe', ff', e'e, e'f, e'e', e'f', f'e, f'f, f'e', f'f'⟩ :=
    polar_facts P P' h
  have hw : polar Q P.e (t • P'.e) = 0 := by rw [polar_smul_right_eq, ee', mul_zero]
  refine LinearEquiv.ext fun v => ?_
  rw [eichler_apply P.Q_e hw, planeHom_apply, planeLin_apply]
  simp only [planeA₁, planeA₂, planeC₁, planeC₂, u2_coe, polar_smul_right_eq, map_smul_eq_sq,
    P'.Q_e]
  simp
  rw [sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]
  module

theorem planeHom_l2 [CharP K 2] (h : P.Orth P') (t : K) :
    planeHom h (l2 t) = eichler Q P.f (t • P'.f) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨ee, ee', ef, ef', fe, ff, fe', ff', e'e, e'f, e'e', e'f', f'e, f'f, f'e', f'f'⟩ :=
    polar_facts P P' h
  have hw : polar Q P.f (t • P'.f) = 0 := by rw [polar_smul_right_eq, ff', mul_zero]
  refine LinearEquiv.ext fun v => ?_
  rw [eichler_apply P.Q_f hw, planeHom_apply, planeLin_apply]
  simp only [planeA₁, planeA₂, planeC₁, planeC₂, l2_coe, polar_smul_right_eq, map_smul_eq_sq,
    P'.Q_f]
  simp
  rw [sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]
  module

end Plane

end CFSG.RankThree.PartOne.SEITZ2
