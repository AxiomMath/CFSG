module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaRadicalLevi

public section

namespace CFSG.StandardType.LieKnownR2.POmega.Radical

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.StandardType.ClassicalPosition

private theorem torus_U1_apply_e {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (c : K) :
    eichler Q P.e (c • P'.e) P.e = P.e :=
  eichler_apply_self P.e (c • P'.e)

private theorem torus_U1_apply_e_one {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} :
    eichler Q P.e P'.e P.e = P.e :=
  eichler_apply_self P.e P'.e

private theorem torus_U1_apply_e' {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') (c : K) :
    eichler Q P.e (c • P'.e) P'.e = P'.e := by
  refine eichler_apply_of_polar_eq_zero ?_ ?_
  · rw [polar_comm, h.ee]
  · rw [polar_smul_right_eq, polar_self_eq_zero P'.Q_e, mul_zero]

private theorem torus_U1_apply_e'_one {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') :
    eichler Q P.e P'.e P'.e = P'.e := by
  simpa only [one_smul] using torus_U1_apply_e' (Q := Q) (P := P) (P' := P') h 1

private theorem torus_U1_apply_f {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') (c : K) :
    eichler Q P.e (c • P'.e) P.f = P.f + c • P'.e := by
  rw [eichler_apply P.Q_e (by rw [polar_smul_right_eq, h.ee, mul_zero])]
  simp only [P.polar_fe, one_smul, polar_smul_right_eq, h.fe, mul_zero, map_smul_eq_sq, P'.Q_e,
    zero_mul, add_zero, zero_smul, sub_zero]

private theorem torus_U1_apply_f_one {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') :
    eichler Q P.e P'.e P.f = P.f + P'.e := by
  simpa only [one_smul] using torus_U1_apply_f (Q := Q) (P := P) (P' := P') h 1

private theorem torus_U1_apply_f' {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] (c : K) :
    eichler Q P.e (c • P'.e) P'.f = P'.f + c • P.e := by
  rw [eichler_apply P.Q_e (by rw [polar_smul_right_eq, h.ee, mul_zero])]
  rw [polar_comm Q P'.f P.e, h.ef, zero_smul, polar_smul_right_eq, P'.polar_fe, mul_one,
    map_smul_eq_sq, P'.Q_e, mul_zero]
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h2K : ∀ x : K, x + x = 0 := fun x => by rw [← two_smul K x, h2, zero_smul]
  rw [sub_eq_add_neg, add_zero, ← neg_smul]
  exact congrArg (fun d : K => P'.f + d • P.e) (by
    rw [add_zero, neg_eq_iff_add_eq_zero]
    exact h2K c)

private theorem torus_U1_apply_f'_one {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] :
    eichler Q P.e P'.e P'.f = P'.f + P.e := by
  simpa only [one_smul] using torus_U1_apply_f' (Q := Q) (P := P) (P' := P') h 1

private theorem torus_U2_apply_f {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (c : K) :
    eichler Q P.f (c • P'.f) P.f = P.f :=
  eichler_apply_self P.f (c • P'.f)

private theorem torus_U2_apply_f_one {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} :
    eichler Q P.f P'.f P.f = P.f :=
  eichler_apply_self P.f P'.f

private theorem torus_U2_apply_f' {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') (c : K) :
    eichler Q P.f (c • P'.f) P'.f = P'.f := by
  refine eichler_apply_of_polar_eq_zero ?_ ?_
  · rw [polar_comm, h.ff]
  · rw [polar_smul_right_eq, polar_self_eq_zero P'.Q_f, mul_zero]

private theorem torus_U2_apply_f'_one {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') :
    eichler Q P.f P'.f P'.f = P'.f := by
  simpa only [one_smul] using torus_U2_apply_f' (Q := Q) (P := P) (P' := P') h 1

private theorem torus_U2_apply_e {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') (c : K) :
    eichler Q P.f (c • P'.f) P.e = P.e + c • P'.f := by
  rw [eichler_apply P.Q_f (by rw [polar_smul_right_eq, h.ff, mul_zero])]
  simp only [P.polar_ef, one_smul, polar_smul_right_eq, h.ef, mul_zero, map_smul_eq_sq, P'.Q_f,
    zero_mul, add_zero, zero_smul, sub_zero]

private theorem torus_U2_apply_e_one {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') :
    eichler Q P.f P'.f P.e = P.e + P'.f := by
  simpa only [one_smul] using torus_U2_apply_e (Q := Q) (P := P) (P' := P') h 1

private theorem torus_U2_apply_e' {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] (c : K) :
    eichler Q P.f (c • P'.f) P'.e = P'.e + c • P.f := by
  rw [eichler_apply P.Q_f (by rw [polar_smul_right_eq, h.ff, mul_zero])]
  rw [polar_comm Q P'.e P.f, h.fe, zero_smul, polar_smul_right_eq, P'.polar_ef, mul_one,
    map_smul_eq_sq, P'.Q_f, mul_zero]
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h2K : ∀ x : K, x + x = 0 := fun x => by rw [← two_smul K x, h2, zero_smul]
  rw [sub_eq_add_neg, add_zero, ← neg_smul]
  exact congrArg (fun d : K => P'.e + d • P.f) (by
    rw [add_zero, neg_eq_iff_add_eq_zero]
    exact h2K c)

private theorem torus_U2_apply_e'_one {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] :
    eichler Q P.f P'.f P'.e = P'.e + P.f := by
  simpa only [one_smul] using torus_U2_apply_e' (Q := Q) (P := P) (P' := P') h 1

private noncomputable def torus_siegelTorus {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] (Q : QuadraticForm K V) (P P' : HypPair Q) (l : K) : V ≃ₗ[K] V :=
  eichler Q P.e (l • P'.e) * eichler Q P.f (l⁻¹ • P'.f) * eichler Q P.e (l • P'.e) *
    eichler Q P.e P'.e * eichler Q P.f P'.f * eichler Q P.e P'.e

private theorem torus_siegelTorus_apply_e {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] {l : K} (hl : l ≠ 0) :
    torus_siegelTorus Q P P' l P.e = l • P.e := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h2V : ∀ x : V, x + x = 0 := fun x => by rw [← two_smul K x, h2, zero_smul]
  have h2V' : ∀ x y : V, x + (x + y) = y := by
    intro x y; rw [← add_assoc, h2V, zero_add]
  simp only [torus_siegelTorus, LinearEquiv.mul_apply, map_add, map_smul, smul_add, smul_smul,
    one_smul, torus_U1_apply_e, torus_U1_apply_e_one, torus_U1_apply_f h, torus_U1_apply_f' h,
    torus_U1_apply_f'_one h, torus_U2_apply_e h, torus_U2_apply_e_one h, torus_U2_apply_f,
    torus_U2_apply_f' h, torus_U2_apply_f'_one h, mul_inv_cancel₀ hl,
    inv_mul_cancel₀ hl, mul_one, one_mul, h2V, h2V', add_assoc, add_comm, add_left_comm, add_zero,
    zero_add]

private theorem torus_siegelTorus_apply_e' {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] {l : K} (hl : l ≠ 0) :
    torus_siegelTorus Q P P' l P'.e = l • P'.e := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h2V : ∀ x : V, x + x = 0 := fun x => by rw [← two_smul K x, h2, zero_smul]
  have h2V' : ∀ x y : V, x + (x + y) = y := by
    intro x y; rw [← add_assoc, h2V, zero_add]
  simp only [torus_siegelTorus, LinearEquiv.mul_apply, map_add, map_smul, smul_add, smul_smul,
    one_smul, torus_U1_apply_e, torus_U1_apply_e' h, torus_U1_apply_e'_one h,
    torus_U1_apply_e_one, torus_U1_apply_f h, torus_U1_apply_f_one h, torus_U2_apply_e' h,
    torus_U2_apply_e'_one h, torus_U2_apply_f, torus_U2_apply_f_one, mul_inv_cancel₀ hl,
    inv_mul_cancel₀ hl, mul_one, one_mul, h2V, h2V', add_assoc, add_comm, add_left_comm, add_zero,
    zero_add]

private theorem torus_siegelTorus_apply_f {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] {l : K} (hl : l ≠ 0) :
    torus_siegelTorus Q P P' l P.f = l⁻¹ • P.f := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h2V : ∀ x : V, x + x = 0 := fun x => by rw [← two_smul K x, h2, zero_smul]
  have h2V' : ∀ x y : V, x + (x + y) = y := by
    intro x y; rw [← add_assoc, h2V, zero_add]
  simp only [torus_siegelTorus, LinearEquiv.mul_apply, map_add, map_smul, smul_add, smul_smul,
    one_smul, torus_U1_apply_e, torus_U1_apply_e' h, torus_U1_apply_e'_one h,
    torus_U1_apply_f h, torus_U1_apply_f_one h, torus_U2_apply_e' h, torus_U2_apply_e'_one h,
    torus_U2_apply_f, torus_U2_apply_f_one, mul_inv_cancel₀ hl, inv_mul_cancel₀ hl, mul_one,
    one_mul, h2V, h2V', add_assoc, add_comm, add_left_comm, add_zero, zero_add]

private theorem torus_siegelTorus_apply_f' {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] {l : K} (hl : l ≠ 0) :
    torus_siegelTorus Q P P' l P'.f = l⁻¹ • P'.f := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h2V : ∀ x : V, x + x = 0 := fun x => by rw [← two_smul K x, h2, zero_smul]
  have h2V' : ∀ x y : V, x + (x + y) = y := by
    intro x y; rw [← add_assoc, h2V, zero_add]
  simp only [torus_siegelTorus, LinearEquiv.mul_apply, map_add, map_smul, smul_add, smul_smul,
    one_smul, torus_U1_apply_e, torus_U1_apply_e_one, torus_U1_apply_f' h,
    torus_U1_apply_f'_one h, torus_U2_apply_e h, torus_U2_apply_e_one h, torus_U2_apply_f' h,
    torus_U2_apply_f'_one h, mul_inv_cancel₀ hl, inv_mul_cancel₀ hl, mul_one, one_mul, h2V,
    h2V', add_assoc, add_comm, add_left_comm, add_zero, zero_add]

private theorem torus_siegelTorus_fixes {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (l : K) {w : V}
    (hw : w ∈ siegelW Q P.e P'.e P.f P'.f) : torus_siegelTorus Q P P' l w = w := by
  have hgen : ∀ x ∈ Submodule.span K ({P.e, P'.e, P.f, P'.f} : Set V), polar Q x w = 0 :=
    mem_orth_iff.mp hw
  have key : ∀ u v : V, u ∈ Submodule.span K ({P.e, P'.e, P.f, P'.f} : Set V) →
      v ∈ Submodule.span K ({P.e, P'.e, P.f, P'.f} : Set V) → eichler Q u v w = w := by
    intro u v hu hv
    refine eichler_apply_of_polar_eq_zero ?_ ?_
    · rw [polar_comm]; exact hgen u hu
    · rw [polar_comm]; exact hgen v hv
  have hPe : P.e ∈ Submodule.span K ({P.e, P'.e, P.f, P'.f} : Set V) :=
    Submodule.subset_span (by simp)
  have hPe' : P'.e ∈ Submodule.span K ({P.e, P'.e, P.f, P'.f} : Set V) :=
    Submodule.subset_span (by simp)
  have hPf : P.f ∈ Submodule.span K ({P.e, P'.e, P.f, P'.f} : Set V) :=
    Submodule.subset_span (by simp)
  have hPf' : P'.f ∈ Submodule.span K ({P.e, P'.e, P.f, P'.f} : Set V) :=
    Submodule.subset_span (by simp)
  have hX : eichler Q P.e P'.e w = w := key P.e P'.e hPe hPe'
  have hY : eichler Q P.f P'.f w = w := key P.f P'.f hPf hPf'
  have hXl : eichler Q P.e (l • P'.e) w = w :=
    key P.e (l • P'.e) hPe (Submodule.smul_mem _ l hPe')
  have hYl : eichler Q P.f (l⁻¹ • P'.f) w = w :=
    key P.f (l⁻¹ • P'.f) hPf (Submodule.smul_mem _ l⁻¹ hPf')
  simp only [torus_siegelTorus, LinearEquiv.mul_apply, hX, hY, hXl, hYl]

theorem siegelTorus_exists {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] (lam : Kˣ) :
    ∃ s ∈ elementaryGroup Q,
      s P.e = (lam : K) • P.e ∧ s P'.e = (lam : K) • P'.e ∧
      s P.f = ((lam : K)⁻¹) • P.f ∧ s P'.f = ((lam : K)⁻¹) • P'.f ∧
      (∀ w ∈ siegelW Q P.e P'.e P.f P'.f, s w = w) := by
  refine ⟨torus_siegelTorus Q P P' (lam : K), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [torus_siegelTorus]
    repeat' apply Subgroup.mul_mem
    all_goals exact eichler_mem_elementaryGroup Q _ _
  · exact torus_siegelTorus_apply_e h (Units.ne_zero lam)
  · exact torus_siegelTorus_apply_e' h (Units.ne_zero lam)
  · exact torus_siegelTorus_apply_f h (Units.ne_zero lam)
  · exact torus_siegelTorus_apply_f' h (Units.ne_zero lam)
  · intro w hw
    exact torus_siegelTorus_fixes (lam : K) hw

end CFSG.StandardType.LieKnownR2.POmega.Radical
