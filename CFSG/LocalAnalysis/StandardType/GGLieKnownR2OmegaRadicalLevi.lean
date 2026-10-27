module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaRadicalFrame
public import CFSG.ClassicalGroups.Orthogonal.OddOrder

public section

namespace CFSG.StandardType.LieKnownR2.POmega.Radical

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.StandardType.ClassicalPosition

@[expose] noncomputable def orthSiegelLevi {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (P P' : HypPair Q) : V ≃ₗ[K] V :=
  eichler Q P.e P'.f * eichler Q P'.e P.f

private theorem levi_add_self {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [CharP K 2] (x : V) : x + x = 0 := by
  rw [← two_smul K x, CharTwo.two_eq_zero, zero_smul]

private theorem levi_neg_eq {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [CharP K 2] (x : V) : -x = x :=
  neg_eq_of_add_eq_zero_left (levi_add_self (K := K) x)

private theorem levi_cross_fe {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') : polar Q P'.e P.f = 0 := by
  rw [polar_comm]; exact h.fe

private theorem levi_cross_ee {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') : polar Q P'.e P.e = 0 := by
  rw [polar_comm]; exact h.ee

private theorem levi_key_e1 {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') :
    eichler Q P'.e P.f P.e = P.e - P'.e := by
  rw [eichler_apply P'.Q_e (levi_cross_fe h)]
  simp only [h.ee, P.polar_ef, P.Q_f, zero_mul, add_zero, zero_smul, one_smul, sub_zero]

private theorem levi_key_e2 {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') :
    eichler Q P'.e P.f P'.e = P'.e := by
  rw [eichler_apply P'.Q_e (levi_cross_fe h)]
  simp only [P'.polar_ee, levi_cross_fe h, P.Q_f, zero_mul, add_zero,
    zero_smul, one_smul, sub_zero]

private theorem levi_key_f3 {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') :
    eichler Q P'.e P.f P'.f = P'.f + P.f := by
  rw [eichler_apply P'.Q_e (levi_cross_fe h)]
  simp only [P'.polar_fe, polar_comm Q P'.f P.f, h.ff, P.Q_f, zero_mul, add_zero,
    zero_smul, one_smul, zero_add, sub_zero]

private theorem levi_key_f4 {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] :
    eichler Q P.e P'.f (P'.f + P.f) = P.f := by
  rw [eichler_apply P.Q_e h.ef]
  simp only [polar_add_left, polar_comm Q P'.f P.e, h.ef, P.polar_fe, P'.polar_ff, h.ff,
    P'.Q_f, zero_mul, add_zero, zero_smul, one_smul, zero_add, sub_zero]
  have hh : P'.f + P.f + P'.f = P.f := by
    rw [add_assoc, add_comm P.f P'.f, ← add_assoc, levi_add_self (K := K), zero_add]
  rw [hh]

private theorem levi_apply_e1 {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] :
    orthSiegelLevi Q P P' P.e = P'.e := by
  rw [orthSiegelLevi, LinearEquiv.mul_apply, levi_key_e1 h, eichler_apply P.Q_e h.ef]
  simp only [polar_sub_left, P.polar_ee, levi_cross_ee h, h.ef, P'.polar_ef, P'.Q_f,
    zero_mul, add_zero, zero_smul, one_smul, zero_sub, sub_zero, neg_smul,
    CharTwo.sub_eq_add, CharTwo.neg_eq, add_zero, zero_add]
  have hh : P.e - P'.e - P.e = -P'.e := by abel
  rw [hh, levi_neg_eq (K := K)]

private theorem levi_apply_e2 {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] :
    orthSiegelLevi Q P P' P'.e = P.e + P'.e := by
  rw [orthSiegelLevi, LinearEquiv.mul_apply, levi_key_e2 h, eichler_apply P.Q_e h.ef]
  simp only [P.polar_ee, levi_cross_ee h, h.ef, P'.polar_ef, P'.Q_f, zero_mul, add_zero,
    zero_smul, one_smul, zero_add, sub_zero, zero_sub]
  rw [sub_eq_add_neg, levi_neg_eq (K := K), add_comm]

private theorem levi_apply_f2 {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] :
    orthSiegelLevi Q P P' P'.f = P.f := by
  rw [orthSiegelLevi, LinearEquiv.mul_apply, levi_key_f3 h, levi_key_f4 h]

private theorem levi_g_e {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') :
    orthSiegelLevi Q P P' P.e = (2 : K) • P.e - P'.e := by
  rw [orthSiegelLevi, LinearEquiv.mul_apply, levi_key_e1 h, eichler_apply P.Q_e h.ef]
  rw [polar_sub_left, polar_sub_left, P.polar_ee, levi_cross_ee h, h.ef, P'.polar_ef]
  simp only [P'.Q_f, zero_mul, add_zero, zero_smul, one_smul, zero_sub, sub_zero,
    neg_smul, neg_one_smul, neg_neg]
  module

private theorem levi_A2 {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] :
    eichler Q P.e P'.f * eichler Q P.e P'.f = 1 := by
  rw [eichler_mul h.ef h.ef, show P'.f + P'.f = 0 from levi_add_self (K := K) P'.f]
  exact eichler_zero_right Q P.e

private theorem levi_B2 {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] :
    eichler Q P'.e P.f * eichler Q P'.e P.f = 1 := by
  rw [eichler_mul (levi_cross_fe h) (levi_cross_fe h),
    show P.f + P.f = 0 from levi_add_self (K := K) P.f]
  exact eichler_zero_right Q P'.e

private theorem levi_g_sq {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] :
    orthSiegelLevi Q P P' * orthSiegelLevi Q P P' =
      eichler Q P'.e P.f * eichler Q P.e P'.f := by
  have hA2 := levi_A2 h
  have hB2 := levi_B2 h
  have hconjB := eichler_conj (eichler_mem_orthogonalGroup Q P'.e P.f) P.e P'.f
  have hconjA := eichler_conj (eichler_mem_orthogonalGroup Q P.e P'.f)
      (eichler Q P'.e P.f P.e) (eichler Q P'.e P.f P'.f)
  have hE : eichler Q (eichler Q P.e P'.f (eichler Q P'.e P.f P.e))
      (eichler Q P.e P'.f (eichler Q P'.e P.f P'.f)) = eichler Q P'.e P.f := by
    rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply]
    change eichler Q (orthSiegelLevi Q P P' P.e) (orthSiegelLevi Q P P' P'.f) = eichler Q P'.e P.f
    rw [levi_apply_e1 h, levi_apply_f2 h]
  have h1 : eichler Q P'.e P.f * eichler Q P.e P'.f *
      (eichler Q P'.e P.f)⁻¹ = eichler Q (eichler Q P'.e P.f P.e)
        (eichler Q P'.e P.f P'.f) := hconjB
  have h2 : eichler Q P.e P'.f * eichler Q (eichler Q P'.e P.f P.e)
        (eichler Q P'.e P.f P'.f) * (eichler Q P.e P'.f)⁻¹ = eichler Q P'.e P.f :=
    hconjA.trans hE
  have hBA : eichler Q P'.e P.f * eichler Q P.e P'.f =
      eichler Q (eichler Q P'.e P.f P.e) (eichler Q P'.e P.f P'.f) *
        eichler Q P'.e P.f := by
    calc eichler Q P'.e P.f * eichler Q P.e P'.f =
          eichler Q P'.e P.f * eichler Q P.e P'.f * (eichler Q P'.e P.f)⁻¹ *
            eichler Q P'.e P.f := by group
    _ = eichler Q (eichler Q P'.e P.f P.e) (eichler Q P'.e P.f P'.f) *
          eichler Q P'.e P.f := by rw [h1]
  have hAD : eichler Q P.e P'.f *
        eichler Q (eichler Q P'.e P.f P.e) (eichler Q P'.e P.f P'.f) =
      eichler Q P'.e P.f * eichler Q P.e P'.f := by
    calc eichler Q P.e P'.f *
          eichler Q (eichler Q P'.e P.f P.e) (eichler Q P'.e P.f P'.f) =
          eichler Q P.e P'.f * eichler Q (eichler Q P'.e P.f P.e)
            (eichler Q P'.e P.f P'.f) * (eichler Q P.e P'.f)⁻¹ * eichler Q P.e P'.f := by
              group
    _ = eichler Q P'.e P.f * eichler Q P.e P'.f := by rw [h2]
  calc
    orthSiegelLevi Q P P' * orthSiegelLevi Q P P'
        = eichler Q P.e P'.f * (eichler Q P'.e P.f * eichler Q P.e P'.f) *
            eichler Q P'.e P.f := by rw [orthSiegelLevi]; group
    _ = eichler Q P.e P'.f * (eichler Q (eichler Q P'.e P.f P.e)
          (eichler Q P'.e P.f P'.f) * eichler Q P'.e P.f) * eichler Q P'.e P.f := by
            rw [hBA]
    _ = eichler Q P.e P'.f * eichler Q (eichler Q P'.e P.f P.e)
          (eichler Q P'.e P.f P'.f) := by
            rw [show eichler Q P.e P'.f * (eichler Q (eichler Q P'.e P.f P.e)
                  (eichler Q P'.e P.f P'.f) * eichler Q P'.e P.f) * eichler Q P'.e P.f =
                eichler Q P.e P'.f * (eichler Q (eichler Q P'.e P.f P.e)
                  (eichler Q P'.e P.f P'.f) *
                    (eichler Q P'.e P.f * eichler Q P'.e P.f)) by group,
              hB2, mul_one]
    _ = eichler Q P'.e P.f * eichler Q P.e P'.f := hAD

private theorem levi_cube {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] :
    orthSiegelLevi Q P P' ^ 3 = 1 := by
  have hsq := levi_g_sq h
  have hA2 := levi_A2 h
  have hB2 := levi_B2 h
  calc
    orthSiegelLevi Q P P' ^ 3 = (orthSiegelLevi Q P P' * orthSiegelLevi Q P P')
      * orthSiegelLevi Q P P' := by
      rw [pow_succ, pow_two]
    _ = (eichler Q P'.e P.f * eichler Q P.e P'.f) *
          (eichler Q P.e P'.f * eichler Q P'.e P.f) := by rw [hsq, orthSiegelLevi]
    _ = 1 := by
      rw [show (eichler Q P'.e P.f * eichler Q P.e P'.f) *
              (eichler Q P.e P'.f * eichler Q P'.e P.f) =
            eichler Q P'.e P.f * (eichler Q P.e P'.f * eichler Q P.e P'.f) *
              eichler Q P'.e P.f by group,
          hA2, mul_one, hB2]

theorem orthSiegelLevi_mem_elementary {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') :
    orthSiegelLevi Q P P' ∈ elementaryGroup Q := by
  rw [orthSiegelLevi]
  exact Subgroup.mul_mem _ (eichler_mem_elementaryGroup Q P.e P'.f)
    (eichler_mem_elementaryGroup Q P'.e P.f)

theorem orthSiegelLevi_apply_e {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] :
    orthSiegelLevi Q P P' P.e = P'.e ∧ orthSiegelLevi Q P P' P'.e = P.e + P'.e :=
  ⟨levi_apply_e1 h, levi_apply_e2 h⟩

theorem orthSiegelLevi_fixes_W {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') {w : V}
    (hw : w ∈ siegelW Q P.e P'.e P.f P'.f) :
    orthSiegelLevi Q P P' w = w := by
  rw [siegelW, LinearMap.BilinForm.mem_orthogonal_iff] at hw
  have hmem : ∀ n ∈ ({P.e, P'.e, P.f, P'.f} : Set V), polar Q n w = 0 := by
    intro n hn
    simpa only [QuadraticMap.polarBilin_apply_apply] using hw n (Submodule.subset_span hn)
  have h1 : polar Q w P'.e = 0 := by rw [polar_comm]; exact hmem P'.e (by simp)
  have h2 : polar Q w P.f = 0 := by rw [polar_comm]; exact hmem P.f (by simp)
  have h3 : polar Q w P.e = 0 := by rw [polar_comm]; exact hmem P.e (by simp)
  have h4 : polar Q w P'.f = 0 := by rw [polar_comm]; exact hmem P'.f (by simp)
  rw [orthSiegelLevi, LinearEquiv.mul_apply,
    eichler_apply_of_polar_eq_zero h1 h2, eichler_apply_of_polar_eq_zero h3 h4]

theorem orthSiegelLevi_orderOf {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] :
    orderOf (orthSiegelLevi Q P P') = 3 := by
  refine orderOf_eq_prime (levi_cube h) ?_
  intro hg
  have hne : P.e ≠ P'.e := by
    intro heq
    have h1 : polar Q P.e P'.f = 0 := h.ef
    rw [heq, P'.polar_ef] at h1
    exact one_ne_zero h1
  have h2 : orthSiegelLevi Q P P' P.e = P.e := by rw [hg]; rfl
  rw [levi_g_e h] at h2
  have h3 : (2 : K) • P.e - P'.e = P'.e := by
    rw [show (2 : K) • P.e = 0 by rw [CharTwo.two_eq_zero, zero_smul], zero_sub,
      levi_neg_eq (K := K)]
  exact hne (h3.symm.trans h2).symm

end CFSG.StandardType.LieKnownR2.POmega.Radical
