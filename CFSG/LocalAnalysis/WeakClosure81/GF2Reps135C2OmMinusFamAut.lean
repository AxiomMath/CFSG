module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaMinusOpp
import CFSG.ClassicalInvolution.ModelFacts.OrthAutMain
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusAut

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

@[expose] noncomputable def omMinusReflAut (n : ℕ) (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    spinGroup (quadMinus n K b c) ≃* spinGroup (quadMinus n K b c) :=
  CFSG.StandardType.GGOppRadOmega.minusConj hirrQ hn
    (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup (quadMinus n K b c)
      (planeVec n planeOne))

theorem spinAction_omMinusReflAut {n : ℕ} (hn : 4 ≤ n) (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (g : spinGroup (quadMinus n K b c)) :
    spinAction (quadMinus n K b c) (omMinusReflAut n hn hirrQ g) =
      CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus n K b c) (planeVec n planeOne) *
        spinAction (quadMinus n K b c) g *
        CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus n K b c) (planeVec n planeOne) := by
  rw [omMinusReflAut, CFSG.StandardType.GGOppRadOmega.spinAction_minusConj,
    CFSG.ClassicalGroups.Orthogonal.reflect_inv]

theorem omMinusReflAut_apply_apply {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (g : spinGroup (quadMinus n K b c)) :
    omMinusReflAut n hn hirrQ (omMinusReflAut n hn hirrQ g) = g := by
  apply CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective hirrQ
  rw [spinAction_omMinusReflAut, spinAction_omMinusReflAut, ← mul_assoc, ← mul_assoc,
    CFSG.ClassicalGroups.Orthogonal.reflect_mul_self, one_mul, mul_assoc,
    CFSG.ClassicalGroups.Orthogonal.reflect_mul_self, mul_one]

private noncomputable instance w135c2_omfMAut_invert (n : ℕ) :
    Invertible (quadMinus n K b c (planeVec n planeOne)) :=
  invertibleOfNonzero (by rw [quadMinus_planeVec]; simp [planeOne])

private theorem w135c2_omfMAut_conj_reflect {M : Type*} [Group M] {A R g : M}
    (hR : R * R = 1) :
    (A * R) * g * (A * R)⁻¹ = A * (R * g * R) * A⁻¹ := by
  have hRinv : R⁻¹ = R := inv_eq_of_mul_eq_one_left hR
  rw [mul_inv_rev, hRinv]
  group

private theorem w135c2_omfMAut_inner_case {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {α : MulAut (spinGroup (quadMinus n K b c))} {gA : Vm n K ≃ₗ[K] Vm n K}
    (hA_orth : gA ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c))
    (hconj' : ∀ x, spinAction (quadMinus n K b c) (α x) =
      gA * spinAction (quadMinus n K b c) x * gA⁻¹)
    (hEven : Even (Module.finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace gA))) :
    ∃ h : spinGroup (quadMinus n K b c), ∀ g, α g = h * g * h⁻¹ := by
  have hgAmem : gA ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup (quadMinus n K b c)
      (nondegenerate_polarBilin_quadMinus_of_finite n K hirrQ) :=
    CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mpr ⟨hA_orth, hEven⟩
  obtain ⟨h, hh⟩ :=
    CFSG.StandardType.GGOppRadOmega.exists_spinAction_eq_of_mem_omegaGroup_minus
      (hirr := hirrQ) hn hgAmem
  refine ⟨h, fun g => ?_⟩
  apply CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective hirrQ
  rw [hconj' g, ← hh, map_mul, map_mul, map_inv]

private theorem w135c2_omfMAut_outer_case {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {α : MulAut (spinGroup (quadMinus n K b c))} {gA : Vm n K ≃ₗ[K] Vm n K}
    (hA_orth : gA ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c))
    (hconj' : ∀ x, spinAction (quadMinus n K b c) (α x) =
      gA * spinAction (quadMinus n K b c) x * gA⁻¹)
    (hOdd : Odd (Module.finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace gA))) :
    ∃ h : spinGroup (quadMinus n K b c),
      ∀ g, α g = h * omMinusReflAut n hn hirrQ g * h⁻¹ := by
  let R : Vm n K ≃ₗ[K] Vm n K :=
    CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus n K b c) (planeVec n planeOne)
  have hR_mem : R ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c) :=
    CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup _ _
  have hR_sq : R * R = 1 := CFSG.ClassicalGroups.Orthogonal.reflect_mul_self _ _
  have hRref : R = TauCeti.QuadraticMap.reflection (quadMinus n K b c)
      (planeVec n planeOne) :=
    CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection
  have hfinR : Module.finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace R) = 1 := by
    rw [hRref]
    exact CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_reflection
      (nondegenerate_polarBilin_quadMinus_of_finite n K hirrQ) (planeVec n planeOne)
  have hgAR_mem : gA * R ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup
      (quadMinus n K b c) (nondegenerate_polarBilin_quadMinus_of_finite n K hirrQ) := by
    refine CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mpr
      ⟨mul_mem hA_orth hR_mem, ?_⟩
    rw [← ZMod.natCast_eq_zero_iff_even,
      CFSG.RankThree.OrthogonalInvolutions.natCast_finrank_commSpace_mul
        (nondegenerate_polarBilin_quadMinus_of_finite n K hirrQ) hA_orth hR_mem,
      ZMod.natCast_eq_one_iff_odd.mpr hOdd, hfinR]
    exact CharTwo.add_self_eq_zero 1
  obtain ⟨h, hh⟩ :=
    CFSG.StandardType.GGOppRadOmega.exists_spinAction_eq_of_mem_omegaGroup_minus
      (hirr := hirrQ) hn hgAR_mem
  refine ⟨h, fun g => ?_⟩
  have hgAeq : gA = spinAction (quadMinus n K b c) h * R := by
    rw [hh, mul_assoc, hR_sq, mul_one]
  apply CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective hirrQ
  rw [hconj' g, hgAeq, map_mul, map_mul, map_inv, spinAction_omMinusReflAut]
  exact w135c2_omfMAut_conj_reflect hR_sq

theorem omMinus_two_aut_inner_or_refl (hK : Nat.card K = 2) {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (α : MulAut (spinGroup (quadMinus n K b c))) :
    ∃ h : spinGroup (quadMinus n K b c),
      (∀ g, α g = h * g * h⁻¹) ∨ ∀ g, α g = h * omMinusReflAut n hn hirrQ g * h⁻¹ := by
  classical
  obtain ⟨hcard, hμ1, hφr⟩ := omPlusAut_field_triv hK
  obtain ⟨A, φ, μ, hsim, hconj⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.OrthAut.spinMinus_aut_similarity
      (p := 2) (f := 1) hn le_rfl (by rw [pow_one]; exact hK) hirrQ α
  have hφ : φ = RingEquiv.refl K := hφr φ
  have hμ : (μ : K) = 1 := hμ1 μ
  set gA : Vm n K ≃ₗ[K] Vm n K :=
    omPlusAutGlLin (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K A with hgAset
  have hA_orth : gA ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    have h := hsim v
    rw [hφ] at h
    have hfun : (fun i => (RingEquiv.refl K) (v i)) = v := rfl
    rw [hfun, hμ, one_mul] at h
    simp only [RingEquiv.refl_apply] at h
    rw [hgAset, omPlusAutGlLin_apply]
    exact h
  have hconj' : ∀ x, spinAction (quadMinus n K b c) (α x) =
      gA * spinAction (quadMinus n K b c) x * gA⁻¹ := by
    intro x
    rw [← omPlusAutGlLin_spinMatrix (Q := quadMinus n K b c) (x := α x), hconj x, hφ,
      omPlusAut_glFieldEquiv_refl]
    rw [hgAset, map_mul, map_mul, map_inv, omPlusAutGlLin_spinMatrix]
  by_cases hEven : Even (Module.finrank K
    (CFSG.RankThree.OrthogonalInvolutions.commSpace gA))
  · obtain ⟨h, hh⟩ := w135c2_omfMAut_inner_case hn hirrQ hA_orth hconj' hEven
    exact ⟨h, Or.inl hh⟩
  · obtain ⟨h, hh⟩ :=
      w135c2_omfMAut_outer_case hn hirrQ hA_orth hconj' (Nat.not_even_iff_odd.mp hEven)
    exact ⟨h, Or.inr hh⟩

end CFSG.LocalAnalysis.WeakClosure81
