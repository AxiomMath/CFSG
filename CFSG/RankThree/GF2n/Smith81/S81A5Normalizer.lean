module

public import CFSG.RankThree.GF2n.Smith81.S81A5ProjAut
public import CFSG.RankThree.GF2n.Smith81.S81A5Fixed
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix exteriorPower CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type*} [Field K]

private theorem n1_rho_one : rho K 1 = 1 :=
  map_one (TauCeti.extPowerRep K 6 3)

private theorem n1_sub_one_ne_zero {a b : Fin 6} (hab : a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (hne : a ≠ b) (I : Set.powersetCard (Fin 6) 3) (hb : b ∈ I.val) (ha : a ∉ I.val) :
    rho K (transvGL K a b hne 1) - 1 ≠ 0 := by
  intro h
  have hR : rho K (transvGL K a b hne 1) = 1 := sub_eq_zero.mp h
  have hc : b ∈ I.val ∧ a ∉ I.val := ⟨hb, ha⟩
  have key := rho_transvGL_cubeBasis (K := K) hab hne (1 : K) I
  rw [hR, Module.End.one_apply, dif_pos hc, one_smul] at key
  have h1 : cubeBasis K I + 0 = cubeBasis K I + cubeBasis K (replSet I a b hb ha) := by
    rw [add_zero]
    exact key
  exact (cubeBasis K).ne_zero _ (add_left_cancel h1).symm

theorem rho_transvGL_eq {a b : Fin 6} (hab : a.val + 1 = b.val ∨ b.val + 1 = a.val) (hne : a ≠ b) (t : K) :
    rho K (transvGL K a b hne t) = 1 + t • (rho K (transvGL K a b hne 1) - 1) := by
  refine (cubeBasis K).ext fun I => ?_
  rw [rho_transvGL_cubeBasis hab hne t I, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, Module.End.one_apply, rho_transvGL_cubeBasis hab hne (1 : K) I]
  split_ifs with h
  · rw [one_smul, add_sub_cancel_left]
  · rw [sub_self, smul_zero, add_zero]

theorem rho_transvGL_sub_one_ne_zero_23 : rho K (transvGL K 2 3 (by decide) 1) - 1 ≠ 0 :=
  n1_sub_one_ne_zero (a := 2) (b := 3) (by decide) (by decide)
    (tripleSet 0 1 3 (by decide) (by decide) (by decide)) (by decide) (by decide)

theorem rho_transvGL_sub_one_ne_zero_32 : rho K (transvGL K 3 2 (by decide) 1) - 1 ≠ 0 :=
  n1_sub_one_ne_zero (a := 3) (b := 2) (by decide) (by decide)
    (tripleSet 0 1 2 (by decide) (by decide) (by decide)) (by decide) (by decide)

theorem eq_of_twist_smul {V : Type*} [AddCommGroup V] [Module K V] {σ : K → K} (hσ : σ 1 = 1)
    (T : V ≃ₗ[K] V) (X Y : V →ₗ[K] V) (hY : Y ≠ 0)
    (h : ∀ (t : K) (ξ : V), T (ξ + t • X ξ) = T ξ + σ t • Y (T ξ)) (t : K) : σ t = t := by
  have hX : ∀ ξ : V, T (X ξ) = Y (T ξ) := by
    intro ξ
    have h1 := h 1 ξ
    rw [hσ, one_smul, one_smul, map_add] at h1
    exact add_left_cancel h1
  have hall : ∀ v : V, (t - σ t) • Y v = 0 := by
    intro v
    obtain ⟨ξ, rfl⟩ := T.surjective v
    have e1 := h t ξ
    rw [map_add, map_smul, hX ξ] at e1
    have e2 : t • Y (T ξ) = σ t • Y (T ξ) := add_left_cancel e1
    rw [sub_smul, e2, sub_self]
  obtain ⟨v, hv⟩ : ∃ v, Y v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hY (LinearMap.ext fun v => by simp [hcon v])
  rcases smul_eq_zero.mp (hall v) with h0 | h0
  · exact (sub_eq_zero.mp h0).symm
  · exact absurd h0 hv

theorem sigma_eq_one_of_twist {T : Cube K ≃ₗ[K] Cube K} {σ : K ≃+* K} {A : GL (Fin 6) K}
    {a b a' b' : Fin 6} (hab : a.val + 1 = b.val ∨ b.val + 1 = a.val) (hne : a ≠ b)
    (hab' : a'.val + 1 = b'.val ∨ b'.val + 1 = a'.val) (hne' : a' ≠ b')
    (hX' : rho K (transvGL K a' b' hne' 1) - 1 ≠ 0)
    (h : ∀ (t : K) (ξ : Cube K), T (rho K (transvGL K a b hne t) ξ) =
      rho K (A * transvGL K a' b' hne' (σ t) * A⁻¹) (T ξ)) :
    σ = 1 := by
  have hQP : rho K (A⁻¹) * rho K A = 1 := by
    rw [← rho_mul, inv_mul_cancel, n1_rho_one]
  have hPQ : rho K A * rho K (A⁻¹) = 1 := by
    rw [← rho_mul, mul_inv_cancel, n1_rho_one]
  have hY : rho K A * (rho K (transvGL K a' b' hne' 1) - 1) * rho K (A⁻¹) ≠ 0 := by
    intro hY0
    apply hX'
    calc rho K (transvGL K a' b' hne' 1) - 1
        = (rho K (A⁻¹) * rho K A) * (rho K (transvGL K a' b' hne' 1) - 1) *
            (rho K (A⁻¹) * rho K A) := by
          rw [hQP, one_mul, mul_one]
      _ = rho K (A⁻¹) * (rho K A * (rho K (transvGL K a' b' hne' 1) - 1) * rho K (A⁻¹)) *
            rho K A := by
          simp only [mul_assoc]
      _ = 0 := by rw [hY0, mul_zero, zero_mul]
  have hconj : ∀ t : K, rho K (A * transvGL K a' b' hne' (σ t) * A⁻¹) =
      1 + σ t • (rho K A * (rho K (transvGL K a' b' hne' 1) - 1) * rho K (A⁻¹)) := by
    intro t
    rw [rho_mul, rho_mul, rho_transvGL_eq hab' hne' (σ t), mul_add, add_mul, mul_one,
      mul_smul_comm, smul_mul_assoc, hPQ]
  have hform : ∀ (t : K) (ξ : Cube K), T (ξ + t • (rho K (transvGL K a b hne 1) - 1) ξ) =
      T ξ + σ t • (rho K A * (rho K (transvGL K a' b' hne' 1) - 1) * rho K (A⁻¹)) (T ξ) := by
    intro t ξ
    calc T (ξ + t • (rho K (transvGL K a b hne 1) - 1) ξ)
        = T (rho K (transvGL K a b hne t) ξ) := by
          rw [rho_transvGL_eq hab hne t, LinearMap.add_apply, LinearMap.smul_apply,
            Module.End.one_apply]
      _ = rho K (A * transvGL K a' b' hne' (σ t) * A⁻¹) (T ξ) := h t ξ
      _ = T ξ + σ t • (rho K A * (rho K (transvGL K a' b' hne' 1) - 1) * rho K (A⁻¹)) (T ξ) := by
          rw [hconj t, LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply]
  have hfix := eq_of_twist_smul (V := Cube K) (σ := ⇑σ) (map_one σ) T
    (rho K (transvGL K a b hne 1) - 1)
    (rho K A * (rho K (transvGL K a' b' hne' 1) - 1) * rho K (A⁻¹)) hY hform
  exact RingEquiv.ext fun t => hfix t

theorem twist_of_alpha_zero [CharP K 2] {T : Cube K ≃ₗ[K] Cube K} (hT : NormalizesSL T)
    {α : MulAut (projectiveSL 6 K)}
    (hα : ∀ g g' : SpecialLinearGroup (Fin 6) K,
      (∀ ξ, T (rho K (SpecialLinearGroup.toGL g) ξ) = rho K (SpecialLinearGroup.toGL g') (T ξ)) →
        α (proj 6 K g) = proj 6 K g')
    {A : GL (Fin 6) K} {σ : K ≃+* K} (hαeq : α = conjAut 6 K A * fieldAut 6 K σ)
    (g : SpecialLinearGroup (Fin 6) K) (ξ : Cube K) :
    T (rho K (SpecialLinearGroup.toGL g) ξ) =
      rho K (A * SpecialLinearGroup.toGL (SpecialLinearGroup.map σ.toRingHom g) * A⁻¹) (T ξ) := by
  obtain ⟨g', hg'⟩ := exists_sl_twist hT g
  have h1 := hα g g' hg'
  rw [hαeq] at h1
  simp only [MulAut.mul_apply, fieldAut_proj, conjAut_proj] at h1
  have h2 := (rho_eq_iff_proj_eq _ _).mpr h1
  rw [hg' ξ, ← h2, ← CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]

theorem twist_of_alpha_one [CharP K 2] {T : Cube K ≃ₗ[K] Cube K} (hT : NormalizesSL T)
    {α : MulAut (projectiveSL 6 K)}
    (hα : ∀ g g' : SpecialLinearGroup (Fin 6) K,
      (∀ ξ, T (rho K (SpecialLinearGroup.toGL g) ξ) = rho K (SpecialLinearGroup.toGL g') (T ξ)) →
        α (proj 6 K g) = proj 6 K g')
    {A : GL (Fin 6) K} {σ : K ≃+* K} (hαeq : α = conjAut 6 K A * fieldAut 6 K σ * dualAut 6 K)
    (g : SpecialLinearGroup (Fin 6) K) (ξ : Cube K) :
    T (rho K (SpecialLinearGroup.toGL g) ξ) =
      rho K (A * SpecialLinearGroup.toGL (SpecialLinearGroup.map σ.toRingHom (g⁻¹).transpose) * A⁻¹) (T ξ) := by
  obtain ⟨g', hg'⟩ := exists_sl_twist hT g
  have h1 := hα g g' hg'
  rw [hαeq] at h1
  simp only [MulAut.mul_apply, dualAut_proj, fieldAut_proj, conjAut_proj] at h1
  have h2 := (rho_eq_iff_proj_eq _ _).mpr h1
  rw [hg' ξ, ← h2, ← CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]

theorem toGL_map_transvection {a b : Fin 6} (hne : a ≠ b) (σ : K ≃+* K) (t : K) :
    SpecialLinearGroup.toGL (SpecialLinearGroup.map σ.toRingHom
        (Matrix.TransvectionStruct.toSpecialLinearGroup (⟨a, b, hne, t⟩ : Matrix.TransvectionStruct (Fin 6) K))) =
      transvGL K a b hne (σ t) := by
  apply Units.ext
  rw [transvGL_val]
  ext i j
  by_cases hij : i = j <;> by_cases hia : i = a <;> by_cases hjb : j = b <;>
    simp_all [Matrix.transvection, Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply,
      Matrix.single_apply, apply_ite]

theorem toGL_map_dual_transvection [CharP K 2] {a b : Fin 6} (hne : a ≠ b) (σ : K ≃+* K) (t : K) :
    SpecialLinearGroup.toGL (SpecialLinearGroup.map σ.toRingHom
        ((Matrix.TransvectionStruct.toSpecialLinearGroup
          (⟨a, b, hne, t⟩ : Matrix.TransvectionStruct (Fin 6) K))⁻¹).transpose) =
      transvGL K b a hne.symm (σ t) := by
  have hinv : (Matrix.TransvectionStruct.toSpecialLinearGroup
      (⟨a, b, hne, t⟩ : Matrix.TransvectionStruct (Fin 6) K))⁻¹ =
        Matrix.SpecialLinearGroup.transvection hne t := by
    rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk,
      Matrix.SpecialLinearGroup.transvection_inv, CharTwo.neg_eq]
  apply Units.ext
  rw [transvGL_val, hinv]
  ext i j
  by_cases hij : i = j <;> by_cases hia : j = a <;> by_cases hjb : i = b <;>
    simp_all [Matrix.transvection, Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply,
      Matrix.single_apply, apply_ite]

private theorem n3_map_one_eq (X : SpecialLinearGroup (Fin 6) K) :
    SpecialLinearGroup.map (1 : K ≃+* K).toRingHom X = X := by
  ext i j
  rfl

private theorem n3_toGL_map_one (X : SpecialLinearGroup (Fin 6) K) :
    SpecialLinearGroup.toGL (SpecialLinearGroup.map (1 : K ≃+* K).toRingHom X) =
      SpecialLinearGroup.toGL X := by
  rw [n3_map_one_eq]

private theorem n3_toGL_transpose_inv (gS : SpecialLinearGroup (Fin 6) K) :
    SpecialLinearGroup.toGL (gS⁻¹).transpose = invTransp (SpecialLinearGroup.toGL gS) := by
  refine Units.ext ?_
  have h1 : ((SpecialLinearGroup.toGL gS⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      (((SpecialLinearGroup.toGL gS)⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
    rw [map_inv]
  exact congrArg Matrix.transpose h1

theorem a5NormalizerModelStatement_holds : A5NormalizerModelStatement := by
  unfold A5NormalizerModelStatement
  intro K _ _ _ T hT
  obtain ⟨α, hα⟩ := exists_aut_of_normalizes hT
  obtain ⟨A, σ, ε, hε, hαeq⟩ := (automorphism_generation (K := K) (n := 6) (by norm_num)).2 α
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  ·
    simp only [pow_zero, mul_one] at hαeq
    have htw := twist_of_alpha_zero hT hα hαeq
    have hσ : σ = 1 := by
      refine sigma_eq_one_of_twist (K := K) (T := T) (A := A) (σ := σ) (a := 2) (b := 3)
        (a' := 2) (b' := 3) (by decide) (by decide) (by decide) (by decide)
        (rho_transvGL_sub_one_ne_zero_23 (K := K)) ?_
      intro t ξ
      have h := htw (Matrix.TransvectionStruct.toSpecialLinearGroup
        (⟨2, 3, by decide, t⟩ : Matrix.TransvectionStruct (Fin 6) K)) ξ
      rw [toGL_map_transvection] at h
      exact h
    subst hσ
    refine ⟨A, Or.inl ?_⟩
    intro g hg ξ
    obtain ⟨gS, rfl⟩ : ∃ gS : SpecialLinearGroup (Fin 6) K, SpecialLinearGroup.toGL gS = g :=
      ⟨⟨(g : Matrix (Fin 6) (Fin 6) K), hg⟩, Units.ext rfl⟩
    have h := htw gS ξ
    rw [n3_toGL_map_one] at h
    exact h
  ·
    simp only [pow_one] at hαeq
    have htw := twist_of_alpha_one hT hα hαeq
    have hσ : σ = 1 := by
      refine sigma_eq_one_of_twist (K := K) (T := T) (A := A) (σ := σ) (a := 2) (b := 3)
        (a' := 3) (b' := 2) (by decide) (by decide) (by decide) (by decide)
        (rho_transvGL_sub_one_ne_zero_32 (K := K)) ?_
      intro t ξ
      have h := htw (Matrix.TransvectionStruct.toSpecialLinearGroup
        (⟨2, 3, by decide, t⟩ : Matrix.TransvectionStruct (Fin 6) K)) ξ
      rw [toGL_map_dual_transvection (K := K) (a := 2) (b := 3) (by decide)] at h
      exact h
    subst hσ
    refine ⟨A, Or.inr ?_⟩
    intro g hg ξ
    obtain ⟨gS, rfl⟩ : ∃ gS : SpecialLinearGroup (Fin 6) K, SpecialLinearGroup.toGL gS = g :=
      ⟨⟨(g : Matrix (Fin 6) (Fin 6) K), hg⟩, Units.ext rfl⟩
    have h := htw gS ξ
    rw [n3_toGL_map_one, n3_toGL_transpose_inv] at h
    exact h

end CFSG.RankThree.GF2n.Smith81.A5Cube
