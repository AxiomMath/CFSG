module

public import CFSG.ClassicalGroups.Orthogonal.RootGroupChar
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
public import CFSG.ClassicalGroups.Orthogonal.RootGroupCard
public import CFSG.ClassicalGroups.Orthogonal.RootGroupNormalizer
public import CFSG.ClassicalGroups.Orthogonal.RootGroupPair

public section

namespace CFSG.StandardType.RCKC1

open CFSG.ClassicalGroups.Orthogonal QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

private theorem rckSOmM1_neg_eq_self [CharP K 2] (v : V) : -v = v := by
  rw [neg_eq_iff_add_eq_zero, ← two_smul K v, CharTwo.two_eq_zero, zero_smul]

private theorem rckSOmM1_sub_eq_add [CharP K 2] (a b : V) : a - b = a + b := by
  rw [sub_eq_add_neg, rckSOmM1_neg_eq_self (K := K)]

noncomputable def rckSOmM1_N (Q : QuadraticForm K V) (e w : V) : V →ₗ[K] V :=
  eichlerLin Q e w - 1

private theorem rckSOmM1_N_apply (e w x : V) :
    rckSOmM1_N Q e w x = polar Q x e • w - (polar Q x w + Q w * polar Q x e) • e := by
  simp only [rckSOmM1_N, LinearMap.sub_apply, Module.End.one_apply, eichlerLin_apply]
  abel

theorem rckSOmM1_N_apply' [CharP K 2] (e w x : V) :
    rckSOmM1_N Q e w x = polar Q x e • w + (polar Q x w + Q w * polar Q x e) • e := by
  rw [rckSOmM1_N_apply, rckSOmM1_sub_eq_add (K := K)]

private theorem rckSOmM1_quad_span [CharP K 2] {e w : V} (he : Q e = 0)
    (hew : polar Q e w = 0) (a b : K) : Q (a • e + b • w) = b ^ 2 * Q w := by
  rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, polar_smul_left_eq,
    polar_smul_right_eq, he, hew]
  ring

private theorem rckSOmM1_linearIndependent [CharP K 2] {e w : V} (he : Q e = 0)
    (hew : polar Q e w = 0) (hw : Q w ≠ 0) (he0 : e ≠ 0) : LinearIndependent K ![e, w] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have hQ0 : Q (a • e + b • w) = 0 := by rw [hab, map_zero]
  rw [rckSOmM1_quad_span he hew] at hQ0
  have hb : b = 0 := by
    have hb2 : b ^ 2 * Q w = 0 := hQ0
    exact (pow_eq_zero_iff two_ne_zero).mp ((mul_eq_zero.mp hb2).resolve_right hw)
  subst hb
  simp only [zero_smul, add_zero] at hab
  exact ⟨(smul_eq_zero.mp hab).resolve_right he0, rfl⟩

private theorem rckSOmM1_exists_dual [CharP K 2] (hQ : (polarBilin Q).Nondegenerate)
    [FiniteDimensional K V] {e w : V} (he : Q e = 0) (hew : polar Q e w = 0)
    (hw : Q w ≠ 0) (he0 : e ≠ 0) :
    ∃ g0 g1 : V, rckSOmM1_N Q e w g0 = w + Q w • e ∧ rckSOmM1_N Q e w g1 = e ∧
      polar Q e g0 = 1 ∧ polar Q e g1 = 0 ∧ polar Q w g0 = 0 ∧ polar Q w g1 = 1 := by
  obtain ⟨g, hg⟩ := exists_dual_family hQ (t := ![e, w])
    (rckSOmM1_linearIndependent he hew hw he0)
  have hg00 : polar Q e (g 0) = 1 := by simpa using hg 0 0
  have hg01 : polar Q e (g 1) = 0 := by simpa using hg 0 1
  have hg10 : polar Q w (g 0) = 0 := by simpa using hg 1 0
  have hg11 : polar Q w (g 1) = 1 := by simpa using hg 1 1
  refine ⟨g 0, g 1, ?_, ?_, hg00, hg01, hg10, hg11⟩
  · rw [rckSOmM1_N_apply', polar_comm Q (g 0) e, hg00, polar_comm Q (g 0) w, hg10]
    module
  · rw [rckSOmM1_N_apply', polar_comm Q (g 1) e, hg01, polar_comm Q (g 1) w, hg11]
    module

theorem rckSOmM1_N_range [CharP K 2] (hQ : (polarBilin Q).Nondegenerate)
    [FiniteDimensional K V] {e w : V} (he : Q e = 0) (hew : polar Q e w = 0)
    (hw : Q w ≠ 0) (he0 : e ≠ 0) :
    (rckSOmM1_N Q e w).range = Submodule.span K {e, w} := by
  obtain ⟨g0, g1, hg0, hg1, -, -, -, -⟩ := rckSOmM1_exists_dual hQ he hew hw he0
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, rfl⟩
    rw [rckSOmM1_N_apply']
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · rw [Submodule.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with heq | hwq
    · rw [heq]; exact ⟨g1, hg1⟩
    · rw [hwq]; refine ⟨g0 - Q w • g1, ?_⟩
      rw [map_sub, map_smul, hg0, hg1, rckSOmM1_sub_eq_add (K := K)]
      rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

theorem rckSOmM1_commute_fixes [CharP K 2] (hQ : (polarBilin Q).Nondegenerate)
    [FiniteDimensional K V] {e w : V} (he : Q e = 0) (hew : polar Q e w = 0)
    (hw : Q w ≠ 0) (he0 : e ≠ 0) {T : V ≃ₗ[K] V}
    (hT : T ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hcomm : ∀ x, T (eichler Q e w x) = eichler Q e w (T x)) :
    T e = e ∧ ∃ a : K, T (w + Q w • e) = (w + Q w • e) + a • e := by
  obtain ⟨g0, g1, hg0, hg1, hg0e, hg1e, -, hg1w⟩ := rckSOmM1_exists_dual hQ he hew hw he0
  have hxall : ∀ y, rckSOmM1_N Q e w y = eichler Q e w y - y := by
    intro y
    rw [rckSOmM1_N_apply]
    rw [eichler_apply he hew]
    abel
  have hNcomm : ∀ x, T (rckSOmM1_N Q e w x) = rckSOmM1_N Q e w (T x) := by
    intro x
    rw [hxall x, hxall (T x), map_sub, hcomm x]
  have hTe_mem : T e ∈ Submodule.span K {e, w} := by
    have h1 : T e = rckSOmM1_N Q e w (T g1) := by rw [← hNcomm g1, hg1]
    rw [← rckSOmM1_N_range hQ he hew hw he0, h1]
    exact ⟨T g1, rfl⟩
  have hTw_mem : T (w + Q w • e) ∈ Submodule.span K {e, w} := by
    have h1 : T (w + Q w • e) = rckSOmM1_N Q e w (T g0) := by rw [← hNcomm g0, hg0]
    rw [← rckSOmM1_N_range hQ he hew hw he0, h1]
    exact ⟨T g0, rfl⟩
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hTe_mem
  obtain ⟨γ, δ, hγδ⟩ := Submodule.mem_span_pair.mp hTw_mem
  have hβ : β = 0 := by
    have hQ0 : Q (T e) = 0 := by rw [map_of_mem hT e, he]
    rw [← hαβ] at hQ0
    rw [rckSOmM1_quad_span he hew α β] at hQ0
    exact (pow_eq_zero_iff two_ne_zero).mp ((mul_eq_zero.mp hQ0).resolve_right hw)
  subst hβ
  have hTe : T e = α • e := by rw [← hαβ]; simp
  have hα0 : α ≠ 0 := by
    intro h0
    have : T e = 0 := by rw [hTe, h0, zero_smul]
    exact he0 (T.injective (by rw [this, map_zero]))
  have hδ : δ = 1 := by
    have hQ0 : Q (T (w + Q w • e)) = Q (w + Q w • e) := map_of_mem hT _
    have hQw' : Q (w + Q w • e) = Q w := by
      have h := rckSOmM1_quad_span he hew (Q w) 1
      rw [one_smul, one_pow, one_mul, add_comm] at h
      exact h
    rw [hQw', ← hγδ] at hQ0
    rw [rckSOmM1_quad_span he hew γ δ] at hQ0
    have hδ2 : δ ^ 2 = 1 := by
      have h1 : (δ ^ 2 - 1) * Q w = 0 := by linear_combination hQ0
      exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hw)
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hsub : (δ - 1) ^ 2 = 0 := by linear_combination hδ2 + (1 - δ) * h2
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsub)
  subst hδ
  have hcoef : polar Q (T g0) e = 1 := by
    have h := congrArg (fun z => polar Q z g1) (hNcomm g0)
    rw [hg0, ← hγδ, rckSOmM1_N_apply'] at h
    simp only [polar_add_left, polar_smul_left_eq, hg1e, hg1w, mul_zero, mul_one, one_smul,
      add_zero, zero_add] at h
    exact h.symm
  have hTinv : T.symm e = α⁻¹ • e := by
    have h : T.symm (T e) = T.symm (α • e) := by rw [hTe]
    rw [LinearEquiv.symm_apply_apply, map_smul] at h
    calc T.symm e = α⁻¹ • (α • T.symm e) := by rw [smul_smul, inv_mul_cancel₀ hα0, one_smul]
      _ = α⁻¹ • e := by rw [← h]
  have hα1 : α = 1 := by
    have h3 : polar Q g0 (T.symm e) = α⁻¹ := by
      rw [hTinv, polar_smul_right_eq, polar_comm Q g0 e, hg0e, mul_one]
    have h4 : polar Q (T g0) e = polar Q g0 (T.symm e) := by
      have h := polar_map_of_mem hT g0 (T.symm e)
      rwa [LinearEquiv.apply_symm_apply] at h
    rw [h4, h3] at hcoef
    exact inv_eq_one.mp hcoef
  refine ⟨by rw [hTe, hα1, one_smul], ⟨γ + Q w, ?_⟩⟩
  rw [← hγδ, one_smul, add_comm (γ • e) w]
  rw [add_assoc, ← add_smul]
  congr 1
  rw [add_comm (Q w) (γ + Q w), add_assoc, CharTwo.add_self_eq_zero, add_zero]

end CFSG.StandardType.RCKC1
