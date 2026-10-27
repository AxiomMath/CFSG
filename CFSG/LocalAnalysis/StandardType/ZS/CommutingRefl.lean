module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.GGWitSlpmConjAux
public import Mathlib.LinearAlgebra.Reflection
import CFSG.LocalAnalysis.StandardType.GGWitSlpm

public section

namespace CFSG.StandardType.ZS

open Module

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private lemma commute_smul_eq {a b : U} {φ ψ : Dual (ZMod p) U}
    (hφ : φ a = 2) (hψ : ψ b = 2)
    (hcomm : Commute (reflection hφ) (reflection hψ)) (v : U) :
    (φ b * ψ v) • a = (ψ a * φ v) • b := by
  have key : (reflection hφ) ((reflection hψ) v) = (reflection hψ) ((reflection hφ) v) := by
    change ((reflection hφ) * (reflection hψ)) v = ((reflection hψ) * (reflection hφ)) v
    rw [hcomm]
  have h1 : (reflection hφ) ((reflection hψ) v)
      = v - ψ v • b - (φ v - ψ v * φ b) • a := by
    rw [reflection_apply v hψ, reflection_apply _ hφ, map_sub, map_smul, smul_eq_mul]
    abel
  have h2 : (reflection hψ) ((reflection hφ) v)
      = v - φ v • a - (ψ v - φ v * ψ a) • b := by
    rw [reflection_apply v hφ, reflection_apply _ hψ, map_sub, map_smul, smul_eq_mul]
    abel
  have hE : v - ψ v • b - (φ v - ψ v * φ b) • a
      = v - φ v • a - (ψ v - φ v * ψ a) • b :=
    h1.symm.trans (key.trans h2)
  have heq : (v - ψ v • b - (φ v - ψ v * φ b) • a)
        - (v - φ v • a - (ψ v - φ v * ψ a) • b)
      = (ψ v * φ b) • a - (φ v * ψ a) • b := by
    module
  have h0 : (ψ v * φ b) • a - (φ v * ψ a) • b = 0 := by
    rw [← heq]
    exact sub_eq_zero.mpr hE
  exact sub_eq_zero.mp (by
    rwa [mul_comm (ψ v) (φ b), mul_comm (φ v) (ψ a)] at h0)

theorem reflection_eq_of_commute_of_mem_span (hp : p ≠ 2) {a b : U} {φ ψ : Dual (ZMod p) U}
    (hφ : φ a = 2) (hψ : ψ b = 2) (hcomm : Commute (reflection hφ) (reflection hψ))
    (hab : b ∈ Submodule.span (ZMod p) {a}) : reflection hφ = reflection hψ := by
  obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.mp hab
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, map_zero] at hφ
    exact h2 hφ.symm
  have hlψa : l * ψ a = 2 := by
    rw [← hl, map_smul, smul_eq_mul] at hψ
    exact hψ
  have hψa0 : ψ a ≠ 0 := by
    intro h
    rw [h, mul_zero] at hlψa
    exact h2 hlψa.symm
  have hrel := commute_smul_eq hφ hψ hcomm
  have hφb : φ b = 2 * l := by
    have hv := hrel a
    rw [hφ] at hv
    nth_rewrite 2 [← hl] at hv
    rw [smul_smul] at hv
    have hcoef := (smul_left_inj ha0).mp hv
    rw [mul_assoc] at hcoef
    exact mul_left_cancel₀ hψa0 (by rwa [mul_comm (φ b) (ψ a)] at hcoef)
  have hφv : ∀ v, φ v = l * ψ v := by
    intro v
    have hv := hrel v
    nth_rewrite 2 [← hl] at hv
    rw [smul_smul] at hv
    have hcoef := (smul_left_inj ha0).mp hv
    rw [hφb, mul_assoc, mul_comm (ψ a) (φ v), mul_assoc, mul_comm (ψ a) l, hlψa,
      mul_comm (φ v) 2] at hcoef
    exact (mul_left_cancel₀ h2 hcoef).symm
  apply LinearEquiv.ext
  intro v
  rw [reflection_apply v hφ, reflection_apply v hψ, ← hl, hφv v, smul_smul, mul_comm (ψ v) l]

theorem apply_eq_zero_of_commute (hp : p ≠ 2) {a b : U} {φ ψ : Dual (ZMod p) U}
    (hφ : φ a = 2) (hψ : ψ b = 2) (hcomm : Commute (reflection hφ) (reflection hψ))
    (hne : reflection hφ ≠ reflection hψ) : φ b = 0 := by
  by_contra hφb
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hcoef : φ b * 2 ≠ 0 := mul_ne_zero hφb h2
  have hrel := commute_smul_eq hφ hψ hcomm b
  rw [hψ] at hrel
  have ha : a ∈ Submodule.span (ZMod p) {b} := by
    refine Submodule.mem_span_singleton.mpr ⟨(φ b * 2)⁻¹ * (ψ a * φ b), ?_⟩
    rw [← smul_smul, ← hrel, smul_smul, inv_mul_cancel₀ hcoef, one_smul]
  exact hne (reflection_eq_of_commute_of_mem_span hp hψ hφ hcomm.symm ha).symm

theorem linearIndependent_of_pairwise_commute (hp : p ≠ 2) {ι : Type*} {a : ι → U}
    {φ : ι → Dual (ZMod p) U} (hφ : ∀ i, φ i (a i) = 2)
    (hcomm : Pairwise fun i j => Commute (reflection (hφ i)) (reflection (hφ j)))
    (hne : Pairwise fun i j => reflection (hφ i) ≠ reflection (hφ j)) :
    LinearIndependent (ZMod p) a := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have hzero : ∀ j ∈ s, j ≠ i → φ i (a j) = 0 := fun j _ hji =>
    apply_eq_zero_of_commute hp (hφ i) (hφ j) (hcomm (Ne.symm hji)) (hne (Ne.symm hji))
  have hmap : ∑ j ∈ s, g j * φ i (a j) = 0 := by
    have := congrArg (φ i) hsum
    simpa only [map_sum, map_smul, map_zero, smul_eq_mul] using this
  rw [Finset.sum_eq_single i (fun j hj hji => by rw [hzero j hj hji, mul_zero])
    (fun hi' => absurd hi hi')] at hmap
  rw [hφ i] at hmap
  exact (mul_eq_zero.mp hmap).resolve_right h2

end CFSG.StandardType.ZS
