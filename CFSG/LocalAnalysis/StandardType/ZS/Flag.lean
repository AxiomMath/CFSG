module

public import CFSG.LocalAnalysis.StandardType.GGQTwoReflLin
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.LinearMaps
import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.StandardType.ZS

@[expose] def FixesFlag {K : Type*} [Ring K] {U : Type*} [AddCommGroup U] [Module K U]
    (W X : Submodule K U) (k : U ≃ₗ[K] U) : Prop :=
  (∀ v, k v - v ∈ X) ∧ (∀ v ∈ X, k v - v ∈ W) ∧ ∀ v ∈ W, k v = v

variable {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U]

private theorem coe_pow_toEnd (k : U ≃ₗ[K] U) (n : ℕ) :
    ((k ^ n : U ≃ₗ[K] U) : U →ₗ[K] U) = (k : U →ₗ[K] U) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, LinearEquiv.coe_toLinearMap_mul, ih]

private theorem eq_one_of_fixes_line {G : Subgroup (U ≃ₗ[K] U)}
    (hG : QTwoLin.TransvectionFree G) {W : Submodule K U} (hW : Module.finrank K W = 1)
    {g : U ≃ₗ[K] U} (hg : g ∈ G) (hfix : ∀ w ∈ W, g w = w) (hquot : ∀ v, g v - v ∈ W) :
    g = 1 := by
  have hWne : W ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hW
    exact Nat.zero_ne_one hW
  obtain ⟨w₀, hw₀mem, hw₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
  have hspan : W = Submodule.span K {w₀} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hW hw₀mem hw₀ne
  let Φ : U →ₗ[K] (Submodule.span K {w₀}) :=
    LinearMap.codRestrict (Submodule.span K {w₀}) ((g : U →ₗ[K] U) - 1) fun v => by
      rw [← hspan]; simpa using hquot v
  let ψ : U →ₗ[K] K :=
    (LinearEquiv.toSpanNonzeroSingleton K U w₀ hw₀ne).symm.toLinearMap.comp Φ
  have hψ : ∀ v, ψ v • w₀ = g v - v := by
    intro v
    have h := LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul (R := K) (M := U) w₀ hw₀ne (Φ v)
    simp only [ψ, LinearEquiv.coe_toLinearMap, LinearMap.comp_apply] at h ⊢
    rw [h]
    rfl
  have hψ0 : ψ w₀ = 0 := by
    have h := hψ w₀
    rw [hfix w₀ hw₀mem, sub_self] at h
    exact (smul_eq_zero.mp h).resolve_right hw₀ne
  by_contra hgne
  have hψne : ψ ≠ 0 := by
    intro hzero
    apply hgne
    ext v
    have h := hψ v
    rw [hzero, LinearMap.zero_apply, zero_smul] at h
    exact sub_eq_zero.mp h.symm
  exact hG g hg ⟨w₀, ψ, hw₀ne, hψne, hψ0, fun v => by rw [hψ v]; abel⟩

theorem commute_of_fixesFlag {G : Subgroup (U ≃ₗ[K] U)} (hG : QTwoLin.TransvectionFree G)
    {W X : Submodule K U} (hW : Module.finrank K W = 1) {s t : U ≃ₗ[K] U}
    (hs : s ∈ G) (ht : t ∈ G) (hsf : FixesFlag W X s) (htf : FixesFlag W X t) :
    Commute s t := by
  set c : U ≃ₗ[K] U := s * t * s⁻¹ * t⁻¹ with hc
  have hcG : c ∈ G := by
    rw [hc]
    exact G.mul_mem (G.mul_mem (G.mul_mem hs ht) (G.inv_mem hs)) (G.inv_mem ht)
  have hsinv : ∀ w ∈ W, s⁻¹ w = w := fun w hw => by
    have h := congrArg (fun x => s⁻¹ x) (hsf.2.2 w hw)
    simpa using h.symm
  have htin : ∀ w ∈ W, t⁻¹ w = w := fun w hw => by
    have h := congrArg (fun x => t⁻¹ x) (htf.2.2 w hw)
    simpa using h.symm
  have hfix : ∀ w ∈ W, c w = w := by
    intro w hw
    rw [hc, LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      htin w hw, hsinv w hw, htf.2.2 w hw, hsf.2.2 w hw]
  have hquot : ∀ v, c v - v ∈ W := by
    intro v
    set w : U := s⁻¹ (t⁻¹ v) with hw
    have hcv : c v = s (t w) := by
      rw [hc]; simp [w]
    have htsw : t (s w) = v := by
      simp [w]
    have hsplit : c v - v =
        (s (t w - w) - (t w - w)) - (t (s w - w) - (s w - w)) := by
      rw [hcv]
      simp only [map_sub]
      rw [htsw]
      abel
    rw [hsplit]
    exact W.sub_mem (hsf.2.1 (t w - w) (htf.1 w))
      (htf.2.1 (s w - w) (hsf.1 w))
  have hc1 : c = 1 := eq_one_of_fixes_line hG hW hcG hfix hquot
  have hcomm : s * t * s⁻¹ * t⁻¹ = 1 := by rw [← hc]; exact hc1
  show s * t = t * s
  calc s * t = s * t * s⁻¹ * t⁻¹ * (t * s) := by group
    _ = 1 * (t * s) := by rw [hcomm]
    _ = t * s := by simp

theorem pow_eq_one_of_fixesFlag {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] {W X : Submodule (ZMod p) V} {k : V ≃ₗ[ZMod p] V}
    (hk : FixesFlag W X k) : k ^ p = 1 := by
  let N : Module.End (ZMod p) V := (k : V →ₗ[ZMod p] V) - 1
  have hN3 : N ^ 3 = 0 := by
    ext v
    have h1 : N v ∈ X := hk.1 v
    have h2 : N (N v) ∈ W := hk.2.1 (N v) h1
    have h3 : N (N (N v)) = 0 := by
      have h := hk.2.2 (N (N v)) h2
      simpa [N, sub_eq_zero] using h
    simpa [pow_succ, pow_two, Module.End.mul_apply] using h3
  have hp3 : 3 ≤ p := by
    have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  have hNp : N ^ p = 0 := by
    have hp' : p = 3 + (p - 3) := by omega
    rw [congrArg (fun n => N ^ n) hp', pow_add, hN3, zero_mul]
  have hk1 : (k : V →ₗ[ZMod p] V) = 1 + N := by
    ext v
    simp [N]
  suffices hpow : (k : Module.End (ZMod p) V) ^ p = 1 by
    refine LinearEquiv.toLinearMap_injective ?_
    have hcoe := coe_pow_toEnd (K := ZMod p) (U := V) k p
    rw [hcoe, hpow, LinearEquiv.coe_toLinearMap_one]
    rfl
  by_cases hV : Nontrivial V
  · let _ : CharP (Module.End (ZMod p) V) p := by
      obtain ⟨x, hx⟩ := exists_ne (0 : V)
      exact Module.charP_end (R := ZMod p) (M := V) (p := p) ⟨x, by
        rw [Submodule.eq_bot_iff]
        intro r hr
        rw [Ideal.mem_torsionOf_iff] at hr
        by_contra hr0
        exact hx (by
          have h1 : r⁻¹ • (r • x) = x := by
            rw [smul_smul, inv_mul_cancel₀ (a := r) hr0, one_smul]
          rw [hr, smul_zero] at h1
          exact h1.symm)⟩
    rw [hk1, add_pow_char_of_commute p (Commute.one_left N), hNp, add_zero, one_pow]
  · have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    exact Subsingleton.elim _ _

end CFSG.StandardType.ZS
