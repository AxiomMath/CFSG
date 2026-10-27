module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR33Aux2
import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR33Aux3
public import CFSG.LocalAnalysis.StandardType.GGWitOrthTypeA
public import CFSG.LocalAnalysis.StandardType.GGWitOrthNormal
import Mathlib.LinearAlgebra.Reflection

public section

namespace CFSG.StandardType.ZS

open Subgroup

attribute [-instance] Nat.fact_prime_three

theorem owR33_classRefl_scale3 (w : Fin 3 → ZMod 3) (c : ZMod 3) (hc : c ≠ 0) :
    ClassRefl 3 (owR33_Qw 3 3 (fun i => c⁻¹ * w i)) 1 = ClassRefl 3 (owR33_Qw 3 3 w) c := by
  have hcinv : c⁻¹ = c := by
    have h : ∀ c : ZMod 3, c ≠ 0 → c⁻¹ = c := by decide +kernel
    exact h c hc
  have hsq : c * c = 1 := by
    have h : ∀ c : ZMod 3, c ≠ 0 → c * c = 1 := by decide +kernel
    exact h c hc
  have hQ : owR33_Qw 3 3 (fun i => c⁻¹ * w i) = c⁻¹ • owR33_Qw 3 3 w := by
    ext v
    rw [owR33_Qw_apply, smul_apply, owR33_Qw_apply]
    simp only [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hQ, hcinv]
  ext t
  simp only [ClassRefl, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hrefl, hiso, a, ha, hta⟩
    refine ⟨hrefl, ?_, a, ?_, hta⟩
    · intro v
      have h := hiso v
      change c * owR33_Qw 3 3 w (t v) = c * owR33_Qw 3 3 w v at h
      have h2 := congrArg (fun x => c * x) h
      simpa [← mul_assoc, hsq, one_mul] using h2
    · have h := ha
      change c * owR33_Qw 3 3 w a = 1 at h
      have h2 := congrArg (fun x => c * x) h
      simpa [← mul_assoc, hsq, one_mul] using h2
  · rintro ⟨hrefl, hiso, a, ha, hta⟩
    refine ⟨hrefl, ?_, a, ?_, hta⟩
    · intro v
      change c * owR33_Qw 3 3 w (t v) = c * owR33_Qw 3 3 w v
      rw [hiso v]
    · change c * owR33_Qw 3 3 w a = 1
      rw [ha, hsq]

def owR33_alphaLinP (p : ℕ) (W : Fin 3 → ZMod p) (a : Fin 3 → ZMod p) :
    (Fin 3 → ZMod p) →ₗ[ZMod p] ZMod p where
  toFun v := (2 * (1 : ZMod p)⁻¹) * ∑ k, W k * (v k * a k)
  map_add' x y := by
    simp only [Pi.add_apply]
    rw [show (∑ k, W k * ((x k + y k) * a k))
          = (∑ k, W k * (x k * a k)) + (∑ k, W k * (y k * a k)) by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring]
    ring
  map_smul' r x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [show (∑ k, W k * ((r * x k) * a k)) = r * ∑ k, W k * (x k * a k) by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring]
    ring_nf

def owR33_formP (p : ℕ) (W : Fin 3 → ZMod p) (b v : Fin 3 → ZMod p) : Fin 3 → ZMod p :=
  v - (owR33_alphaLinP p W b v) • b

theorem owR33_alpha_self {p : ℕ} (W : Fin 3 → ZMod p) (y : Fin 3 → ZMod p)
    (hy : (∑ k, W k * (y k * y k)) = 1) :
    owR33_alphaLinP p W y y = 2 := by
  show (2 * (1 : ZMod p)⁻¹) * ∑ k, W k * (y k * y k) = 2
  rw [hy, mul_one]
  simp

theorem owR33_formP_norm {p : ℕ} (W : Fin 3 → ZMod p) (y z : Fin 3 → ZMod p)
    (hy : (∑ k, W k * (y k * y k)) = 1)
    (hz : (∑ k, W k * (z k * z k)) = 1) :
    ∑ k, W k * (owR33_formP p W y z k * owR33_formP p W y z k) = 1 := by
  set A : ZMod p := owR33_alphaLinP p W y z with hA
  have hAval : A = (2 * (1 : ZMod p)⁻¹) * ∑ k, W k * (z k * y k) := by
    rw [hA]; rfl
  have hform : ∀ k, owR33_formP p W y z k = z k - A * y k := by
    intro k
    simp only [owR33_formP, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hA]
  calc ∑ k, W k * (owR33_formP p W y z k * owR33_formP p W y z k)
      = ∑ k, W k * ((z k - A * y k) * (z k - A * y k)) := by
        apply Finset.sum_congr rfl; intro k _; rw [hform k]
    _ = ∑ k, (W k * (z k * z k) - (2 * A) * (W k * (z k * y k))
          + (A * A) * (W k * (y k * y k))) := by
        apply Finset.sum_congr rfl; intro k _; ring
    _ = (∑ k, W k * (z k * z k)) - (2 * A) * (∑ k, W k * (z k * y k))
          + (A * A) * (∑ k, W k * (y k * y k)) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = 1 := by
        rw [hz, hy, hAval]
        simp
        ring

theorem owR33_bilin {p : ℕ} (W : Fin 3 → ZMod p) (b : Fin 3 → ZMod p)
    (hb : (∑ k, W k * (b k * b k)) = 1) (v x : Fin 3 → ZMod p) :
    ∑ k, W k * (owR33_formP p W b v k * x k)
      = ∑ k, W k * (v k * owR33_formP p W b x k) := by
  simp only [owR33_formP, owR33_alphaLinP, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  simp only [Fin.sum_univ_three]
  ring

theorem owR33_alpha_conj {p : ℕ} (W : Fin 3 → ZMod p) (b : Fin 3 → ZMod p)
    (hb : (∑ k, W k * (b k * b k)) = 1) (v x : Fin 3 → ZMod p) :
    owR33_alphaLinP p W (owR33_formP p W b x) v
      = owR33_alphaLinP p W x (owR33_formP p W b v) := by
  simp only [owR33_alphaLinP, LinearMap.coe_mk, AddHom.coe_mk]
  rw [owR33_bilin W b hb v x]

theorem owR33_r_congr {p : ℕ} (W : Fin 3 → ZMod p) (x y : Fin 3 → ZMod p)
    (hx : (∑ k, W k * (x k * x k)) = 1) (hy : (∑ k, W k * (y k * y k)) = 1) (h : x = y) :
    Module.reflection (f := owR33_alphaLinP p W x) (x := x) (owR33_alpha_self W x hx)
      = Module.reflection (f := owR33_alphaLinP p W y) (x := y) (owR33_alpha_self W y hy) := by
  subst h
  rfl

theorem owR33_reflP_conj {p : ℕ} (W : Fin 3 → ZMod p) (b x : Fin 3 → ZMod p)
    (hb : (∑ k, W k * (b k * b k)) = 1) (hx : (∑ k, W k * (x k * x k)) = 1) :
    Module.reflection (f := owR33_alphaLinP p W b) (x := b) (owR33_alpha_self W b hb)
      * Module.reflection (f := owR33_alphaLinP p W x) (x := x) (owR33_alpha_self W x hx)
      * (Module.reflection (f := owR33_alphaLinP p W b) (x := b) (owR33_alpha_self W b hb))⁻¹
    = Module.reflection (f := owR33_alphaLinP p W (owR33_formP p W b x))
        (x := owR33_formP p W b x)
        (owR33_alpha_self W (owR33_formP p W b x) (owR33_formP_norm W b x hb hx)) := by
  ext v
  rw [Module.reflection_apply (x := owR33_formP p W b x)
    (f := owR33_alphaLinP p W (owR33_formP p W b x))
    (h := owR33_alpha_self W (owR33_formP p W b x) (owR33_formP_norm W b x hb hx)) (y := v)]
  simp only [LinearEquiv.mul_apply, Module.reflection_inv]
  rw [owR33_alpha_conj W b hb v x]
  have h1 : Module.reflection (f := owR33_alphaLinP p W x) (x := x) (owR33_alpha_self W x hx)
        (Module.reflection (f := owR33_alphaLinP p W b) (x := b) (owR33_alpha_self W b hb) v)
      = Module.reflection (f := owR33_alphaLinP p W b) (x := b) (owR33_alpha_self W b hb) v
        - owR33_alphaLinP p W x
            (Module.reflection (f := owR33_alphaLinP p W b) (x := b) (owR33_alpha_self W b hb) v)
          • x :=
    Module.reflection_apply (x := x) (f := owR33_alphaLinP p W x)
      (h := owR33_alpha_self W x hx)
      (y := Module.reflection (f := owR33_alphaLinP p W b) (x := b) (owR33_alpha_self W b hb) v)
  have h2 : Module.reflection (f := owR33_alphaLinP p W b) (x := b) (owR33_alpha_self W b hb)
        (Module.reflection (f := owR33_alphaLinP p W b) (x := b) (owR33_alpha_self W b hb) v) = v :=
    Module.involutive_reflection (owR33_alpha_self W b hb) v
  rw [h1, map_sub, map_smul, h2]
  simp only [owR33_formP, Module.reflection_apply]

theorem owR33_alphaLinP_neg {p : ℕ} (W : Fin 3 → ZMod p) (y : Fin 3 → ZMod p) :
    owR33_alphaLinP p W (-y) = -owR33_alphaLinP p W y := by
  ext v
  simp [owR33_alphaLinP, Finset.sum_neg_distrib, mul_neg, neg_mul]

theorem owR33_refl_neg {p : ℕ} (W : Fin 3 → ZMod p) (y : Fin 3 → ZMod p)
    (hy : (∑ k, W k * (y k * y k)) = 1) :
    Module.reflection (f := owR33_alphaLinP p W (-y)) (x := -y)
        (owR33_alpha_self W (-y) (by
          simpa only [Pi.neg_apply, neg_mul, mul_neg, neg_neg] using hy))
      = Module.reflection (f := owR33_alphaLinP p W y) (x := y) (owR33_alpha_self W y hy) := by
  have hα := owR33_alphaLinP_neg W y
  ext v
  simp only [Module.reflection_apply]
  rw [show owR33_alphaLinP p W (-y) v = -owR33_alphaLinP p W y v from by rw [hα]; rfl]
  simp only [neg_smul, smul_neg, neg_neg]

theorem owR33_alphaVal_eq (W : Fin 3 → ZMod 3) (a v : Fin 3 → ZMod 3) :
    owR33_alphaVal W a v = owR33_alphaLinP 3 W a v := by
  simp only [owR33_alphaVal, owR33_alphaLinP, LinearMap.coe_mk, AddHom.coe_mk, ZMod.inv_one]
  ring

theorem owR33_form_eq (W : Fin 3 → ZMod 3) (a v : Fin 3 → ZMod 3) :
    owR33_form W a v = owR33_formP 3 W a v := by
  simp only [owR33_form, owR33_formP, owR33_alphaVal_eq]

theorem owR33_bridge {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (W : Fin 3 → ZMod p)
    (A : Fin 3 → Fin 3 → ZMod p) (X : Fin 6 → Fin 3 → ZMod p)
    (hnorm : ∀ i, ∑ k, W k * (A i k * A i k) = 1)
    (hbase : X 0 = A 0 ∧ X 1 = A 1 ∧ X 2 = A 2)
    (hchain : X 3 = owR33_formP p W (A 1) (X 0) ∧
      X 4 = owR33_formP p W (A 2) (X 1) ∧ X 5 = owR33_formP p W (A 2) (X 3))
    (hcover : ∀ y : Fin 3 → ZMod p, (∑ k, W k * (y k * y k)) = 1 →
      ∃ k : Fin 6, y = X k ∨ y = -X k)
    (hP : ∀ i j, owR33_alphaLinP p W (A i) (A j) = (CartanMatrix.A 3 i j : ZMod p)) :
    LinWeyl p (closure (ClassRefl p (owR33_Qw p 3 W) 1)) := by
  classical
  let s : Fin 3 → (Fin 3 → ZMod p) ≃ₗ[ZMod p] (Fin 3 → ZMod p) :=
    fun i => Module.reflection (f := owR33_alphaLinP p W (A i)) (x := A i)
      (owR33_alpha_self W (A i) (hnorm i))
  have hs : ∀ i v, s i v = v - owR33_alphaLinP p W (A i) v • A i := by
    intro i v
    exact Module.reflection_apply (x := A i) (f := owR33_alphaLinP p W (A i))
      (h := owR33_alpha_self W (A i) (hnorm i)) (y := v)
  have hone : (1 : ZMod p) ≠ 0 := by
    intro h
    exact hp.not_dvd_one ((ZMod.natCast_eq_zero_iff 1 p).mp (by simpa using h))
  have hs_mem : ∀ i, s i ∈ ClassRefl p (owR33_Qw p 3 W) 1 := by
    intro i
    rw [show owR33_Qw p 3 W = QuadraticMap.weightedSumSquares (ZMod p) W from rfl]
    rw [wit_coord_classRefl_iff hp hp2 W 1 hone]
    exact ⟨A i, hnorm i, fun v => by rw [hs i v]; rfl⟩
  have h0 : (∑ k, W k * (X 0 k * X 0 k)) = 1 := by rw [hbase.1]; exact hnorm 0
  have h1 : (∑ k, W k * (X 1 k * X 1 k)) = 1 := by rw [hbase.2.1]; exact hnorm 1
  have h2 : (∑ k, W k * (X 2 k * X 2 k)) = 1 := by rw [hbase.2.2]; exact hnorm 2
  have h3 : (∑ k, W k * (X 3 k * X 3 k)) = 1 := by
    rw [hchain.1]; exact owR33_formP_norm W (A 1) (X 0) (hnorm 1) h0
  have h4 : (∑ k, W k * (X 4 k * X 4 k)) = 1 := by
    rw [hchain.2.1]; exact owR33_formP_norm W (A 2) (X 1) (hnorm 2) h1
  have h5 : (∑ k, W k * (X 5 k * X 5 k)) = 1 := by
    rw [hchain.2.2]; exact owR33_formP_norm W (A 2) (X 3) (hnorm 2) h3
  have hXn : ∀ k : Fin 6, (∑ j, W j * (X k j * X k j)) = 1 := by
    intro k; fin_cases k
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  let H : Subgroup ((Fin 3 → ZMod p) ≃ₗ[ZMod p] (Fin 3 → ZMod p)) := closure (Set.range s)
  have hsH : ∀ i, s i ∈ H := fun i => Subgroup.subset_closure ⟨i, rfl⟩
  have hm0 : Module.reflection (f := owR33_alphaLinP p W (X 0)) (x := X 0)
      (owR33_alpha_self W (X 0) (hXn 0)) ∈ H := by
    rw [owR33_r_congr W (X 0) (A 0) (hXn 0) (hnorm 0) hbase.1]; exact hsH 0
  have hm1 : Module.reflection (f := owR33_alphaLinP p W (X 1)) (x := X 1)
      (owR33_alpha_self W (X 1) (hXn 1)) ∈ H := by
    rw [owR33_r_congr W (X 1) (A 1) (hXn 1) (hnorm 1) hbase.2.1]; exact hsH 1
  have hm2 : Module.reflection (f := owR33_alphaLinP p W (X 2)) (x := X 2)
      (owR33_alpha_self W (X 2) (hXn 2)) ∈ H := by
    rw [owR33_r_congr W (X 2) (A 2) (hXn 2) (hnorm 2) hbase.2.2]; exact hsH 2
  have hm3 : Module.reflection (f := owR33_alphaLinP p W (X 3)) (x := X 3)
      (owR33_alpha_self W (X 3) (hXn 3)) ∈ H := by
    rw [owR33_r_congr W (X 3) (owR33_formP p W (A 1) (X 0)) (hXn 3)
      (owR33_formP_norm W (A 1) (X 0) (hnorm 1) h0) hchain.1,
      ← owR33_reflP_conj W (A 1) (X 0) (hnorm 1) h0,
      owR33_r_congr W (X 0) (X 0) h0 (hXn 0) rfl]
    exact H.mul_mem (H.mul_mem (hsH 1) hm0) (H.inv_mem (hsH 1))
  have hm4 : Module.reflection (f := owR33_alphaLinP p W (X 4)) (x := X 4)
      (owR33_alpha_self W (X 4) (hXn 4)) ∈ H := by
    rw [owR33_r_congr W (X 4) (owR33_formP p W (A 2) (X 1)) (hXn 4)
      (owR33_formP_norm W (A 2) (X 1) (hnorm 2) h1) hchain.2.1,
      ← owR33_reflP_conj W (A 2) (X 1) (hnorm 2) h1,
      owR33_r_congr W (X 1) (X 1) h1 (hXn 1) rfl]
    exact H.mul_mem (H.mul_mem (hsH 2) hm1) (H.inv_mem (hsH 2))
  have hm5 : Module.reflection (f := owR33_alphaLinP p W (X 5)) (x := X 5)
      (owR33_alpha_self W (X 5) (hXn 5)) ∈ H := by
    rw [owR33_r_congr W (X 5) (owR33_formP p W (A 2) (X 3)) (hXn 5)
      (owR33_formP_norm W (A 2) (X 3) (hnorm 2) h3) hchain.2.2,
      ← owR33_reflP_conj W (A 2) (X 3) (hnorm 2) h3,
      owR33_r_congr W (X 3) (X 3) h3 (hXn 3) rfl]
    exact H.mul_mem (H.mul_mem (hsH 2) hm3) (H.inv_mem (hsH 2))
  have hXmem : ∀ k : Fin 6, Module.reflection (f := owR33_alphaLinP p W (X k)) (x := X k)
      (owR33_alpha_self W (X k) (hXn k)) ∈ H := by
    intro k; fin_cases k <;> assumption
  have hgen : closure (Set.range s) = closure (ClassRefl p (owR33_Qw p 3 W) 1) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact Subgroup.subset_closure (hs_mem i)
    · rw [Subgroup.closure_le]
      intro t ht
      rw [show owR33_Qw p 3 W = QuadraticMap.weightedSumSquares (ZMod p) W from rfl] at ht
      rw [wit_coord_classRefl_iff hp hp2 W 1 hone] at ht
      obtain ⟨a, ha, hta⟩ := ht
      have hra : t = Module.reflection (f := owR33_alphaLinP p W a) (x := a)
          (owR33_alpha_self W a ha) := by
        ext v; rw [hta v]; rfl
      obtain ⟨k, hk | hk⟩ := hcover a ha
      · rw [hra, owR33_r_congr W a (X k) ha (hXn k) hk]; exact hXmem k
      · have hneg : Module.reflection (f := owR33_alphaLinP p W a) (x := a)
            (owR33_alpha_self W a ha)
            = Module.reflection (f := owR33_alphaLinP p W (X k)) (x := X k)
              (owR33_alpha_self W (X k) (hXn k)) := by
          rw [owR33_r_congr W a (-X k) ha (by rw [← hk]; exact ha) hk]
          exact owR33_refl_neg W (X k) (hXn k)
        rw [hra, hneg]; exact hXmem k
  exact owTA_linWeyl_of_typeA hp hp2 (owR33_Qw p 3 W) 1 (by norm_num : 3 ≤ 3)
    A (fun i => owR33_alphaLinP p W (A i)) hP s hs hs_mem hgen

theorem owR33_weyl112 : LinWeyl 3 (closure (ClassRefl 3 (owR33_Qw 3 3 owR33_W112) 1)) := by
  obtain ⟨hnorm, hbase, hchain, hcover, hcart⟩ := owR33_data112
  refine owR33_bridge (p := 3) (by norm_num) (by norm_num) owR33_W112 owR33_A112 owR33_X112
    hnorm hbase ?_ hcover ?_
  · exact ⟨by rw [← owR33_form_eq]; exact hchain.1,
      by rw [← owR33_form_eq]; exact hchain.2.1,
      by rw [← owR33_form_eq]; exact hchain.2.2⟩
  · intro i j; rw [← owR33_alphaVal_eq]; exact hcart i j

theorem owR33_weyl121 : LinWeyl 3 (closure (ClassRefl 3 (owR33_Qw 3 3 owR33_W121) 1)) := by
  obtain ⟨hnorm, hbase, hchain, hcover, hcart⟩ := owR33_data121
  refine owR33_bridge (p := 3) (by norm_num) (by norm_num) owR33_W121 owR33_A121 owR33_X121
    hnorm hbase ?_ hcover ?_
  · exact ⟨by rw [← owR33_form_eq]; exact hchain.1,
      by rw [← owR33_form_eq]; exact hchain.2.1,
      by rw [← owR33_form_eq]; exact hchain.2.2⟩
  · intro i j; rw [← owR33_alphaVal_eq]; exact hcart i j

theorem owR33_weyl211 : LinWeyl 3 (closure (ClassRefl 3 (owR33_Qw 3 3 owR33_W211) 1)) := by
  obtain ⟨hnorm, hbase, hchain, hcover, hcart⟩ := owR33_data211
  refine owR33_bridge (p := 3) (by norm_num) (by norm_num) owR33_W211 owR33_A211 owR33_X211
    hnorm hbase ?_ hcover ?_
  · exact ⟨by rw [← owR33_form_eq]; exact hchain.1,
      by rw [← owR33_form_eq]; exact hchain.2.1,
      by rw [← owR33_form_eq]; exact hchain.2.2⟩
  · intro i j; rw [← owR33_alphaVal_eq]; exact hcart i j

theorem owR33_weyl222 : LinWeyl 3 (closure (ClassRefl 3 (owR33_Qw 3 3 owR33_W222) 1)) := by
  obtain ⟨hnorm, hbase, hchain, hcover, hcart⟩ := owR33_data222
  refine owR33_bridge (p := 3) (by norm_num) (by norm_num) owR33_W222 owR33_A222 owR33_X222
    hnorm hbase ?_ hcover ?_
  · exact ⟨by rw [← owR33_form_eq]; exact hchain.1,
      by rw [← owR33_form_eq]; exact hchain.2.1,
      by rw [← owR33_form_eq]; exact hchain.2.2⟩
  · intro i j; rw [← owR33_alphaVal_eq]; exact hcart i j

theorem owR33_coord_linWeyl {p d : ℕ} (hp : p.Prime) (hp3 : p = 3) (hd : d = 3)
    {w : Fin d → ZMod p} (hw : ∀ i, w i ≠ 0) (c : ZMod p) (hc : c ≠ 0)
    (hai : AbsIrred p (closure (ClassRefl p (owR33_Qw p d w) c))) :
    LinWeyl p (closure (ClassRefl p (owR33_Qw p d w) c)) := by
  subst d
  subst p
  rw [← owR33_classRefl_scale3 w c hc] at hai ⊢
  have hc1 : c * c⁻¹ = 1 := by
    have h : ∀ c : ZMod 3, c ≠ 0 → c * c⁻¹ = 1 := by decide +kernel
    exact h c hc
  have hw' : ∀ i, c⁻¹ * w i ≠ 0 := by
    intro i h
    have h2 : c * (c⁻¹ * w i) = 0 := by rw [h, mul_zero]
    rw [← mul_assoc, hc1, one_mul] at h2
    exact hw i h2
  set w' : Fin 3 → ZMod 3 := fun i => c⁻¹ * w i with hw'def
  have hw'' : ∀ i, w' i ≠ 0 := by intro i; rw [hw'def]; exact hw' i
  rcases owR33_w_cases w' hw'' with h | h | h | h | h | h | h | h
  · rw [h] at hai ⊢; exfalso; exact owR33_red111_absurd hai
  · rw [h] at ⊢; exact owR33_weyl112
  · rw [h] at ⊢; exact owR33_weyl121
  · rw [h] at hai ⊢; exfalso; exact owR33_red122_absurd hai
  · rw [h] at ⊢; exact owR33_weyl211
  · rw [h] at hai ⊢; exfalso; exact owR33_red212_absurd hai
  · rw [h] at hai ⊢; exfalso; exact owR33_red221_absurd hai
  · rw [h] at ⊢; exact owR33_weyl222

end CFSG.StandardType.ZS

end
