module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUReduceVRefl
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallBridge
import CFSG.LocalAnalysis.StandardType.GGQTwoReflLin
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.StandardType.HdRo7D

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU CFSG.StandardType.HdRo7SU.Small
open CFSG.RankThree.PartOne.ReflF

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7DRedUAux_two_ne_zero : (2 : ZMod 3) ≠ 0 := by decide

private lemma hdRo7DRedUAux_eq_one_or_neg_one (x : ZMod 3) (hx : x ≠ 0) :
    x = 1 ∨ x = -1 := by
  decide +revert

private lemma hdRo7DRedUAux_sq_eq_one (x : ZMod 3) (hx : x ≠ 0) : x * x = 1 := by
  decide +revert

private lemma hdRo7DRedUAux_mul_eq_one_or_neg_one {a b : ZMod 3}
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) : a * b = 1 ∨ a * b = -1 := by
  decide +revert

private lemma hdRo7DRedUAux_dsp_apply_zero {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} {b : Module.Basis (Fin (n + 1)) (ZMod p) V}
    {a : V ≃ₗ[ZMod p] V} (ha : DSP p b a) : a (b 0) = b 0 := by
  obtain ⟨σ, c, hσ0, hc0, -, -, happly⟩ := ha
  rw [happly 0, hσ0, hc0, one_smul]

private noncomputable def hdRo7DRedUAux_signChangeLin {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    (T : Finset (Fin m)) : V →ₗ[ZMod 3] V :=
  b.constr (ZMod 3) fun j => if j ∈ T then -b j else b j

private lemma hdRo7DRedUAux_signChangeLin_involutive {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    (T : Finset (Fin m)) :
    Function.Involutive (hdRo7DRedUAux_signChangeLin b T) := by
  have hS : ∀ j, hdRo7DRedUAux_signChangeLin b T (b j) =
      if j ∈ T then -b j else b j := fun j =>
    Module.Basis.constr_basis b (ZMod 3) (fun j => if j ∈ T then -b j else b j) j
  have hcomp : (hdRo7DRedUAux_signChangeLin b T).comp
      (hdRo7DRedUAux_signChangeLin b T) = LinearMap.id := by
    apply b.ext
    intro j
    rw [LinearMap.comp_apply, LinearMap.id_apply, hS j]
    by_cases hj : j ∈ T
    · rw [if_pos hj, map_neg, hS j, if_pos hj, neg_neg]
    · rw [if_neg hj, hS j, if_neg hj]
  intro x
  have hx := congrArg (fun L : V →ₗ[ZMod 3] V => L x) hcomp
  simpa [LinearMap.comp_apply] using hx

private noncomputable def hdRo7DRedUAux_signChange {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    (T : Finset (Fin m)) : V ≃ₗ[ZMod 3] V :=
  LinearEquiv.ofInvolutive (hdRo7DRedUAux_signChangeLin b T)
    (hdRo7DRedUAux_signChangeLin_involutive b T)

private lemma hdRo7DRedUAux_signChange_apply {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    (T : Finset (Fin m)) (j : Fin m) :
    hdRo7DRedUAux_signChange b T (b j) = if j ∈ T then -b j else b j := by
  simp only [hdRo7DRedUAux_signChange, LinearEquiv.coe_ofInvolutive,
    hdRo7DRedUAux_signChangeLin]
  rw [Module.Basis.constr_basis]

private lemma hdRo7DRedUAux_signChange_mul_self {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    (T : Finset (Fin m)) :
    hdRo7DRedUAux_signChange b T * hdRo7DRedUAux_signChange b T = 1 := by
  apply LinearEquiv.ext
  intro v
  change hdRo7DRedUAux_signChange b T (hdRo7DRedUAux_signChange b T v) = v
  simp only [hdRo7DRedUAux_signChange, LinearEquiv.coe_ofInvolutive]
  exact hdRo7DRedUAux_signChangeLin_involutive b T v

private lemma hdRo7DRedUAux_signChange_coord_term {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    (T : Finset (Fin m)) (v : V) (i j : Fin m) :
    b.coord i (hdRo7DRedUAux_signChange b T ((b.repr v) j • b j)) =
      (if i = j then (if i ∈ T then -1 else 1) * b.repr v j else 0) := by
  rw [Module.Basis.coord_apply, map_smul, map_smul]
  rw [Finsupp.smul_apply, hdRo7DRedUAux_signChange_apply]
  by_cases hji : i = j
  · subst hji
    by_cases hiT : i ∈ T
    · rw [if_pos hiT, if_pos rfl, if_pos hiT]
      rw [show -b i = (-1 : ZMod 3) • b i from (neg_one_smul _ _).symm]
      rw [map_smul, b.repr_self, Finsupp.smul_single, Finsupp.single_eq_same]
      simp only [smul_eq_mul]
      ring
    · rw [if_neg hiT, if_pos rfl, if_neg hiT]
      rw [b.repr_self, Finsupp.single_eq_same]
      simp [smul_eq_mul]
  · rw [if_neg hji]
    by_cases hjT : j ∈ T
    · rw [if_pos hjT]
      rw [show -b j = (-1 : ZMod 3) • b j from (neg_one_smul _ _).symm]
      rw [map_smul, b.repr_self, Finsupp.smul_single, Finsupp.single_eq_of_ne hji]
      simp
    · rw [if_neg hjT, b.repr_self, Finsupp.single_eq_of_ne hji]
      simp

private lemma hdRo7DRedUAux_coord_signChange {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    (T : Finset (Fin m)) (v : V) (i : Fin m) :
    b.coord i (hdRo7DRedUAux_signChange b T v) =
      (if i ∈ T then -1 else 1) * b.coord i v := by
  conv_lhs => rw [← b.sum_repr v]
  rw [map_sum]
  rw [map_sum]
  simp only [hdRo7DRedUAux_signChange_coord_term]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, Module.Basis.coord_apply]
  · intro j _ hji
    rw [if_neg (Ne.symm hji)]
  · intro h
    exact absurd (Finset.mem_univ i) h

private lemma hdRo7DRedUAux_coord_signChange_neg {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    (T : Finset (Fin m)) (v : V) (hT : ∀ i, b.coord i v ≠ 0 → i ∈ T) (i : Fin m) :
    b.coord i (hdRo7DRedUAux_signChange b T v) = -b.coord i v := by
  rw [hdRo7DRedUAux_coord_signChange]
  by_cases hi : i ∈ T
  · rw [if_pos hi]
    ring
  · have h0 : b.coord i v = 0 := by
      by_contra hne
      exact hi (hT i hne)
    rw [if_neg hi, h0, mul_zero, neg_zero]

private lemma hdRo7DRedUAux_signChange_apply_neg {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    (T : Finset (Fin m)) (v : V) (hT : ∀ i, b.coord i v ≠ 0 → i ∈ T) :
    hdRo7DRedUAux_signChange b T v = -v := by
  apply b.ext_elem
  intro i
  rw [map_neg, Finsupp.neg_apply]
  simpa only [Module.Basis.coord_apply] using
    hdRo7DRedUAux_coord_signChange_neg b T v hT i

private theorem hdRo7DRedUAux_signChange_dsp {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (T : Finset (Fin (n + 1))) (h0T : (0 : Fin (n + 1)) ∉ T) (hTeven : T.card % 2 = 0) :
    DSP 3 b (hdRo7DRedUAux_signChange b T) := by
  classical
  refine ⟨1, fun j => if j ∈ T then -1 else 1, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp [h0T]
  · intro j
    by_cases hj : j ∈ T <;> simp [hj]
  · have hprod : (∏ j, (if j ∈ T then (-1 : ZMod 3) else 1)) = (-1) ^ T.card := by
      rw [Fintype.prod_extend_by_one T (fun _ => (-1 : ZMod 3)), Finset.prod_const]
    rw [hprod]
    exact Even.neg_one_pow (Nat.even_iff.mpr hTeven)
  · intro j
    rw [hdRo7DRedUAux_signChange_apply]
    by_cases hj : j ∈ T <;> simp [hj]

private noncomputable def hdRo7DRedUAux_signedSwapLin {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    (i j : Fin m) (ε : ZMod 3) : V →ₗ[ZMod 3] V :=
  b.constr (ZMod 3) fun k =>
    if k = i then ε • b j else if k = j then ε • b i else b k

private lemma hdRo7DRedUAux_signedSwapLin_involutive {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    {i j : Fin m} (hij : i ≠ j) {ε : ZMod 3} (hε : ε * ε = 1) :
    Function.Involutive (hdRo7DRedUAux_signedSwapLin b i j ε) := by
  have hS : ∀ k, hdRo7DRedUAux_signedSwapLin b i j ε (b k) =
      if k = i then ε • b j else if k = j then ε • b i else b k := fun k =>
    Module.Basis.constr_basis b (ZMod 3)
      (fun k => if k = i then ε • b j else if k = j then ε • b i else b k) k
  have hcomp : (hdRo7DRedUAux_signedSwapLin b i j ε).comp
      (hdRo7DRedUAux_signedSwapLin b i j ε) = LinearMap.id := by
    apply b.ext
    intro k
    rw [LinearMap.comp_apply, LinearMap.id_apply, hS k]
    by_cases hki : k = i
    · rw [if_pos hki, map_smul, hS j, if_neg (fun h : j = i => hij h.symm), if_pos rfl,
        smul_smul, hε, one_smul, hki]
    · by_cases hkj : k = j
      · rw [if_neg hki, if_pos hkj, map_smul, hS i, if_pos rfl, smul_smul, hε, one_smul,
          hkj]
      · rw [if_neg hki, if_neg hkj, hS k, if_neg hki, if_neg hkj]
  intro x
  have hx := congrArg (fun L : V →ₗ[ZMod 3] V => L x) hcomp
  simpa [LinearMap.comp_apply] using hx

private noncomputable def hdRo7DRedUAux_signedSwap {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    {i j : Fin m} (hij : i ≠ j) (ε : ZMod 3) (hε : ε * ε = 1) : V ≃ₗ[ZMod 3] V :=
  LinearEquiv.ofInvolutive (hdRo7DRedUAux_signedSwapLin b i j ε)
    (hdRo7DRedUAux_signedSwapLin_involutive b hij hε)

private lemma hdRo7DRedUAux_signedSwap_apply {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    {i j : Fin m} (hij : i ≠ j) {ε : ZMod 3} (hε : ε * ε = 1) (k : Fin m) :
    hdRo7DRedUAux_signedSwap b hij ε hε (b k) =
      if k = i then ε • b j else if k = j then ε • b i else b k := by
  simp only [hdRo7DRedUAux_signedSwap, LinearEquiv.coe_ofInvolutive,
    hdRo7DRedUAux_signedSwapLin]
  rw [Module.Basis.constr_basis]

private theorem hdRo7DRedUAux_signedSwap_reflData {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    {i j : Fin m} (hij : i ≠ j) {ε : ZMod 3} (hε : ε * ε = 1) :
    ReflData (hdRo7DRedUAux_signedSwap b hij ε hε) (b i - ε • b j)
      (b.coord i - ε • b.coord j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    have h := congrArg (b.coord i) hzero
    simp only [map_sub, map_smul, hdRo7SUReduceVAux_coord_basis b i i,
      hdRo7SUReduceVAux_coord_basis b i j, if_neg hij, smul_zero,
      sub_zero, map_zero] at h
    exact one_ne_zero h
  · simp only [LinearMap.sub_apply, map_sub, map_smul, LinearMap.smul_apply,
      hdRo7SUReduceVAux_coord_basis b i i,
      hdRo7SUReduceVAux_coord_basis b j i, hdRo7SUReduceVAux_coord_basis b i j,
      hdRo7SUReduceVAux_coord_basis b j j, if_neg hij, if_neg hij.symm,
      zero_sub, smul_eq_mul]
    ring_nf
    rw [pow_two, hε]
    norm_num
  · intro v
    have hlin : (hdRo7DRedUAux_signedSwap b hij ε hε).toLinearMap =
        LinearMap.id - (b.coord i - ε • b.coord j).smulRight (b i - ε • b j) := by
      apply b.ext
      intro k
      rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
        LinearMap.sub_apply, LinearMap.smul_apply]
      change hdRo7DRedUAux_signedSwap b hij ε hε (b k) =
        b k - ((b.coord i - ε • b.coord j) (b k)) • (b i - ε • b j)
      rw [hdRo7DRedUAux_signedSwap_apply b hij hε k]
      by_cases hki : k = i
      · rw [hki, if_pos rfl]
        rw [LinearMap.sub_apply, LinearMap.smul_apply,
          hdRo7SUReduceVAux_coord_basis b i i, hdRo7SUReduceVAux_coord_basis b j i,
          if_pos rfl, if_neg hij.symm, smul_zero, sub_zero, one_smul]
        abel
      · by_cases hkj : k = j
        · rw [hkj, if_neg (fun h : j = i => hij h.symm), if_pos rfl]
          rw [LinearMap.sub_apply, LinearMap.smul_apply,
            hdRo7SUReduceVAux_coord_basis b i j, hdRo7SUReduceVAux_coord_basis b j j,
            if_neg hij, if_pos rfl, zero_sub, neg_smul]
          simp only [smul_eq_mul, mul_one, sub_neg_eq_add, smul_sub, smul_smul, hε]
          module
        · rw [if_neg hki, if_neg hkj]
          rw [LinearMap.sub_apply, LinearMap.smul_apply,
            hdRo7SUReduceVAux_coord_basis b i k, hdRo7SUReduceVAux_coord_basis b j k,
            if_neg (fun h : i = k => hki h.symm), if_neg (fun h : j = k => hkj h.symm),
            smul_zero, sub_zero, zero_smul, sub_zero]
    have h := congrArg (fun L : V →ₗ[ZMod 3] V => L v) hlin
    simpa [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply] using h

private theorem hdRo7DRedUAux_signedSwap_dsp {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    {i j : Fin (n + 1)} (hi0 : i ≠ 0) (hj0 : j ≠ 0) (hij : i ≠ j) {ε : ZMod 3}
    (hεsq : ε * ε = 1) (hε : ε = 1 ∨ ε = -1) :
    DSP 3 b (hdRo7DRedUAux_signedSwap b hij ε hεsq) := by
  refine ⟨Equiv.swap i j, fun k => if k = i then ε else if k = j then ε else 1,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hi0) (Ne.symm hj0)]
  · simp [Ne.symm hi0, Ne.symm hj0]
  · intro k
    by_cases hki : k = i
    · simp [hki, hε]
    · by_cases hkj : k = j
      · simp [hkj, hε]
      · simp [hki, hkj]
  · have hsupp : ∀ x, x ∉ ({i, j} : Finset (Fin (n + 1))) →
        (if x = i then ε else if x = j then ε else 1) = 1 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      simp [hx.1, hx.2]
    have hprod : (∏ k, (if k = i then ε else if k = j then ε else 1)) = ε * ε := by
      rw [← Finset.prod_subset (s₁ := ({i, j} : Finset (Fin (n + 1))))
        (s₂ := Finset.univ) (by simp) (fun x _ hx => hsupp x hx)]
      rw [Finset.prod_pair hij]
      simp
    rw [hprod]
    exact hεsq
  · intro k
    rw [hdRo7DRedUAux_signedSwap_apply b hij hεsq]
    change (if k = i then ε • b j else if k = j then ε • b i else b k) =
      (if k = i then ε else if k = j then ε else 1) • b (Equiv.swap i j k)
    by_cases hki : k = i
    · subst hki
      rw [if_pos rfl, if_pos rfl, Equiv.swap_apply_left]
    · by_cases hkj : k = j
      · subst hkj
        rw [if_neg hki, if_pos rfl, if_neg hki, if_pos rfl, Equiv.swap_apply_right]
      · rw [if_neg hki, if_neg hkj, if_neg hki, if_neg hkj,
          Equiv.swap_apply_of_ne_of_ne hki hkj, one_smul]

private lemma hdRo7DRedUAux_root_mem_move {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {r : V ≃ₗ[ZMod 3] V} {h : V} {φ : V →ₗ[ZMod 3] ZMod 3}
    (hr : ReflData r h φ) : h ∈ ggLinMove (p := 3) r := by
  refine LinearMap.mem_range.mpr ⟨h, ?_⟩
  rw [LinearMap.sub_apply, LinearEquiv.coe_toLinearMap, hr.apply h, hr.pair]
  have h2 : (2 : ZMod 3) = -1 := by decide
  rw [h2, neg_smul]
  module

private theorem hdRo7DRedUAux_eq_form_of_same_root {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hNoT : ∀ a ∈ A, ¬ C2Transv (p := 3) a)
    {r s : V ≃ₗ[ZMod 3] V} {u : V} {φ ψ : V →ₗ[ZMod 3] ZMod 3}
    (hr : ReflData r u φ) (hs : ReflData s u ψ) (hrA : r ∈ A) (hsA : s ∈ A) :
    φ = ψ := by
  by_contra hne
  have hr' : r = Module.reflection hr.pair := LinearEquiv.ext fun v => by
    rw [hr.apply v, Module.reflection_apply]
  have hs' : s = Module.reflection hs.pair := LinearEquiv.ext fun v => by
    rw [hs.apply v, Module.reflection_apply]
  have htv := QTwoLin.transvection_of_same_centre (K := ZMod 3) hr.pair hs.pair hne
  refine hNoT (s * r) (A.mul_mem hsA hrA) (c2Transv_of_isTransvectionLin (s * r) ?_)
  simpa only [hr', hs'] using htv

private theorem hdRo7DRedUAux_phi_axis_of_neg {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {n : ℕ}
    {b : Module.Basis (Fin (n + 1)) (ZMod 3) V} {H A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hD : DLinData 3 n V b H A)
    {r : V ≃ₗ[ZMod 3] V} {h : V} {φ : V →ₗ[ZMod 3] ZMod 3}
    (hr : ReflData r h φ) (hrH : r ∈ H)
    {w : V ≃ₗ[ZMod 3] V} (hwDSP : DSP 3 b w) (hwh : w h = -h) :
    φ (b 0) = 0 := by
  have hwH : w ∈ H := hD.hPH w hwDSP
  have hw0 : w (b 0) = b 0 := hdRo7DRedUAux_dsp_apply_zero hwDSP
  have hws0 : w.symm (b 0) = b 0 := by
    apply w.injective
    rw [w.apply_symm_apply, hw0]
  have hconj : ReflData (w * r * w⁻¹) (w h) (φ ∘ₗ (w.symm : V →ₗ[ZMod 3] V)) :=
    hr.conj w
  rw [hwh] at hconj
  have hconj' : ReflData (w * r * w⁻¹) h (-(φ ∘ₗ (w.symm : V →ₗ[ZMod 3] V))) := by
    simpa using hconj.neg
  have hwA : w * r * w⁻¹ ∈ A :=
    A.mul_mem (A.mul_mem (hD.hHA hwH) (hD.hHA hrH)) (A.inv_mem (hD.hHA hwH))
  have hrA : r ∈ A := hD.hHA hrH
  have heq : φ = -(φ ∘ₗ (w.symm : V →ₗ[ZMod 3] V)) :=
    hdRo7DRedUAux_eq_form_of_same_root hD.hNoT hr hconj' hrA hwA
  have h0 : φ (b 0) = -φ (b 0) := by
    have h := congrArg (fun f : V →ₗ[ZMod 3] ZMod 3 => f (b 0)) heq
    simpa [hws0] using h
  have h2 : (2 : ZMod 3) * φ (b 0) = 0 := by
    have h1 := congrArg (fun y : ZMod 3 => y + φ (b 0)) h0
    simpa [two_mul] using h1
  exact (mul_eq_zero.mp h2).resolve_left hdRo7DRedUAux_two_ne_zero

private theorem hdRo7DRedUAux_mul_phi_eq {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {n : ℕ}
    {b : Module.Basis (Fin (n + 1)) (ZMod 3) V} {H A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hD : DLinData 3 n V b H A)
    {r : V ≃ₗ[ZMod 3] V} {h : V} {φ : V →ₗ[ZMod 3] ZMod 3}
    (hr : ReflData r h φ) (hrH : r ∈ H)
    {i j : Fin (n + 1)} (hi0 : i ≠ 0) (hj0 : j ≠ 0) (hij : i ≠ j)
    (hi : b.coord i h ≠ 0) (hj : b.coord j h ≠ 0) :
    b.coord i h * φ (b i) = b.coord j h * φ (b j) := by
  let ε : ZMod 3 := b.coord i h * b.coord j h
  have hε1 : ε = 1 ∨ ε = -1 :=
    hdRo7DRedUAux_mul_eq_one_or_neg_one
      (hdRo7DRedUAux_eq_one_or_neg_one _ hi) (hdRo7DRedUAux_eq_one_or_neg_one _ hj)
  have hεsq : ε * ε = 1 := by rcases hε1 with h | h <;> rw [h] <;> norm_num
  have hψh : (b.coord i - ε • b.coord j) h = 0 := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    dsimp only [ε]
    rw [show b.coord i h * b.coord j h * b.coord j h =
        b.coord i h * (b.coord j h * b.coord j h) by ring,
      hdRo7DRedUAux_sq_eq_one _ hj]
    ring
  have htdata : ReflData (hdRo7DRedUAux_signedSwap b hij ε hεsq) (b i - ε • b j)
      (b.coord i - ε • b.coord j) :=
    hdRo7DRedUAux_signedSwap_reflData b hij hεsq
  have htDSP : DSP 3 b (hdRo7DRedUAux_signedSwap b hij ε hεsq) :=
    hdRo7DRedUAux_signedSwap_dsp b hi0 hj0 hij hεsq hε1
  have htH : hdRo7DRedUAux_signedSwap b hij ε hεsq ∈ H := hD.hPH _ htDSP
  have htA : hdRo7DRedUAux_signedSwap b hij ε hεsq ∈ A := hD.hHA htH
  have hrA : r ∈ A := hD.hHA hrH
  have hzero : φ (b i - ε • b j) = 0 :=
    (hdRo7SUReduceVAux_zero_pair_iff hD.hNoT hr htdata hrA htA).mpr hψh
  have hrel : φ (b i) = ε * φ (b j) := by
    have h := hzero
    rw [map_sub, map_smul, smul_eq_mul] at h
    exact sub_eq_zero.mp h
  calc b.coord i h * φ (b i) = b.coord i h * (ε * φ (b j)) := by rw [hrel]
    _ = (b.coord i h * b.coord i h) * (b.coord j h * φ (b j)) := by
        dsimp only [ε]; ring
    _ = b.coord j h * φ (b j) := by
        rw [hdRo7DRedUAux_sq_eq_one _ hi, one_mul]

private theorem hdRo7DRedUAux_phi_axis_of_even {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {n : ℕ}
    {b : Module.Basis (Fin (n + 1)) (ZMod 3) V} {H A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hD : DLinData 3 n V b H A) (hneven : n % 2 = 0)
    {r : V ≃ₗ[ZMod 3] V} {h : V} {φ : V →ₗ[ZMod 3] ZMod 3}
    (hr : ReflData r h φ) (hrH : r ∈ H) (hhU : b.coord 0 h = 0) :
    φ (b 0) = 0 := by
  let T : Finset (Fin (n + 1)) := Finset.univ.erase 0
  have h0T : (0 : Fin (n + 1)) ∉ T := Finset.notMem_erase _ _
  have hcard : T.card = n := by
    dsimp only [T]
    rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin (n + 1))),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hTeven : T.card % 2 = 0 := by rw [hcard]; exact hneven
  have hsupp : ∀ i, b.coord i h ≠ 0 → i ∈ T := by
    intro i hi
    dsimp only [T]
    rw [Finset.mem_erase]
    exact ⟨fun h0 => hi (by rw [h0]; exact hhU), Finset.mem_univ i⟩
  exact hdRo7DRedUAux_phi_axis_of_neg hD hr hrH
    (hdRo7DRedUAux_signChange_dsp b T h0T hTeven)
    (hdRo7DRedUAux_signChange_apply_neg b T h hsupp)

private theorem hdRo7DRedUAux_phi_axis_of_zero_coord {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {n : ℕ}
    {b : Module.Basis (Fin (n + 1)) (ZMod 3) V} {H A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hD : DLinData 3 n V b H A)
    {r : V ≃ₗ[ZMod 3] V} {h : V} {φ : V →ₗ[ZMod 3] ZMod 3}
    (hr : ReflData r h φ) (hrH : r ∈ H) (hhU : b.coord 0 h = 0)
    {k : Fin (n + 1)} (hk0 : k ≠ 0) (hk : b.coord k h = 0) :
    φ (b 0) = 0 := by
  classical
  let T0 : Finset (Fin (n + 1)) := Finset.univ.filter (fun i => b.coord i h ≠ 0)
  have h0T0 : (0 : Fin (n + 1)) ∉ T0 := by
    simpa [T0] using hhU
  have hkT0 : k ∉ T0 := by
    simpa [T0] using hk
  have hT0supp : ∀ i, b.coord i h ≠ 0 → i ∈ T0 := by
    intro i hi
    simpa [T0] using hi
  let T : Finset (Fin (n + 1)) := if T0.card % 2 = 0 then T0 else insert k T0
  have h0T : (0 : Fin (n + 1)) ∉ T := by
    by_cases hc : T0.card % 2 = 0
    · simp [T, hc, h0T0]
    · simp [T, hc, h0T0, Ne.symm hk0]
  have hTeven : T.card % 2 = 0 := by
    by_cases hc : T0.card % 2 = 0
    · simp [T, hc]
    · have hc1 : T0.card % 2 = 1 := by omega
      dsimp only [T]
      rw [if_neg hc, Finset.card_insert_of_notMem hkT0]
      omega
  have hsupp : ∀ i, b.coord i h ≠ 0 → i ∈ T := by
    intro i hi
    have hiT0 : i ∈ T0 := hT0supp i hi
    by_cases hc : T0.card % 2 = 0
    · simp [T, hc, hiT0]
    · simp [T, hc, hiT0]
  exact hdRo7DRedUAux_phi_axis_of_neg hD hr hrH
    (hdRo7DRedUAux_signChange_dsp b T h0T hTeven)
    (hdRo7DRedUAux_signChange_apply_neg b T h hsupp)

private theorem hdRo7DRedUAux_full_support_data {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {n : ℕ}
    {b : Module.Basis (Fin (n + 1)) (ZMod 3) V} {H A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hD : DLinData 3 n V b H A) (hn : 6 ≤ n)
    {r : V ≃ₗ[ZMod 3] V} {h : V} {φ : V →ₗ[ZMod 3] ZMod 3}
    (hr : ReflData r h φ) (hrH : r ∈ H) (hhU : b.coord 0 h = 0)
    (hfull : ∀ i : Fin (n + 1), i ≠ 0 → b.coord i h ≠ 0) :
    ∃ μ : ZMod 3, (∀ i, i ≠ 0 → φ (b i) = μ * b.coord i h) ∧
      (2 : ZMod 3) = (n : ZMod 3) * μ := by
  let i1 : Fin (n + 1) := ⟨1, by omega⟩
  have hi10 : i1 ≠ 0 := by
    intro h0
    have h := congrArg Fin.val h0
    simp [i1] at h
  let μ : ZMod 3 := b.coord i1 h * φ (b i1)
  have hmul : ∀ i, i ≠ 0 → b.coord i h * φ (b i) = μ := by
    intro i hi0
    by_cases hi1 : i = i1
    · subst hi1
      rfl
    · exact hdRo7DRedUAux_mul_phi_eq hD hr hrH hi0 hi10 hi1 (hfull i hi0) (hfull i1 hi10)
  have hφ : ∀ i, i ≠ 0 → φ (b i) = μ * b.coord i h := by
    intro i hi0
    have hμ := hmul i hi0
    have hsq := hdRo7DRedUAux_sq_eq_one (b.coord i h) (hfull i hi0)
    calc φ (b i) = (b.coord i h * b.coord i h) * φ (b i) := by rw [hsq, one_mul]
      _ = b.coord i h * (b.coord i h * φ (b i)) := by ring
      _ = b.coord i h * μ := by rw [hμ]
      _ = μ * b.coord i h := by ring
  have hmap : φ h = ∑ i : Fin (n + 1), b.coord i h * φ (b i) := by
    conv_lhs => rw [← b.sum_repr h]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, ← Module.Basis.coord_apply, smul_eq_mul]
  have hterm : ∀ i, b.coord i h * φ (b i) = if i = 0 then (0 : ZMod 3) else μ := by
    intro i
    by_cases hi0 : i = 0
    · subst hi0
      rw [hhU, zero_mul]
      simp
    · rw [if_neg hi0]
      exact hmul i hi0
  let S : Finset (Fin (n + 1)) := Finset.univ.erase 0
  have hScard : S.card = n := by
    dsimp only [S]
    rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin (n + 1))),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hsplit : (∑ i : Fin (n + 1), b.coord i h * φ (b i)) = ∑ i ∈ S, μ := by
    rw [← Finset.add_sum_erase Finset.univ (fun i => b.coord i h * φ (b i))
      (Finset.mem_univ (0 : Fin (n + 1)))]
    have hf0 : b.coord 0 h * φ (b 0) = 0 := by rw [hhU, zero_mul]
    rw [hf0, zero_add]
    apply Finset.sum_congr rfl
    intro i hi
    have hi0 : i ≠ 0 := by simpa [S] using hi
    exact hmul i hi0
  have hsumS : (∑ i ∈ S, μ) = (n : ZMod 3) * μ := by
    rw [Finset.sum_const, hScard, nsmul_eq_mul]
  refine ⟨μ, hφ, ?_⟩
  calc (2 : ZMod 3) = φ h := hr.pair.symm
    _ = ∑ i : Fin (n + 1), b.coord i h * φ (b i) := hmap
    _ = ∑ i ∈ S, μ := hsplit
    _ = (n : ZMod 3) * μ := hsumS

private theorem hdRo7DRedUAux_axis_of_mod_one {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {n : ℕ}
    {b : Module.Basis (Fin (n + 1)) (ZMod 3) V} {H A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hD : DLinData 3 n V b H A) (hn : 6 ≤ n)
    {r : V ≃ₗ[ZMod 3] V} {h : V} {φ : V →ₗ[ZMod 3] ZMod 3}
    (hr : ReflData r h φ) (hrH : r ∈ H) (hhU : b.coord 0 h = 0)
    (hfull : ∀ i : Fin (n + 1), i ≠ 0 → b.coord i h ≠ 0)
    {μ : ZMod 3} (hφμ : ∀ i, i ≠ 0 → φ (b i) = μ * b.coord i h)
    (hμ : μ = 2) :
    φ (b 0) = 0 := by
  let i1 : Fin (n + 1) := ⟨1, by omega⟩
  let i2 : Fin (n + 1) := ⟨2, by omega⟩
  have hi10 : i1 ≠ 0 := by
    intro h0
    have h := congrArg Fin.val h0
    simp [i1] at h
  have hi20 : i2 ≠ 0 := by
    intro h0
    have h := congrArg Fin.val h0
    simp [i2] at h
  have hi12 : i1 ≠ i2 := by
    intro h0
    have h := congrArg Fin.val h0
    simp [i1, i2] at h
  let ε : ZMod 3 := b.coord i1 h * b.coord i2 h
  have hε1 : ε = 1 ∨ ε = -1 :=
    hdRo7DRedUAux_mul_eq_one_or_neg_one
      (hdRo7DRedUAux_eq_one_or_neg_one _ (hfull i1 hi10))
      (hdRo7DRedUAux_eq_one_or_neg_one _ (hfull i2 hi20))
  let ε' : ZMod 3 := -ε
  have hε'1 : ε' = 1 ∨ ε' = -1 := by
    rcases hε1 with h | h
    · right
      dsimp only [ε']
      rw [h]
    · left
      dsimp only [ε']
      rw [h]
      norm_num
  have hε'sq : ε' * ε' = 1 := by rcases hε'1 with h | h <;> rw [h] <;> norm_num
  let t : V ≃ₗ[ZMod 3] V := hdRo7DRedUAux_signedSwap b hi12 ε' hε'sq
  have htdata : ReflData t (b i1 - ε' • b i2) (b.coord i1 - ε' • b.coord i2) :=
    hdRo7DRedUAux_signedSwap_reflData b hi12 hε'sq
  have htDSP : DSP 3 b t :=
    hdRo7DRedUAux_signedSwap_dsp b hi10 hi20 hi12 hε'sq hε'1
  have htH : t ∈ H := hD.hPH t htDSP
  let g : V := b i1 - ε' • b i2
  have hg : g = b i1 + ε • b i2 := by
    dsimp only [g, ε']
    rw [neg_smul, sub_neg_eq_add]
  have hφg : φ g = b.coord i1 h := by
    have h2sq : b.coord i2 h * b.coord i2 h = 1 :=
      hdRo7DRedUAux_sq_eq_one _ (hfull i2 hi20)
    rw [hg, map_add, map_smul, hφμ i1 hi10, hφμ i2 hi20, smul_eq_mul, hμ]
    dsimp only [ε]
    rw [show (b.coord i1 h * b.coord i2 h) * (2 * b.coord i2 h) =
        2 * b.coord i1 h by
      linear_combination (2 * b.coord i1 h) * h2sq]
    have h3 : (3 : ZMod 3) = 0 := CharP.cast_eq_zero (ZMod 3) 3
    have h4 : (2 : ZMod 3) + 2 = 1 := by linear_combination h3
    rw [show (2 : ZMod 3) * b.coord i1 h + 2 * b.coord i1 h =
      ((2 : ZMod 3) + 2) * b.coord i1 h by ring, h4, one_mul]
  have hr_inv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr.mul_self
  have hr_symm : r.symm = r := by
    apply LinearEquiv.ext
    intro v
    apply r.injective
    rw [r.apply_symm_apply]
    have h := congrArg (fun e : V ≃ₗ[ZMod 3] V => e v) hr.mul_self
    simpa using h.symm
  have hconj : ReflData (r * t * r) (r g)
      ((b.coord i1 - ε' • b.coord i2) ∘ₗ (r : V →ₗ[ZMod 3] V)) := by
    have h := htdata.conj r
    simpa [g, hr_inv, hr_symm, map_sub, map_smul] using h
  have hg0 : b.coord 0 g = 0 := by
    rw [hg, map_add, map_smul, smul_eq_mul]
    rw [hdRo7SUReduceVAux_coord_basis b 0 i1, hdRo7SUReduceVAux_coord_basis b 0 i2,
      if_neg (Ne.symm hi10), if_neg (Ne.symm hi20)]
    simp
  have hroot0 : b.coord 0 (r g) = 0 := by
    rw [hr.apply g, map_sub, map_smul, smul_eq_mul, hg0, hhU, mul_zero, sub_zero]
  have hg1 : b.coord i1 g = 1 := by
    rw [hg, map_add, map_smul, smul_eq_mul]
    rw [hdRo7SUReduceVAux_coord_basis b i1 i1, hdRo7SUReduceVAux_coord_basis b i1 i2,
      if_pos rfl, if_neg hi12]
    simp
  have hroot1 : b.coord i1 (r g) = 0 := by
    rw [hr.apply g, map_sub, map_smul, smul_eq_mul, hg1, hφg]
    rw [hdRo7DRedUAux_sq_eq_one _ (hfull i1 hi10), sub_self]
  have hmem : r * t * r ∈ H := H.mul_mem (H.mul_mem hrH htH) hrH
  have hzero := hdRo7DRedUAux_phi_axis_of_zero_coord hD hconj hmem hroot0 hi10 hroot1
  have hψ0 : (b.coord i1 - ε' • b.coord i2) (b 0) = 0 := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hdRo7SUReduceVAux_coord_basis b i1 0, hdRo7SUReduceVAux_coord_basis b i2 0,
      if_neg hi10, if_neg hi20]
    simp
  have hψh : (b.coord i1 - ε' • b.coord i2) h = 2 * b.coord i1 h := by
    have h2sq : b.coord i2 h * b.coord i2 h = 1 :=
      hdRo7DRedUAux_sq_eq_one _ (hfull i2 hi20)
    rw [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    dsimp only [ε', ε]
    rw [show (-(b.coord i1 h * b.coord i2 h)) * b.coord i2 h =
        -b.coord i1 h by
      linear_combination (-(b.coord i1 h)) * h2sq]
    ring
  have hval : (b.coord i1 - ε' • b.coord i2) (r (b 0)) =
      φ (b 0) * b.coord i1 h := by
    rw [hr.apply (b 0), map_sub, map_smul, smul_eq_mul, hψ0, hψh]
    have h3 : (3 : ZMod 3) = 0 := CharP.cast_eq_zero (ZMod 3) 3
    linear_combination (-(φ (b 0) * b.coord i1 h)) * h3
  have hzero' : (b.coord i1 - ε' • b.coord i2) (r (b 0)) = 0 := by
    simpa [LinearMap.comp_apply] using hzero
  rw [hval] at hzero'
  exact (mul_eq_zero.mp hzero').resolve_right (hfull i1 hi10)

private lemma hdRo7DRedUAux_T6_inj {n : ℕ} (hn : 6 ≤ n) :
    Function.Injective (fun k : Fin 6 => (⟨k.val + 1, by omega⟩ : Fin (n + 1))) := by
  intro a b hab
  have h := congrArg Fin.val hab
  simp at h
  exact Fin.ext h

private noncomputable def hdRo7DRedUAux_T6 {n : ℕ} (hn : 6 ≤ n) : Finset (Fin (n + 1)) :=
  Finset.univ.map ⟨fun k : Fin 6 => (⟨k.val + 1, by omega⟩ : Fin (n + 1)),
    hdRo7DRedUAux_T6_inj hn⟩

private lemma hdRo7DRedUAux_T6_card {n : ℕ} (hn : 6 ≤ n) :
    (hdRo7DRedUAux_T6 hn).card = 6 := by
  dsimp only [hdRo7DRedUAux_T6]
  rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]

private lemma hdRo7DRedUAux_T6_zero_notMem {n : ℕ} (hn : 6 ≤ n) :
    (0 : Fin (n + 1)) ∉ hdRo7DRedUAux_T6 hn := by
  intro hmem
  dsimp only [hdRo7DRedUAux_T6] at hmem
  obtain ⟨k, -, hk⟩ := Finset.mem_map.mp hmem
  have h := congrArg Fin.val hk
  simp at h

private lemma hdRo7DRedUAux_T6_even {n : ℕ} (hn : 6 ≤ n) :
    (hdRo7DRedUAux_T6 hn).card % 2 = 0 := by
  rw [hdRo7DRedUAux_T6_card hn]

private lemma hdRo7DRedUAux_T6_one_mem {n : ℕ} (hn : 6 ≤ n) :
    (⟨1, by omega⟩ : Fin (n + 1)) ∈ hdRo7DRedUAux_T6 hn := by
  dsimp only [hdRo7DRedUAux_T6]
  refine Finset.mem_map.mpr ⟨(⟨0, by norm_num⟩ : Fin 6), Finset.mem_univ _, ?_⟩
  apply Fin.ext
  simp

private lemma hdRo7DRedUAux_T6_sum {n : ℕ} (hn : 6 ≤ n) {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {b : Module.Basis (Fin (n + 1)) (ZMod 3) V} (h : V)
    (φ : V →ₗ[ZMod 3] ZMod 3) {μ : ZMod 3}
    (hμterm : ∀ i, i ≠ 0 → b.coord i h * φ (b i) = μ) :
    (∑ i ∈ hdRo7DRedUAux_T6 hn, b.coord i h * φ (b i)) = 6 * μ := by
  dsimp only [hdRo7DRedUAux_T6]
  rw [Finset.sum_map]
  change (∑ k : Fin 6,
      b.coord (⟨k.val + 1, by omega⟩ : Fin (n + 1)) h *
        φ (b (⟨k.val + 1, by omega⟩ : Fin (n + 1)))) = 6 * μ
  have hterm : ∀ k : Fin 6,
      b.coord (⟨k.val + 1, by omega⟩ : Fin (n + 1)) h *
        φ (b (⟨k.val + 1, by omega⟩ : Fin (n + 1))) = μ := by
    intro k
    apply hμterm
    intro hk
    have h := congrArg Fin.val hk
    simp at h
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num

private lemma hdRo7DRedUAux_phi_signChange_six {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {n : ℕ} {b : Module.Basis (Fin (n + 1)) (ZMod 3) V}
    (hn : 6 ≤ n) {r : V ≃ₗ[ZMod 3] V} {h : V} {φ : V →ₗ[ZMod 3] ZMod 3}
    (hr : ReflData r h φ) {μ : ZMod 3}
    (hμterm : ∀ i, i ≠ 0 → b.coord i h * φ (b i) = μ) :
    φ (hdRo7DRedUAux_signChange b (hdRo7DRedUAux_T6 hn) h) = 2 := by
  let T := hdRo7DRedUAux_T6 hn
  let h' := hdRo7DRedUAux_signChange b T h
  have hcoord : ∀ i, b.coord i h' = (if i ∈ T then -1 else 1) * b.coord i h :=
    fun i => hdRo7DRedUAux_coord_signChange b T h i
  have hmap' : φ h' = ∑ i : Fin (n + 1), b.coord i h' * φ (b i) := by
    conv_lhs => rw [← b.sum_repr h']
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, ← Module.Basis.coord_apply, smul_eq_mul]
  have hmap : φ h = ∑ i : Fin (n + 1), b.coord i h * φ (b i) := by
    conv_lhs => rw [← b.sum_repr h]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, ← Module.Basis.coord_apply, smul_eq_mul]
  have hsplit : (∑ i : Fin (n + 1), b.coord i h' * φ (b i)) =
      (∑ i : Fin (n + 1), b.coord i h * φ (b i)) -
        2 * (∑ i ∈ T, b.coord i h * φ (b i)) := by
    have hpoint : ∀ i, b.coord i h' * φ (b i) =
        b.coord i h * φ (b i) -
          2 * (if i ∈ T then b.coord i h * φ (b i) else 0) := by
      intro i
      rw [hcoord i]
      by_cases hi : i ∈ T <;> (simp [hi]; try ring)
    rw [Finset.sum_congr rfl (fun i _ => hpoint i), Finset.sum_sub_distrib]
    congr 1
    calc (∑ i : Fin (n + 1), 2 * (if i ∈ T then b.coord i h * φ (b i) else 0))
        = ∑ i : Fin (n + 1),
            (if i ∈ T then 2 * (b.coord i h * φ (b i)) else 0) := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : i ∈ T <;> simp [hi]
      _ = ∑ i ∈ T, 2 * (b.coord i h * φ (b i)) +
            ∑ i ∈ Tᶜ, (0 : ZMod 3) := by
          rw [Finset.sum_ite]
          simp
      _ = 2 * ∑ i ∈ T, b.coord i h * φ (b i) := by
          rw [Finset.sum_const_zero, add_zero, Finset.mul_sum]
  have hTsum : (∑ i ∈ T, b.coord i h * φ (b i)) = 6 * μ := hdRo7DRedUAux_T6_sum hn h φ hμterm
  calc φ h' = ∑ i : Fin (n + 1), b.coord i h' * φ (b i) := hmap'
    _ = (∑ i : Fin (n + 1), b.coord i h * φ (b i)) - 2 * (∑ i ∈ T, b.coord i h * φ (b i)) :=
        hsplit
    _ = φ h - 2 * (6 * μ) := by rw [← hmap, hTsum]
    _ = 2 - 2 * (6 * μ) := by rw [hr.pair]
    _ = 2 := by
        have h12 : (2 : ZMod 3) * (6 * μ) = 0 := by
          have h12' : (2 : ZMod 3) * (6 * μ) = (12 : ZMod 3) * μ := by ring
          rw [h12']
          have h3 : (3 : ZMod 3) = 0 := CharP.cast_eq_zero (ZMod 3) 3
          have h12'' : (12 : ZMod 3) = 0 := by linear_combination 4 * h3
          rw [h12'', zero_mul]
        rw [h12, sub_zero]

private lemma hdRo7DRedUAux_mul_phi_of_phi_eq {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {n : ℕ} {b : Module.Basis (Fin (n + 1)) (ZMod 3) V}
    {h : V} {φ : V →ₗ[ZMod 3] ZMod 3} {μ : ZMod 3}
    (hfull : ∀ i : Fin (n + 1), i ≠ 0 → b.coord i h ≠ 0)
    (hφμ : ∀ i, i ≠ 0 → φ (b i) = μ * b.coord i h) :
    ∀ i, i ≠ 0 → b.coord i h * φ (b i) = μ := by
  intro i hi0
  calc b.coord i h * φ (b i) = b.coord i h * (μ * b.coord i h) := by
        rw [hφμ i hi0]
    _ = μ * (b.coord i h * b.coord i h) := by ring
    _ = μ * 1 := by rw [hdRo7DRedUAux_sq_eq_one _ (hfull i hi0)]
    _ = μ := by ring

private theorem hdRo7DRedUAux_axis_of_mod_two {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {n : ℕ}
    {b : Module.Basis (Fin (n + 1)) (ZMod 3) V} {H A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hD : DLinData 3 n V b H A) (hn : 6 ≤ n)
    {r : V ≃ₗ[ZMod 3] V} {h : V} {φ : V →ₗ[ZMod 3] ZMod 3}
    (hr : ReflData r h φ) (hrH : r ∈ H) (hhU : b.coord 0 h = 0)
    (hfull : ∀ i : Fin (n + 1), i ≠ 0 → b.coord i h ≠ 0)
    {μ : ZMod 3} (hφμ : ∀ i, i ≠ 0 → φ (b i) = μ * b.coord i h) :
    φ (b 0) = 0 := by
  let i1 : Fin (n + 1) := ⟨1, by omega⟩
  have hi10 : i1 ≠ 0 := by
    intro h0
    have h := congrArg Fin.val h0
    simp [i1] at h
  let T := hdRo7DRedUAux_T6 hn
  let w : V ≃ₗ[ZMod 3] V := hdRo7DRedUAux_signChange b T
  have hwDSP : DSP 3 b w :=
    hdRo7DRedUAux_signChange_dsp b T (hdRo7DRedUAux_T6_zero_notMem hn)
      (hdRo7DRedUAux_T6_even hn)
  have hwH : w ∈ H := hD.hPH w hwDSP
  have hw0 : w (b 0) = b 0 := hdRo7DRedUAux_dsp_apply_zero hwDSP
  have hw_sq : w * w = 1 := hdRo7DRedUAux_signChange_mul_self b T
  have hw_inv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw_sq
  have hw_symm : w.symm = w := by
    apply LinearEquiv.ext
    intro v
    apply w.injective
    rw [w.apply_symm_apply]
    have h := congrArg (fun e : V ≃ₗ[ZMod 3] V => e v) hw_sq
    simpa using h.symm
  let h' : V := w h
  have hcong : ReflData (w * r * w) h' (φ ∘ₗ (w : V →ₗ[ZMod 3] V)) := by
    have h := hr.conj w
    simpa [h', hw_inv, hw_symm] using h
  have hμterm : ∀ i, i ≠ 0 → b.coord i h * φ (b i) = μ :=
    hdRo7DRedUAux_mul_phi_of_phi_eq hfull hφμ
  have hφh' : φ h' = 2 := hdRo7DRedUAux_phi_signChange_six hn hr hμterm
  let r' : V ≃ₗ[ZMod 3] V := w * r * w
  have hr_inv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr.mul_self
  have hr_symm : r.symm = r := by
    apply LinearEquiv.ext
    intro v
    apply r.injective
    rw [r.apply_symm_apply]
    have hh := congrArg (fun e : V ≃ₗ[ZMod 3] V => e v) hr.mul_self
    simpa using hh.symm
  have hconj2 : ReflData (r * r' * r) (r h')
      ((φ ∘ₗ (w : V →ₗ[ZMod 3] V)) ∘ₗ (r : V →ₗ[ZMod 3] V)) := by
    have h := hcong.conj r
    simpa [r', hr_inv, hr_symm] using h
  have hroot_eq : r h' = h' + h := by
    rw [hr.apply h', hφh']
    have h2neg : (2 : ZMod 3) = -1 := by
      have h3 : (3 : ZMod 3) = 0 := CharP.cast_eq_zero (ZMod 3) 3
      calc (2 : ZMod 3) = 3 - 1 := by norm_num
        _ = 0 - 1 := by rw [h3]
        _ = -1 := by ring
    rw [h2neg, neg_smul, sub_neg_eq_add, one_smul]
  have hcoord0 : b.coord 0 h' = 0 := by
    rw [show h' = w h from rfl,
      hdRo7DRedUAux_coord_signChange b T h 0, if_neg (hdRo7DRedUAux_T6_zero_notMem hn)]
    simp [hhU]
  have hrootU : b.coord 0 (r h') = 0 := by
    rw [hroot_eq, map_add, hcoord0, hhU, add_zero]
  have hi1T : i1 ∈ T := hdRo7DRedUAux_T6_one_mem hn
  have hcoord1 : b.coord i1 h' = -b.coord i1 h := by
    rw [show h' = w h from rfl, hdRo7DRedUAux_coord_signChange b T h i1, if_pos hi1T,
      neg_one_mul]
  have hrootzero : b.coord i1 (r h') = 0 := by
    rw [hroot_eq, map_add, hcoord1]
    abel
  have hmem : r * r' * r ∈ H :=
    H.mul_mem (H.mul_mem hrH (H.mul_mem (H.mul_mem hwH hrH) hwH)) hrH
  have hzero := hdRo7DRedUAux_phi_axis_of_zero_coord hD hconj2 hmem hrootU hi10 hrootzero
  have hval : ((φ ∘ₗ (w : V →ₗ[ZMod 3] V)) ∘ₗ (r : V →ₗ[ZMod 3] V)) (b 0) =
      -φ (b 0) := by
    change φ (w (r (b 0))) = -φ (b 0)
    rw [hr.apply (b 0)]
    simp only [map_sub, map_smul, smul_eq_mul]
    rw [hw0, show w h = h' from rfl, hφh']
    ring
  rw [hval] at hzero
  exact neg_eq_zero.mp hzero

private theorem hdRo7DRedUAux_phi_axis_of_full_support {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {n : ℕ}
    {b : Module.Basis (Fin (n + 1)) (ZMod 3) V} {H A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hD : DLinData 3 n V b H A) (hn : 6 ≤ n)
    {r : V ≃ₗ[ZMod 3] V} {h : V} {φ : V →ₗ[ZMod 3] ZMod 3}
    (hr : ReflData r h φ) (hrH : r ∈ H) (hhU : b.coord 0 h = 0)
    (hfull : ∀ i : Fin (n + 1), i ≠ 0 → b.coord i h ≠ 0) :
    φ (b 0) = 0 := by
  obtain ⟨μ, hφμ, h2⟩ := hdRo7DRedUAux_full_support_data hD hn hr hrH hhU hfull
  have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2mod
  · have hcast : (n : ZMod 3) = 0 :=
      (ZMod.natCast_eq_zero_iff n 3).mpr (Nat.dvd_of_mod_eq_zero (m := 3) (n := n) h0)
    rw [hcast, zero_mul] at h2
    exact absurd h2 hdRo7DRedUAux_two_ne_zero
  · have hcast : (n : ZMod 3) = 1 := by
      have hm : n ≡ 1 [MOD 3] := by
        show n % 3 = 1 % 3
        rw [h1]
      have h := (ZMod.natCast_eq_natCast_iff' n 1 3).mpr hm
      simpa using h
    rw [hcast, one_mul] at h2
    exact hdRo7DRedUAux_axis_of_mod_one hD hn hr hrH hhU hfull hφμ h2.symm
  · exact hdRo7DRedUAux_axis_of_mod_two hD hn hr hrH hhU hfull hφμ

theorem d_reflFix_of_mem {p : ℕ} [Fact p.Prime] {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {b : Module.Basis (Fin (n + 1)) (ZMod p) V}
    {H A : Subgroup (V ≃ₗ[ZMod p] V)} (hD : DLinData p n V b H A) {r : V ≃ₗ[ZMod p] V}
    (hrH : r ∈ H) (hr : GGLinRefl r) (hU : ggLinMove r ≤ LinearMap.ker (b.coord 0)) :
    r (b 0) = b 0 := by
  obtain rfl := hD.hp
  have hn := hD.hn
  have hfin : Module.Finite (ZMod 3) V := Module.Finite.of_basis b
  obtain ⟨h, φ, hdata⟩ := hdRo7SUReduceVAux_reflData r hr
  have hhU : b.coord 0 h = 0 := hU (hdRo7DRedUAux_root_mem_move hdata)
  have hφ0 : φ (b 0) = 0 := by
    by_cases hneven : n % 2 = 0
    · exact hdRo7DRedUAux_phi_axis_of_even hD hneven hdata hrH hhU
    · by_cases hzero : ∃ k : Fin (n + 1), k ≠ 0 ∧ b.coord k h = 0
      · obtain ⟨k, hk0, hk⟩ := hzero
        exact hdRo7DRedUAux_phi_axis_of_zero_coord hD hdata hrH hhU hk0 hk
      · push Not at hzero
        exact hdRo7DRedUAux_phi_axis_of_full_support hD hn hdata hrH hhU hzero
  rw [hdata.apply (b 0), hφ0, zero_smul, sub_zero]

theorem d_reduceU_holds : DReduceULeaf := by
  intro p hpFact n V instAC instMod b H A hD hU
  obtain rfl := hD.hp
  obtain ⟨S, hS, hScl, -⟩ := hD.hgen
  have hfix : ∀ s ∈ S, s (b 0) = b 0 := fun s hs =>
    d_reflFix_of_mem hD (hS s hs).1 (hS s hs).2 (hU s (hS s hs).1 (hS s hs).2)
  let K : Subgroup (V ≃ₗ[ZMod 3] V) :=
    { carrier := {a | a (b 0) = b 0}
      one_mem' := rfl
      mul_mem' := by
        intro a c ha hc
        show (a * c) (b 0) = b 0
        rw [LinearEquiv.mul_apply, hc, ha]
      inv_mem' := by
        intro a ha
        change a.symm (b 0) = b 0
        apply a.injective
        rw [a.apply_symm_apply, ha] }
  have hSK : S ⊆ K := fun s hs => hfix s hs
  have hHK : H ≤ K := by
    rw [hScl]
    exact (Subgroup.closure_le K).mpr hSK
  intro a ha
  exact hHK ha

end CFSG.StandardType.HdRo7D
