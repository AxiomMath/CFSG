module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUReduceVIrrB
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBFrame
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.StandardType.HdRo7D

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU
open CFSG.RankThree.PartOne.ReflF

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7DIrrAux_two_ne_zero : (2 : ZMod 3) ≠ 0 := by decide

private lemma hdRo7DIrrAux_four_ne_zero : (4 : ZMod 3) ≠ 0 := by decide

private lemma hdRo7DIrrAux_one_ne_neg_one : (1 : ZMod 3) ≠ -1 := by decide

private lemma hdRo7DIrrAux_eq_one_or_neg_one (x : ZMod 3) (hx : x ≠ 0) :
    x = 1 ∨ x = -1 := by
  revert hx
  decide +revert

private lemma hdRo7DIrrAux_dsp_apply_zero {p : ℕ} {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] {m : ℕ} {b : Module.Basis (Fin (m + 1)) (ZMod p) W}
    {a : W ≃ₗ[ZMod p] W} (ha : DSP p b a) : a (b 0) = b 0 := by
  obtain ⟨σ, c, hσ0, hc0, -, -, happly⟩ := ha
  rw [happly 0, hσ0, hc0, one_smul]

private theorem hdRo7DIrrAux_dsp_mul {p : ℕ} {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] {m : ℕ} {b : Module.Basis (Fin (m + 1)) (ZMod p) W}
    {a q : W ≃ₗ[ZMod p] W} (ha : DSP p b a) (hq : DSP p b q) :
    DSP p b (a * q) := by
  obtain ⟨σ, c, hσ0, hc0, hc, hprod, hact⟩ := ha
  obtain ⟨τ, d, hτ0, hd0, hd, hdprod, hqact⟩ := hq
  refine ⟨σ * τ, fun i => d i * c (τ i), ?_, ?_, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, hτ0, hσ0]
  · show d 0 * c (τ 0) = 1
    rw [hτ0, hd0, hc0, mul_one]
  · intro i
    rcases hd i with h | h <;> rcases hc (τ i) with h' | h' <;> simp [h, h']
  · rw [Finset.prod_mul_distrib, hdprod]
    have hcomp : (∏ i, c (τ i)) = ∏ i, c i := Equiv.prod_comp τ c
    rw [hcomp, hprod, mul_one]
  · intro i
    rw [LinearEquiv.mul_apply, hqact i, map_smul, hact (τ i), smul_smul,
      Equiv.Perm.mul_apply]

private lemma hdRo7DIrrAux_perm_dsp {p : ℕ} {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] {m : ℕ} {b : Module.Basis (Fin (m + 1)) (ZMod p) W}
    (σ : Equiv.Perm (Fin (m + 1))) (hσ : σ 0 = 0) :
    DSP p b (b.equiv b σ) := by
  refine ⟨σ, fun _ => 1, hσ, rfl, fun i => Or.inl rfl, by simp, fun i => ?_⟩
  rw [Module.Basis.equiv_apply, one_smul]

section

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
  [Fact (Nat.Prime 3)] {b : Module.Basis (Fin (n + 1)) (ZMod 3) V}

private noncomputable def hdRo7DIrrAux_signChangeLin (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (T : Finset (Fin (n + 1))) : V →ₗ[ZMod 3] V :=
  b.constr (ZMod 3) fun j => if j ∈ T then -b j else b j

private lemma hdRo7DIrrAux_signChangeLin_involutive
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (T : Finset (Fin (n + 1))) :
    Function.Involutive (hdRo7DIrrAux_signChangeLin b T) := by
  have hS : ∀ j, hdRo7DIrrAux_signChangeLin b T (b j) =
      if j ∈ T then -b j else b j := fun j =>
    Module.Basis.constr_basis b (ZMod 3) (fun j => if j ∈ T then -b j else b j) j
  have hcomp : (hdRo7DIrrAux_signChangeLin b T).comp
      (hdRo7DIrrAux_signChangeLin b T) = LinearMap.id := by
    apply b.ext
    intro j
    rw [LinearMap.comp_apply, LinearMap.id_apply, hS j]
    by_cases hj : j ∈ T
    · rw [if_pos hj, map_neg, hS j, if_pos hj, neg_neg]
    · rw [if_neg hj, hS j, if_neg hj]
  intro x
  have hx := congrArg (fun L : V →ₗ[ZMod 3] V => L x) hcomp
  simpa [LinearMap.comp_apply] using hx

private noncomputable def hdRo7DIrrAux_signChange
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (T : Finset (Fin (n + 1))) :
    V ≃ₗ[ZMod 3] V :=
  LinearEquiv.ofInvolutive (hdRo7DIrrAux_signChangeLin b T)
    (hdRo7DIrrAux_signChangeLin_involutive b T)

private lemma hdRo7DIrrAux_signChange_apply
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (T : Finset (Fin (n + 1)))
    (j : Fin (n + 1)) :
    hdRo7DIrrAux_signChange b T (b j) = if j ∈ T then -b j else b j := by
  simp only [hdRo7DIrrAux_signChange, LinearEquiv.coe_ofInvolutive,
    hdRo7DIrrAux_signChangeLin]
  rw [Module.Basis.constr_basis]

private lemma hdRo7DIrrAux_coord_signChange
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (T : Finset (Fin (n + 1)))
    (v : V) (i : Fin (n + 1)) :
    b.coord i (hdRo7DIrrAux_signChange b T v) =
      (if i ∈ T then -1 else 1) * b.coord i v := by
  have hmap : (b.coord i).comp (hdRo7DIrrAux_signChange b T : V →ₗ[ZMod 3] V) =
      (if i ∈ T then -1 else 1) • b.coord i := by
    apply b.ext
    intro j
    simp only [LinearMap.comp_apply, LinearMap.smul_apply]
    by_cases hji : j = i
    · rw [hji]
      by_cases hi : i ∈ T <;>
        simp [hi, hdRo7DIrrAux_signChange_apply, map_neg]
    · have hij : i ≠ j := fun h => hji h.symm
      by_cases hj : j ∈ T <;>
        simp [hdRo7DIrrAux_signChange_apply, hij, hj]
  have h := congrArg (fun L : V →ₗ[ZMod 3] ZMod 3 => L v) hmap
  by_cases hi : i ∈ T
  · simpa [LinearMap.comp_apply, LinearMap.smul_apply, hi,
      Module.Basis.coord_apply] using h
  · simpa [LinearMap.comp_apply, LinearMap.smul_apply, hi,
      Module.Basis.coord_apply] using h

private theorem hdRo7DIrrAux_signChange_dsp
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (T : Finset (Fin (n + 1)))
    (h0T : (0 : Fin (n + 1)) ∉ T) (hTeven : T.card % 2 = 0) :
    DSP 3 b (hdRo7DIrrAux_signChange b T) := by
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
    rw [hdRo7DIrrAux_signChange_apply]
    by_cases hj : j ∈ T <;> simp [hj]

private noncomputable def hdRo7DIrrAux_signedSwapLin
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (i j : Fin (n + 1)) (ε : ZMod 3) :
    V →ₗ[ZMod 3] V :=
  b.constr (ZMod 3) fun k =>
    if k = i then ε • b j else if k = j then ε • b i else b k

private lemma hdRo7DIrrAux_signedSwapLin_involutive
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    {i j : Fin (n + 1)} (hij : i ≠ j) {ε : ZMod 3} (hε : ε * ε = 1) :
    Function.Involutive (hdRo7DIrrAux_signedSwapLin b i j ε) := by
  have hS : ∀ k, hdRo7DIrrAux_signedSwapLin b i j ε (b k) =
      if k = i then ε • b j else if k = j then ε • b i else b k := fun k =>
    Module.Basis.constr_basis b (ZMod 3)
      (fun k => if k = i then ε • b j else if k = j then ε • b i else b k) k
  have hcomp : (hdRo7DIrrAux_signedSwapLin b i j ε).comp
      (hdRo7DIrrAux_signedSwapLin b i j ε) = LinearMap.id := by
    apply b.ext
    intro k
    rw [LinearMap.comp_apply, LinearMap.id_apply, hS k]
    by_cases hki : k = i
    · rw [hki]
      simp [hS, Ne.symm hij, hε, smul_smul]
    · by_cases hkj : k = j
      · rw [hkj]
        simp [hS, Ne.symm hij, hε, smul_smul]
      · simp [hS, hki, hkj]
  intro x
  have hx := congrArg (fun L : V →ₗ[ZMod 3] V => L x) hcomp
  simpa [LinearMap.comp_apply] using hx

private noncomputable def hdRo7DIrrAux_signedSwap
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    {i j : Fin (n + 1)} (hij : i ≠ j) (ε : ZMod 3) (hε : ε * ε = 1) : V ≃ₗ[ZMod 3] V :=
  LinearEquiv.ofInvolutive (hdRo7DIrrAux_signedSwapLin b i j ε)
    (hdRo7DIrrAux_signedSwapLin_involutive b hij hε)

private lemma hdRo7DIrrAux_signedSwap_apply
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    {i j : Fin (n + 1)} (hij : i ≠ j) {ε : ZMod 3} (hε : ε * ε = 1)
    (k : Fin (n + 1)) :
    hdRo7DIrrAux_signedSwap b hij ε hε (b k) =
      if k = i then ε • b j else if k = j then ε • b i else b k := by
  simp only [hdRo7DIrrAux_signedSwap, LinearEquiv.coe_ofInvolutive,
    hdRo7DIrrAux_signedSwapLin]
  rw [Module.Basis.constr_basis]

private theorem hdRo7DIrrAux_signedSwap_reflData
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    {i j : Fin (n + 1)} (hij : i ≠ j) {ε : ZMod 3} (hε : ε * ε = 1) :
    ReflData (hdRo7DIrrAux_signedSwap b hij ε hε) (b i - ε • b j)
      (b.coord i - ε • b.coord j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    have h := congrArg (b.coord i) hzero
    rw [map_sub, map_smul, hdRo7SUReduceVAux_coord_basis b i i,
      hdRo7SUReduceVAux_coord_basis b i j, if_pos rfl, if_neg hij, smul_zero, map_zero,
      sub_zero] at h
    exact one_ne_zero h
  · simp [hij, hε]
    norm_num
  · intro v
    have hlin : (hdRo7DIrrAux_signedSwap b hij ε hε).toLinearMap =
        LinearMap.id - (b.coord i - ε • b.coord j).smulRight (b i - ε • b j) := by
      apply b.ext
      intro k
      rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
        LinearMap.sub_apply, LinearMap.smul_apply]
      change hdRo7DIrrAux_signedSwap b hij ε hε (b k) = _
      rw [hdRo7DIrrAux_signedSwap_apply b hij hε k]
      by_cases hki : k = i
      · rw [hki]
        simp [Ne.symm hij, smul_sub, smul_smul, smul_eq_mul]
      · by_cases hkj : k = j
        · rw [hkj]
          simp [Ne.symm hij, smul_sub, smul_smul, smul_eq_mul, hε]
        · simp [hki, hkj, smul_sub, smul_smul, smul_eq_mul]
    have h := congrArg (fun L : V →ₗ[ZMod 3] V => L v) hlin
    simpa [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply] using h

private theorem hdRo7DIrrAux_signedSwap_dsp
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    {i j : Fin (n + 1)} (hi0 : i ≠ 0) (hj0 : j ≠ 0) (hij : i ≠ j) {ε : ZMod 3}
    (hεsq : ε * ε = 1) (hε : ε = 1 ∨ ε = -1) :
    DSP 3 b (hdRo7DIrrAux_signedSwap b hij ε hεsq) := by
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
    rw [hdRo7DIrrAux_signedSwap_apply b hij hεsq]
    by_cases hki : k = i
    · subst hki
      rw [if_pos rfl]
      simp
    · by_cases hkj : k = j
      · subst hkj
        rw [if_neg hki]
        simp
      · rw [if_neg hki, if_neg hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]
        simp [hki, hkj]

private noncomputable def hdRo7DIrrAux_U
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) : Submodule (ZMod 3) V :=
  LinearMap.ker (b.coord 0)

private lemma hdRo7DIrrAux_z_not_mem_U (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) :
    b 0 ∉ hdRo7DIrrAux_U b := by
  rw [hdRo7DIrrAux_U, LinearMap.mem_ker, hdRo7SUReduceVAux_coord_basis b 0 0, if_pos rfl]
  exact one_ne_zero

private lemma hdRo7DIrrAux_diff_mem_U (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    {i j : Fin (n + 1)} (hi : i ≠ 0) (hj : j ≠ 0) :
    b i - b j ∈ hdRo7DIrrAux_U b := by
  rw [hdRo7DIrrAux_U, LinearMap.mem_ker, map_sub, hdRo7SUReduceVAux_coord_basis b 0 i,
    hdRo7SUReduceVAux_coord_basis b 0 j, if_neg (Ne.symm hi), if_neg (Ne.symm hj), sub_zero]

private lemma hdRo7DIrrAux_sum_mem_U (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    {i j : Fin (n + 1)} (hi : i ≠ 0) (hj : j ≠ 0) :
    b i + b j ∈ hdRo7DIrrAux_U b := by
  rw [hdRo7DIrrAux_U, LinearMap.mem_ker, map_add, hdRo7SUReduceVAux_coord_basis b 0 i,
    hdRo7SUReduceVAux_coord_basis b 0 j, if_neg (Ne.symm hi), if_neg (Ne.symm hj), add_zero]

private lemma hdRo7DIrrAux_sub_smul_mem_U (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (v : V) : v - b.coord 0 v • b 0 ∈ hdRo7DIrrAux_U b := by
  rw [hdRo7DIrrAux_U, LinearMap.mem_ker, map_sub, map_smul,
    hdRo7SUReduceVAux_coord_basis b 0 0, if_pos rfl]
  simp

private lemma hdRo7DIrrAux_dsp_mem_U
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) {a : V ≃ₗ[ZMod 3] V}
    (ha : DSP 3 b a) : ∀ u, u ∈ hdRo7DIrrAux_U b → a u ∈ hdRo7DIrrAux_U b := by
  obtain ⟨σ, c, hσ0, hc0, hc, hprod, hact⟩ := ha
  intro u hu
  have hu0 : b.coord 0 u = 0 := by
    rwa [hdRo7DIrrAux_U, LinearMap.mem_ker] at hu
  have hrepr : u = ∑ i, b.coord i u • b i := by
    simp [Module.Basis.coord_apply]
  rw [hrepr, map_sum]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : i = 0
  · subst hi
    rw [hu0, zero_smul, map_zero]
    exact (hdRo7DIrrAux_U b).zero_mem
  · rw [map_smul, hact i]
    have hσi : σ i ≠ 0 := fun h => hi (σ.injective (by rw [h, hσ0]))
    refine Submodule.smul_mem _ _ ?_
    rw [hdRo7DIrrAux_U, LinearMap.mem_ker, map_smul,
      hdRo7SUReduceVAux_coord_basis b 0 (σ i), if_neg (Ne.symm hσi)]
    simp

private theorem hdRo7DIrrAux_fixed (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (hn : 3 ≤ n) (v : V) (hv : ∀ a, DSP 3 b a → a v = v) :
    v ∈ Submodule.span (ZMod 3) {b 0} := by
  have hzero : ∀ i, i ≠ 0 → b.coord i v = 0 := by
    intro i hi
    obtain ⟨k, hk0, hki, -⟩ := exists_ne_zero_ne_ne hn i (0 : Fin (n + 1))
    have hik : i ≠ k := fun h => hki h.symm
    have hcard : ({i, k} : Finset (Fin (n + 1))).card = 2 := Finset.card_pair hik
    have heven : ({i, k} : Finset (Fin (n + 1))).card % 2 = 0 := by rw [hcard]
    have h0 : (0 : Fin (n + 1)) ∉ ({i, k} : Finset (Fin (n + 1))) := by
      simp [Ne.symm hi, Ne.symm hk0]
    have hdsp := hdRo7DIrrAux_signChange_dsp b {i, k} h0 heven
    have hvk := hv _ hdsp
    have hcoord := congrArg (b.coord i) hvk
    rw [hdRo7DIrrAux_coord_signChange] at hcoord
    have hiT : i ∈ ({i, k} : Finset (Fin (n + 1))) := by simp
    rw [if_pos hiT] at hcoord
    have h2 : (2 : ZMod 3) * b.coord i v = 0 := by
      linear_combination -hcoord
    exact (mul_eq_zero.mp h2).resolve_left hdRo7DIrrAux_two_ne_zero
  have hv_eq : v = b.coord 0 v • b 0 := by
    apply b.ext_elem
    intro l
    by_cases hl : l = 0
    · subst hl
      simp
    · change b.coord l v = b.coord l ((b.coord 0) v • b 0)
      rw [hzero l hl, map_smul, hdRo7SUReduceVAux_coord_basis b l 0,
        if_neg (fun h : l = 0 => hl h)]
      simp
  exact Submodule.mem_span_singleton.mpr ⟨b.coord 0 v, hv_eq.symm⟩

private theorem hdRo7DIrrAux_coord_basis_mem
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (hn : 3 ≤ n)
    (W : Submodule (ZMod 3) V)
    (hW : ∀ a, DSP 3 b a → ∀ w ∈ W, a w ∈ W)
    {w : V} (hw : w ∈ W) {j : Fin (n + 1)} (hj : j ≠ 0)
    (hjw : b.coord j w ≠ 0) : b j ∈ W := by
  obtain ⟨k, hk0, hkj, -⟩ := exists_ne_zero_ne_ne hn j (0 : Fin (n + 1))
  obtain ⟨l, hl0, hlj, hlk⟩ := exists_ne_zero_ne_ne hn j k
  have hjk : j ≠ k := fun h => hkj h.symm
  have hjl : j ≠ l := fun h => hlj h.symm
  have hkl : k ≠ l := fun h => hlk h.symm
  let T1 : Finset (Fin (n + 1)) := {j, k}
  let T2 : Finset (Fin (n + 1)) := {k, l}
  have hT1card : T1.card = 2 := Finset.card_pair hjk
  have hT2card : T2.card = 2 := Finset.card_pair hkl
  have hT1even : T1.card % 2 = 0 := by rw [hT1card]
  have hT2even : T2.card % 2 = 0 := by rw [hT2card]
  have h0T1 : (0 : Fin (n + 1)) ∉ T1 := by
    simp [T1, Ne.symm hj, Ne.symm hk0]
  have h0T2 : (0 : Fin (n + 1)) ∉ T2 := by
    simp [T2, Ne.symm hk0, Ne.symm hl0]
  have hT1dsp := hdRo7DIrrAux_signChange_dsp b T1 h0T1 hT1even
  have hT2dsp := hdRo7DIrrAux_signChange_dsp b T2 h0T2 hT2even
  let x : V := w - hdRo7DIrrAux_signChange b T1 w
  have hxW : x ∈ W := W.sub_mem hw (hW _ hT1dsp w hw)
  have hx : x = (2 * b.coord j w) • b j + (2 * b.coord k w) • b k := by
    apply b.ext_elem
    intro m
    change b.coord m (w - hdRo7DIrrAux_signChange b T1 w) =
      b.coord m ((2 * b.coord j w) • b j + (2 * b.coord k w) • b k)
    rw [map_sub, hdRo7DIrrAux_coord_signChange, map_add, map_smul, map_smul]
    by_cases hmj : m = j
    · subst hmj
      simp [T1, hjk]
      ring
    · by_cases hmk : m = k
      · subst hmk
        simp [T1, hmj]
        ring
      · have hT1m : m ∉ T1 := by simp [T1, hmj, hmk]
        have hjm : j ≠ m := fun h => hmj h.symm
        have hkm : k ≠ m := fun h => hmk h.symm
        simp [T1, hT1m, hjm, hkm]
  let y : V := x + hdRo7DIrrAux_signChange b T2 x
  have hyW : y ∈ W := W.add_mem hxW (hW _ hT2dsp x hxW)
  have h2j : hdRo7DIrrAux_signChange b T2 (b j) = b j := by
    rw [hdRo7DIrrAux_signChange_apply]
    simp [T2, hjl, hjk]
  have h2k : hdRo7DIrrAux_signChange b T2 (b k) = -b k := by
    rw [hdRo7DIrrAux_signChange_apply]
    simp [T2]
  have hy : y = (4 * b.coord j w) • b j := by
    rw [show y = x + hdRo7DIrrAux_signChange b T2 x from rfl, hx]
    rw [map_add, map_smul, map_smul, h2j, h2k]
    module
  have hcoef : (4 * b.coord j w) ≠ 0 :=
    mul_ne_zero hdRo7DIrrAux_four_ne_zero hjw
  have hbj : b j ∈ W := by
    have hmem := W.smul_mem ((4 * b.coord j w)⁻¹) hyW
    rwa [hy, smul_smul, inv_mul_cancel₀ hcoef, one_smul] at hmem
  exact hbj

private theorem hdRo7DIrrAux_U_irred
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (hn : 3 ≤ n)
    (W : Submodule (ZMod 3) V) (hWU : W ≤ hdRo7DIrrAux_U b)
    (hW : ∀ a, DSP 3 b a → ∀ w ∈ W, a w ∈ W) :
    W = ⊥ ∨ W = hdRo7DIrrAux_U b := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    have hex : ∃ w, w ∈ W ∧ w ≠ 0 := by
      by_contra h
      push Not at h
      rw [Submodule.eq_bot_iff] at *
      exact hbot h
    obtain ⟨w, hwW, hw0⟩ := hex
    have hwU : w ∈ hdRo7DIrrAux_U b := hWU hwW
    have hwcoord0 : b.coord 0 w = 0 := by
      rwa [hdRo7DIrrAux_U, LinearMap.mem_ker] at hwU
    have hexj : ∃ j, j ≠ 0 ∧ b.coord j w ≠ 0 := by
      by_contra h
      push Not at h
      have hw_eq : w = 0 := by
        have hw_eq' : w = b.coord 0 w • b 0 := by
          apply b.ext_elem
          intro l
          by_cases hl : l = 0
          · subst hl; simp
          · change b.coord l w = b.coord l (b.coord 0 w • b 0)
            rw [h l hl, map_smul, hdRo7SUReduceVAux_coord_basis b l 0,
              if_neg (fun hh : l = 0 => hl hh)]
            simp
        rw [hw_eq', hwcoord0, zero_smul]
      exact hw0 hw_eq
    obtain ⟨j, hj0, hjw⟩ := hexj
    have hbj : b j ∈ W := hdRo7DIrrAux_coord_basis_mem b hn W hW hwW hj0 hjw
    have hbk : ∀ k, k ≠ 0 → b k ∈ W := by
      intro k hk
      by_cases hkj : k = j
      · rwa [hkj]
      · have hdsp : DSP 3 b (b.equiv b (Equiv.swap j k)) :=
          hdRo7DIrrAux_perm_dsp (b := b) (Equiv.swap j k) (by
            rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hj0) (Ne.symm hk)])
        have hmem := hW _ hdsp (b j) hbj
        simpa [Module.Basis.equiv_apply, Equiv.swap_apply_left] using hmem
    have hUW : hdRo7DIrrAux_U b ≤ W := by
      intro u hu
      have hu0 : b.coord 0 u = 0 := by
        rwa [hdRo7DIrrAux_U, LinearMap.mem_ker] at hu
      have hrepr : u = ∑ i, b.coord i u • b i := by
        simp [Module.Basis.coord_apply]
      rw [hrepr]
      apply Submodule.sum_mem
      intro i _
      by_cases hi : i = 0
      · subst hi
        rw [hu0, zero_smul]
        exact W.zero_mem
      · exact W.smul_mem _ (hbk i hi)
    exact le_antisymm hWU hUW

private theorem hdRo7DIrrAux_eq_cz_actions {s t : V ≃ₗ[ZMod 3] V}
    (hsz : s (b 0) = -b 0)
    (hsU : ∀ w, w ∈ hdRo7DIrrAux_U b → s w = w)
    (htz : t (b 0) = -b 0)
    (htU : ∀ w, w ∈ hdRo7DIrrAux_U b → t w = w) : s = t := by
  ext v
  have hvU : v - b.coord 0 v • b 0 ∈ hdRo7DIrrAux_U b :=
    hdRo7DIrrAux_sub_smul_mem_U b v
  have hdecomp : v = (v - b.coord 0 v • b 0) + b.coord 0 v • b 0 := by abel
  rw [hdecomp]
  simp only [map_add, map_smul, hsU _ hvU, htU _ hvU, hsz, htz]

private theorem hdRo7DIrrAux_commute_of_cz_actions {s t : V ≃ₗ[ZMod 3] V}
    (hsz : s (b 0) = -b 0)
    (hsU : ∀ w, w ∈ hdRo7DIrrAux_U b → s w = w)
    (htz : t (b 0) = b 0)
    (htU : ∀ w, w ∈ hdRo7DIrrAux_U b → t w ∈ hdRo7DIrrAux_U b) :
    s * t = t * s := by
  ext v
  have hvU : v - b.coord 0 v • b 0 ∈ hdRo7DIrrAux_U b :=
    hdRo7DIrrAux_sub_smul_mem_U b v
  have hdecomp : v = (v - b.coord 0 v • b 0) + b.coord 0 v • b 0 := by abel
  rw [hdecomp]
  simp only [LinearEquiv.mul_apply, map_add, map_smul, map_neg, hsU _ hvU, hsz, htz,
    hsU _ (htU _ hvU)]

private theorem hdRo7DIrrAux_zero_pair_signed
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    {H A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hD : DLinData 3 n V b H A)
    {r : V ≃ₗ[ZMod 3] V} {u : V} {φ : V →ₗ[ZMod 3] ZMod 3}
    (hr : ReflData r u φ) (hrA : r ∈ A)
    {i j : Fin (n + 1)} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j)
    {ε : ZMod 3} (hεsq : ε * ε = 1) (hε : ε = 1 ∨ ε = -1) :
    φ (b i - ε • b j) = 0 ↔ b.coord i u - ε * b.coord j u = 0 := by
  let t : V ≃ₗ[ZMod 3] V := hdRo7DIrrAux_signedSwap b hij ε hεsq
  have ht : ReflData t (b i - ε • b j) (b.coord i - ε • b.coord j) :=
    hdRo7DIrrAux_signedSwap_reflData b hij hεsq
  have htdsp : DSP 3 b t := hdRo7DIrrAux_signedSwap_dsp b hi hj hij hεsq hε
  have htA : t ∈ A := hD.hHA (hD.hPH t htdsp)
  have hiff := hdRo7SUReduceVAux_zero_pair_iff hD.hNoT hr ht hrA htA
  simpa [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] using hiff

private theorem hdRo7DIrrAux_zero_pair_diff
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    {H A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hD : DLinData 3 n V b H A)
    {r : V ≃ₗ[ZMod 3] V} {u : V} {φ : V →ₗ[ZMod 3] ZMod 3}
    (hr : ReflData r u φ) (hrA : r ∈ A)
    {i j : Fin (n + 1)} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    φ (b i - b j) = 0 ↔ b.coord i u = b.coord j u := by
  have h := hdRo7DIrrAux_zero_pair_signed b hD hr hrA hi hj hij
    (ε := 1) (by norm_num) (Or.inl rfl)
  simpa [sub_eq_zero] using h

private theorem hdRo7DIrrAux_zero_pair_sum
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    {H A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hD : DLinData 3 n V b H A)
    {r : V ≃ₗ[ZMod 3] V} {u : V} {φ : V →ₗ[ZMod 3] ZMod 3}
    (hr : ReflData r u φ) (hrA : r ∈ A)
    {i j : Fin (n + 1)} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    φ (b i + b j) = 0 ↔ b.coord i u + b.coord j u = 0 := by
  have h := hdRo7DIrrAux_zero_pair_signed b hD hr hrA hi hj hij
    (ε := -1) (by norm_num) (Or.inr rfl)
  simpa using h

private theorem hdRo7DIrrAux_refl_root_mem_z
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    {H A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hD : DLinData 3 n V b H A)
    {r : V ≃ₗ[ZMod 3] V} {u : V} {φ : V →ₗ[ZMod 3] ZMod 3}
    (hr : ReflData r u φ) (hrA : r ∈ A)
    (hφU : ∀ w, w ∈ hdRo7DIrrAux_U b → φ w = 0) :
    u ∈ Submodule.span (ZMod 3) {b 0} := by
  have hn : 3 ≤ n := by have := hD.hn; omega
  let i0 : Fin (n + 1) := ⟨1, by omega⟩
  let j0 : Fin (n + 1) := ⟨2, by omega⟩
  have hi0 : i0 ≠ 0 := by simp [i0]
  have hj0 : j0 ≠ 0 := by simp [j0]
  have hij : i0 ≠ j0 := by simp [i0, j0]
  have hdiff : φ (b i0 - b j0) = 0 :=
    hφU _ (hdRo7DIrrAux_diff_mem_U b hi0 hj0)
  have hsum : φ (b i0 + b j0) = 0 :=
    hφU _ (hdRo7DIrrAux_sum_mem_U b hi0 hj0)
  have h1 : b.coord i0 u = b.coord j0 u :=
    (hdRo7DIrrAux_zero_pair_diff b hD hr hrA hi0 hj0 hij).mp hdiff
  have h2 : b.coord i0 u + b.coord j0 u = 0 :=
    (hdRo7DIrrAux_zero_pair_sum b hD hr hrA hi0 hj0 hij).mp hsum
  have hui0 : b.coord i0 u = 0 := by
    have h3 : b.coord i0 u + b.coord i0 u = 0 := by
      have h2' := h2
      rw [← h1] at h2'
      exact h2' 
    have h2' : (2 : ZMod 3) * b.coord i0 u = 0 := by
      rw [two_mul]; exact h3
    exact (mul_eq_zero.mp h2').resolve_left hdRo7DIrrAux_two_ne_zero
  have hzero : ∀ i, i ≠ 0 → b.coord i u = 0 := by
    intro i hi
    by_cases hii0 : i = i0
    · rwa [hii0]
    · have hpair : φ (b i0 - b i) = 0 :=
        hφU _ (hdRo7DIrrAux_diff_mem_U b hi0 hi)
      have h1' : b.coord i0 u = b.coord i u :=
        (hdRo7DIrrAux_zero_pair_diff b hD hr hrA hi0 hi
          (fun h => hii0 h.symm)).mp hpair
      rw [← h1']; exact hui0
  have hu_eq : u = b.coord 0 u • b 0 := by
    apply b.ext_elem
    intro l
    by_cases hl : l = 0
    · subst hl; simp
    · change b.coord l u = b.coord l (b.coord 0 u • b 0)
      rw [hzero l hl, map_smul, hdRo7SUReduceVAux_coord_basis b l 0,
        if_neg (fun h : l = 0 => hl h)]
      simp
  exact Submodule.mem_span_singleton.mpr ⟨b.coord 0 u, hu_eq.symm⟩

private theorem hdRo7DIrrAux_refl_phi_kills
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    {H A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hD : DLinData 3 n V b H A)
    {r : V ≃ₗ[ZMod 3] V} {u : V} {φ : V →ₗ[ZMod 3] ZMod 3}
    (hr : ReflData r u φ) (hrA : r ∈ A)
    (hu : u ∈ Submodule.span (ZMod 3) {b 0}) :
    ∀ w, w ∈ hdRo7DIrrAux_U b → φ w = 0 := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hu
  have hn : 3 ≤ n := by have := hD.hn; omega
  let i0 : Fin (n + 1) := ⟨1, by omega⟩
  let j0 : Fin (n + 1) := ⟨2, by omega⟩
  have hi0 : i0 ≠ 0 := by simp [i0]
  have hj0 : j0 ≠ 0 := by simp [j0]
  have hij : i0 ≠ j0 := by simp [i0, j0]
  have hφbasis : ∀ i, i ≠ 0 → φ (b i) = 0 := by
    intro i hi
    let j : Fin (n + 1) := if i = i0 then j0 else i0
    have hj0' : j ≠ 0 := by
      dsimp [j]
      split_ifs with h
      · simp [j0]
      · exact hi0
    have hji : j ≠ i := by
      dsimp [j]
      split_ifs with h
      · rw [h]; exact fun hh => hij hh.symm
      · exact fun hh => h hh.symm
    have hψ : (b.coord i - b.coord j) u = 0 := by
      rw [← hc, map_smul, LinearMap.sub_apply, smul_eq_mul]
      rw [hdRo7SUReduceVAux_coord_basis b i 0,
        hdRo7SUReduceVAux_coord_basis b j 0,
        if_neg hi, if_neg hj0']
      ring
    have hψ' : b.coord i u - b.coord j u = 0 := by
      simpa [LinearMap.sub_apply] using hψ
    have hdiff : φ (b i - b j) = 0 :=
      (hdRo7DIrrAux_zero_pair_diff b hD hr hrA hi hj0' (fun h => hji h.symm)).mpr
        (sub_eq_zero.mp hψ')
    have hψ2 : (b.coord i + b.coord j) u = 0 := by
      rw [← hc, map_smul, LinearMap.add_apply, smul_eq_mul]
      rw [hdRo7SUReduceVAux_coord_basis b i 0,
        hdRo7SUReduceVAux_coord_basis b j 0,
        if_neg hi, if_neg hj0']
      ring
    have hψ2' : b.coord i u + b.coord j u = 0 := by
      simpa [LinearMap.add_apply] using hψ2
    have hsum : φ (b i + b j) = 0 :=
      (hdRo7DIrrAux_zero_pair_sum b hD hr hrA hi hj0' (fun h => hji h.symm)).mpr hψ2'
    have h2 : φ (b i) + φ (b i) = 0 := by
      have hd' : φ (b i) - φ (b j) = 0 := by simpa [map_sub] using hdiff
      have hs' : φ (b i) + φ (b j) = 0 := by simpa [map_add] using hsum
      linear_combination hd' + hs'
    have h2' : (2 : ZMod 3) * φ (b i) = 0 := by
      rw [two_mul]; exact h2
    exact (mul_eq_zero.mp h2').resolve_left hdRo7DIrrAux_two_ne_zero
  intro w hw
  have hw0 : b.coord 0 w = 0 := by
    rwa [hdRo7DIrrAux_U, LinearMap.mem_ker] at hw
  have hrepr : w = ∑ i, b.coord i w • b i := by
    simp [Module.Basis.coord_apply]
  rw [hrepr, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i = 0
  · subst hi
    rw [hw0, zero_smul, map_zero]
  · rw [map_smul, hφbasis i hi, smul_zero]

private theorem hdRo7DIrrAux_refl_cz_actions
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    {H A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hD : DLinData 3 n V b H A)
    {r : V ≃ₗ[ZMod 3] V} {u : V} {φ : V →ₗ[ZMod 3] ZMod 3}
    (hr : ReflData r u φ) (hrA : r ∈ A)
    (hφU : ∀ w, w ∈ hdRo7DIrrAux_U b → φ w = 0) :
    r (b 0) = -b 0 ∧ ∀ w, w ∈ hdRo7DIrrAux_U b → r w = w := by
  have hu := hdRo7DIrrAux_refl_root_mem_z b hD hr hrA hφU
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hu
  have hcne : c ≠ 0 := by
    intro hc0
    apply hr.ne
    rw [← hc, hc0, zero_smul]
  have hpairab : c * φ (b 0) = 2 := by
    have h : φ u = c * φ (b 0) := by
      rw [← hc, map_smul, smul_eq_mul]
    rw [← h]
    exact hr.pair
  have hphiz : φ (b 0) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hpairab
    exact hdRo7DIrrAux_two_ne_zero hpairab.symm
  constructor
  · have hcoef : φ (b 0) * c = 2 := by
      rw [mul_comm]; exact hpairab
    rw [hr.apply]
    rw [← hc, smul_smul, hcoef]
    module
  · intro w hw
    rw [hr.apply, hφU w hw, zero_smul, sub_zero]

private lemma hdRo7DIrrAux_c2sp_mem_U {t : V ≃ₗ[ZMod 3] V} (ht : C2SP 3 b t) :
    ∀ w, w ∈ hdRo7DIrrAux_U b → t w ∈ hdRo7DIrrAux_U b := by
  obtain ⟨σ, c, hσ0, hc0, hc, hact⟩ := ht
  intro w hw
  have hw0 : b.coord 0 w = 0 := by
    rwa [hdRo7DIrrAux_U, LinearMap.mem_ker] at hw
  have hrepr : w = ∑ i, b.coord i w • b i := by
    simp [Module.Basis.coord_apply]
  rw [hrepr, map_sum]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : i = 0
  · subst hi
    rw [hw0, zero_smul, map_zero]
    exact (hdRo7DIrrAux_U b).zero_mem
  · rw [map_smul, hact i]
    have hσi : σ i ≠ 0 := fun h => hi (σ.injective (by rw [h, hσ0]))
    refine Submodule.smul_mem _ _ ?_
    rw [hdRo7DIrrAux_U, LinearMap.mem_ker, map_smul,
      hdRo7SUReduceVAux_coord_basis b 0 (σ i), if_neg (Ne.symm hσi)]
    simp

private theorem hdRo7DIrrAux_generator_dichotomy
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    {H A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hD : DLinData 3 n V b H A)
    (hHU : ∀ a ∈ H, ∀ w ∈ hdRo7DIrrAux_U b, a w ∈ hdRo7DIrrAux_U b)
    {s : V ≃ₗ[ZMod 3] V} (hsH : s ∈ H) (hsrefl : GGLinRefl (p := 3) s) :
    ggLinMove (p := 3) s ≤ hdRo7DIrrAux_U b ∨
      (s (b 0) = -b 0 ∧ ∀ w, w ∈ hdRo7DIrrAux_U b → s w = w) := by
  have : Module.Finite (ZMod 3) V := Module.Finite.of_basis b
  by_cases hmove : ggLinMove (p := 3) s ≤ hdRo7DIrrAux_U b
  · exact Or.inl hmove
  · right
    obtain ⟨u, φ, hr⟩ := hdRo7SUReduceVAux_reflData s hsrefl
    have hu_not : u ∉ hdRo7DIrrAux_U b := by
      intro hu
      apply hmove
      rw [hdRo7SUReduceVAux_move_eq_span hr, Submodule.span_le, Set.singleton_subset_iff]
      exact hu
    have hφU : ∀ w, w ∈ hdRo7DIrrAux_U b → φ w = 0 := by
      intro w hw
      have hsw : s w - w ∈ hdRo7DIrrAux_U b :=
        Submodule.sub_mem _ (hHU s hsH w hw) hw
      rw [hr.apply w] at hsw
      have hstep : w - φ w • u - w = (-(φ w)) • u := by module
      rw [hstep] at hsw
      by_contra hφ
      apply hu_not
      have hc : -(φ w) ≠ 0 := neg_ne_zero.mpr hφ
      have : u = (-(φ w))⁻¹ • ((-(φ w)) • u) := by
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ hsw
    have hsA : s ∈ A := hD.hHA hsH
    exact hdRo7DIrrAux_refl_cz_actions b hD hr hsA hφU

private theorem hdRo7DIrrAux_cz_of_moves
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    {H A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hD : DLinData 3 n V b H A)
    {t : V ≃ₗ[ZMod 3] V} (htA : t ∈ A) (htrefl : GGLinRefl (p := 3) t)
    (htspan : t (b 0) ∈ Submodule.span (ZMod 3) {b 0})
    (htmoves : t (b 0) ≠ b 0) :
    t (b 0) = -b 0 ∧ ∀ w, w ∈ hdRo7DIrrAux_U b → t w = w := by
  have : Module.Finite (ZMod 3) V := Module.Finite.of_basis b
  obtain ⟨u, φ, hr⟩ := hdRo7SUReduceVAux_reflData t htrefl
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp htspan
  have hcne1 : c ≠ 1 := by
    intro h
    apply htmoves
    rw [← hc, h, one_smul]
  have hc2 : c * c = 1 := by
    have hz : t (t (b 0)) = b 0 := by
      rw [← LinearEquiv.mul_apply, htrefl.1]
      rfl
    have hc2' : (c * c) • b 0 = b 0 := by
      have h1 : t (t (b 0)) = b 0 := hz
      rw [← hc] at h1
      rw [map_smul, ← hc, smul_smul] at h1
      exact h1
    have hzero : (c * c - 1) • b 0 = 0 := by
      rw [sub_smul, hc2', one_smul, sub_self]
    have hcoef : c * c - 1 = 0 :=
      (smul_eq_zero.mp hzero).resolve_right (b.ne_zero 0)
    exact sub_eq_zero.mp hcoef
  have hcne0 : c ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hc2
    exact zero_ne_one hc2
  have hcneg : c = -1 :=
    (hdRo7DIrrAux_eq_one_or_neg_one c hcne0).resolve_left hcne1
  have htz : t (b 0) = -b 0 := by
    rw [← hc, hcneg, neg_one_smul]
  have hphi_u : φ (b 0) • u = (2 : ZMod 3) • b 0 := by
    have h := hr.apply (b 0)
    rw [htz] at h
    have h' : φ (b 0) • u = b 0 + b 0 := by
      calc φ (b 0) • u = b 0 - (b 0 - φ (b 0) • u) := by abel
        _ = b 0 - (-b 0) := by rw [h]
        _ = b 0 + b 0 := by abel
    rw [two_smul]
    exact h'
  have hphiz : φ (b 0) ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hphi_u
    have h2z : (2 : ZMod 3) • b 0 = 0 := hphi_u.symm
    exact (b.ne_zero 0) ((smul_eq_zero.mp h2z).resolve_left hdRo7DIrrAux_two_ne_zero)
  have hu_mem : u ∈ Submodule.span (ZMod 3) {b 0} := by
    rw [Submodule.mem_span_singleton]
    refine ⟨(φ (b 0))⁻¹ * 2, ?_⟩
    calc ((φ (b 0))⁻¹ * 2) • b 0
        = (φ (b 0))⁻¹ • ((2 : ZMod 3) • b 0) := by rw [smul_smul]
      _ = (φ (b 0))⁻¹ • (φ (b 0) • u) := by rw [← hphi_u]
      _ = u := by rw [smul_smul, inv_mul_cancel₀ hphiz, one_smul]
  have hφU := hdRo7DIrrAux_refl_phi_kills b hD hr htA hu_mem
  exact hdRo7DIrrAux_refl_cz_actions b hD hr htA hφU

private theorem hdRo7DIrrAux_singleton_contra
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    {H A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hD : DLinData 3 n V b H A)
    {S : Set (V ≃ₗ[ZMod 3] V)} {s0 : V ≃ₗ[ZMod 3] V}
    (hHcl : H = Subgroup.closure S) (hSsing : S = {s0})
    (hs0sq : s0 * s0 = 1) (hs0z : s0 (b 0) = -b 0) : False := by
  have hn : 2 ≤ n := by have := hD.hn; omega
  let i : Fin (n + 1) := ⟨1, by omega⟩
  let j : Fin (n + 1) := ⟨2, by omega⟩
  have hi0 : i ≠ 0 := by simp [i]
  have hj0 : j ≠ 0 := by simp [j]
  have hij : i ≠ j := by simp [i, j]
  let τ : V ≃ₗ[ZMod 3] V := b.equiv b (Equiv.swap i j)
  have hτdsp : DSP 3 b τ :=
    hdRo7DIrrAux_perm_dsp (b := b) (Equiv.swap i j) (by
      rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hi0) (Ne.symm hj0)])
  have hτH : τ ∈ H := hD.hPH τ hτdsp
  have hτclos : τ ∈ Subgroup.closure ({s0} : Set (V ≃ₗ[ZMod 3] V)) := by
    rw [← hSsing, ← hHcl]
    exact hτH
  have hτcases : τ = 1 ∨ τ = s0 := by
    refine Subgroup.closure_induction (p := fun x _ => x = 1 ∨ x = s0) ?_ ?_ ?_ ?_ hτclos
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Or.inr rfl
    · exact Or.inl rfl
    · intro x y _ _ hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · left; rw [one_mul]
      · right; rw [one_mul]
      · right; rw [mul_one]
      · left; rw [hs0sq]
    · intro x _ hx
      rcases hx with rfl | rfl
      · left; rw [inv_one]
      · right; rw [inv_eq_of_mul_eq_one_right hs0sq]
  have hτne1 : τ ≠ 1 := by
    intro h
    have h1 := congrArg (fun e : V ≃ₗ[ZMod 3] V => e (b i)) h
    simp only [τ, Module.Basis.equiv_apply, Equiv.swap_apply_left, LinearEquiv.one_eq_refl,
      LinearEquiv.refl_apply] at h1
    exact hij (b.injective h1).symm
  have hτz : τ (b 0) = b 0 := by
    simp [τ, Module.Basis.equiv_apply,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hi0) (Ne.symm hj0)]
  have heq : τ (b 0) = s0 (b 0) := by
    rw [hτcases.resolve_left hτne1]
  rw [hτz, hs0z] at heq
  have hbad : (1 : ZMod 3) = -1 := by
    have hc := congrArg (b.coord 0) heq
    simpa using hc
  exact absurd hbad hdRo7DIrrAux_one_ne_neg_one

private theorem hdRo7DIrrAux_not_preserves_U
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    {H A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hD : DLinData 3 n V b H A)
    (hspan : ∃ r ∈ H, GGLinRefl (p := 3) r ∧
      ¬ ggLinMove (p := 3) r ≤ hdRo7DIrrAux_U b) :
    ¬ (∀ a ∈ H, ∀ w ∈ hdRo7DIrrAux_U b, a w ∈ hdRo7DIrrAux_U b) := by
  intro hHU
  have : Module.Finite (ZMod 3) V := Module.Finite.of_basis b
  obtain ⟨S, hS, hHcl, hSconn⟩ := hD.hgen
  have hex : ∃ s ∈ S, ¬ ggLinMove (p := 3) s ≤ hdRo7DIrrAux_U b := by
    by_contra h
    push Not at h
    have hHmove : ∀ a ∈ H, ggLinMove (p := 3) a ≤ hdRo7DIrrAux_U b := by
      intro a ha
      rw [hHcl] at ha
      refine Subgroup.closure_induction
        (p := fun x _ => ggLinMove (p := 3) x ≤ hdRo7DIrrAux_U b) ?_ ?_ ?_ ?_ ha
      · intro x hx
        exact h x hx
      · intro v hv
        obtain ⟨w, hw⟩ := hv
        have hwv : v = 0 := by simpa using hw.symm
        rw [hwv]
        exact (hdRo7DIrrAux_U b).zero_mem
      · intro x y hxmem hymem hx hy
        have hx' : ∀ v, x v - v ∈ hdRo7DIrrAux_U b := fun v => hx ⟨v, rfl⟩
        have hy' : ∀ v, y v - v ∈ hdRo7DIrrAux_U b := fun v => hy ⟨v, rfl⟩
        rw [ggLinMove]
        rintro w ⟨v, rfl⟩
        change x (y v) - v ∈ hdRo7DIrrAux_U b
        have hxy : x (y v) - v = (x (y v) - y v) + (y v - v) := by abel
        rw [hxy]
        exact Submodule.add_mem _ (hx' (y v)) (hy' v)
      · intro x hxmem hx
        rw [ggLinMove]
        rintro w ⟨v, rfl⟩
        change x⁻¹ v - v ∈ hdRo7DIrrAux_U b
        have hx' : ∀ v, x v - v ∈ hdRo7DIrrAux_U b := fun v => hx ⟨v, rfl⟩
        have hxv : x (x⁻¹ v) - x⁻¹ v ∈ hdRo7DIrrAux_U b := hx' (x⁻¹ v)
        have hxinv : x (x⁻¹ v) = v := by simp
        have hmem : v - x⁻¹ v ∈ hdRo7DIrrAux_U b := by
          rwa [hxinv] at hxv
        have : x⁻¹ v - v = -(v - x⁻¹ v) := by abel
        rw [this]
        exact Submodule.neg_mem _ hmem
    obtain ⟨r, hrH, hrrefl, hrmove⟩ := hspan
    exact hrmove (hHmove r hrH)
  obtain ⟨s0, hs0S, hs0move⟩ := hex
  obtain ⟨hs0H, hs0refl⟩ := hS s0 hs0S
  have hs0dich := hdRo7DIrrAux_generator_dichotomy b hD hHU hs0H hs0refl
  have hs0cz : s0 (b 0) = -b 0 ∧
      ∀ w, w ∈ hdRo7DIrrAux_U b → s0 w = w :=
    hs0dich.resolve_left hs0move
  have hs0A : s0 ∈ A := hD.hHA hs0H
  obtain ⟨u0, φ0, hr0⟩ := hdRo7SUReduceVAux_reflData s0 hs0refl
  have hφ0U : ∀ w, w ∈ hdRo7DIrrAux_U b → φ0 w = 0 := by
    intro w hw
    have h := hr0.apply w
    rw [hs0cz.2 w hw] at h
    have hsub : φ0 w • u0 = 0 := sub_eq_self.mp h.symm
    exact (smul_eq_zero.mp hsub).resolve_right hr0.ne
  have hcomm : ∀ t ∈ S, Commute s0 t := by
    intro t htS
    obtain ⟨htH, htrefl⟩ := hS t htS
    have htA : t ∈ A := hD.hHA htH
    obtain ⟨u, φ, hr⟩ := hdRo7SUReduceVAux_reflData t htrefl
    by_cases htm : ggLinMove (p := 3) t ≤ hdRo7DIrrAux_U b
    · have huU : u ∈ hdRo7DIrrAux_U b := by
        have := htm
        rw [hdRo7SUReduceVAux_move_eq_span hr] at this
        exact this (Submodule.mem_span_singleton_self u)
      have hφ0u : φ0 u = 0 := hφ0U u huU
      have hψu0 : φ u0 = 0 :=
        hdRo7SUReduceVAux_zero_pair hD.hNoT hr0 hr hs0A htA hφ0u
      exact commute_of_orth hr0 hr hφ0u hψu0
    · have htcz : t (b 0) = -b 0 ∧
          ∀ w, w ∈ hdRo7DIrrAux_U b → t w = w :=
        (hdRo7DIrrAux_generator_dichotomy b hD hHU htH htrefl).resolve_left htm
      have heq : s0 = t :=
        hdRo7DIrrAux_eq_cz_actions (s := s0) (t := t)
          hs0cz.1 hs0cz.2 htcz.1 htcz.2
      rw [heq]
  have hSsing : S = {s0} := by
    ext t
    constructor
    · intro ht
      have := hdRo7SUReduceVAux_reflTransGen_eq_of_no_edge
        (fun u v => u ∈ S ∧ v ∈ S ∧ ¬ Commute u v)
        (fun b hb => hb.2.2 (hcomm b hb.2.1))
        (hSconn s0 hs0S t ht)
      rw [Set.mem_singleton_iff]
      exact this
    · intro ht
      rw [Set.mem_singleton_iff] at ht
      subst ht
      exact hs0S
  exact hdRo7DIrrAux_singleton_contra b hD hHcl hSsing hs0refl.1 hs0cz.1

private theorem hdRo7DIrrAux_not_preserves_z
    (hN : DNormalizerLeaf) (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    {H A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hD : DLinData 3 n V b H A)
    (hmove : ∃ a ∈ H, a (b 0) ≠ b 0) :
    ¬ (∀ a ∈ H, a (b 0) ∈ Submodule.span (ZMod 3) {b 0}) := by
  intro hHz
  have : Module.Finite (ZMod 3) V := Module.Finite.of_basis b
  obtain ⟨S, hS, hHcl, hSconn⟩ := hD.hgen
  have hex : ∃ s ∈ S, s (b 0) ≠ b 0 := by
    by_contra h
    push Not at h
    have hfix : ∀ a ∈ H, a (b 0) = b 0 := by
      intro a ha
      rw [hHcl] at ha
      refine Subgroup.closure_induction (p := fun x _ => x (b 0) = b 0) ?_ ?_ ?_ ?_ ha
      · intro x hx
        exact h x hx
      · rfl
      · intro x y hxmem hymem hx hy
        rw [LinearEquiv.mul_apply, hy, hx]
      · intro x hxmem hx
        have := congrArg (fun w => x⁻¹ w) hx
        simpa using this.symm
    obtain ⟨a, ha, haz⟩ := hmove
    exact haz (hfix a ha)
  obtain ⟨s0, hs0S, hs0moves⟩ := hex
  obtain ⟨hs0H, hs0refl⟩ := hS s0 hs0S
  have hs0A : s0 ∈ A := hD.hHA hs0H
  have hs0cz : s0 (b 0) = -b 0 ∧
      ∀ w, w ∈ hdRo7DIrrAux_U b → s0 w = w :=
    hdRo7DIrrAux_cz_of_moves b hD hs0A hs0refl (hHz s0 hs0H) hs0moves
  have hcomm : ∀ t ∈ S, Commute s0 t := by
    intro t htS
    obtain ⟨htH, htrefl⟩ := hS t htS
    by_cases htz : t (b 0) = b 0
    · have htA : t ∈ A := hD.hHA htH
      have hnorm : ∀ s, DSP 3 b s → DSP 3 b (t * s * t⁻¹) :=
        hD.hStab t htA htz
      have hC2 : C2SP 3 b t :=
        hN 3 rfl n (by have := hD.hn; omega) V b t hnorm htz
      exact hdRo7DIrrAux_commute_of_cz_actions (b := b) hs0cz.1 hs0cz.2 htz
        (hdRo7DIrrAux_c2sp_mem_U (b := b) hC2)
    · have htcz : t (b 0) = -b 0 ∧
          ∀ w, w ∈ hdRo7DIrrAux_U b → t w = w :=
        hdRo7DIrrAux_cz_of_moves b hD (hD.hHA htH) htrefl (hHz t htH) htz
      have heq : s0 = t :=
        hdRo7DIrrAux_eq_cz_actions (s := s0) (t := t)
          hs0cz.1 hs0cz.2 htcz.1 htcz.2
      rw [heq]
  have hSsing : S = {s0} := by
    ext t
    constructor
    · intro ht
      have := hdRo7SUReduceVAux_reflTransGen_eq_of_no_edge
        (fun u v => u ∈ S ∧ v ∈ S ∧ ¬ Commute u v)
        (fun b hb => hb.2.2 (hcomm b hb.2.1))
        (hSconn s0 hs0S t ht)
      rw [Set.mem_singleton_iff]
      exact this
    · intro ht
      rw [Set.mem_singleton_iff] at ht
      subst ht
      exact hs0S
  exact hdRo7DIrrAux_singleton_contra b hD hHcl hSsing hs0refl.1 hs0cz.1

private theorem hdRo7DIrrAux_PInv
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (hn : 3 ≤ n)
    (W : Submodule (ZMod 3) V)
    (hW : ∀ a, DSP 3 b a → ∀ w ∈ W, a w ∈ W) :
    W = ⊥ ∨ W = Submodule.span (ZMod 3) {b 0} ∨ W = hdRo7DIrrAux_U b ∨ W = ⊤ := by
  by_cases hWU : W ≤ hdRo7DIrrAux_U b
  · rcases hdRo7DIrrAux_U_irred b hn W hWU hW with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · by_cases hWz : W ≤ Submodule.span (ZMod 3) {b 0}
    · right; left
      have hne : W ≠ ⊥ := fun h => hWU (h ▸ bot_le)
      have hex : ∃ w, w ∈ W ∧ w ≠ 0 := by
        by_contra h
        push Not at h
        exact hne ((Submodule.eq_bot_iff W).mpr h)
      obtain ⟨w, hwW, hw0⟩ := hex
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hWz hwW)
      have hcne : c ≠ 0 := by
        intro hc0
        apply hw0
        rw [← hc, hc0, zero_smul]
      have hzW : b 0 ∈ W := by
        have hmem := W.smul_mem c⁻¹ hwW
        rwa [← hc, smul_smul, inv_mul_cancel₀ hcne, one_smul] at hmem
      have hspanle : Submodule.span (ZMod 3) {b 0} ≤ W := by
        rw [Submodule.span_singleton_le_iff_mem]
        exact hzW
      exact le_antisymm hWz hspanle
    · right; right; right
      have hexw : ∃ w, w ∈ W ∧ w ∉ Submodule.span (ZMod 3) {b 0} := by
        by_contra h
        push Not at h
        exact hWz h
      obtain ⟨w, hwW, hwspan⟩ := hexw
      let u : V := w - b.coord 0 w • b 0
      have huU : u ∈ hdRo7DIrrAux_U b := hdRo7DIrrAux_sub_smul_mem_U b w
      have hu0 : u ≠ 0 := by
        intro h
        apply hwspan
        rw [Submodule.mem_span_singleton]
        refine ⟨b.coord 0 w, ?_⟩
        exact (sub_eq_zero.mp h).symm
      have hu_not_span : u ∉ Submodule.span (ZMod 3) {b 0} := by
        intro hu_sp
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hu_sp
        by_cases hc0 : c = 0
        · apply hu0
          rw [← hc, hc0, zero_smul]
        · apply hdRo7DIrrAux_z_not_mem_U b
          have hcz : c • b 0 ∈ hdRo7DIrrAux_U b := by
            rw [hc]; exact huU
          have : b 0 = c⁻¹ • (c • b 0) := by
            rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
          rw [this]
          exact (hdRo7DIrrAux_U b).smul_mem _ hcz
      let V' : Submodule (ZMod 3) V :=
        Submodule.span (ZMod 3)
          {v : V | ∃ p : V ≃ₗ[ZMod 3] V, DSP 3 b p ∧ v = p u - u}
      have hV'U : V' ≤ hdRo7DIrrAux_U b := by
        rw [Submodule.span_le]
        rintro v ⟨p, hp, rfl⟩
        exact (hdRo7DIrrAux_U b).sub_mem (hdRo7DIrrAux_dsp_mem_U b hp u huU) huU
      have hV'W : V' ≤ W := by
        rw [Submodule.span_le]
        rintro v ⟨p, hp, rfl⟩
        have hpz := hdRo7DIrrAux_dsp_apply_zero hp
        have hpu : p u - u = p w - w := by
          show p (w - b.coord 0 w • b 0) - (w - b.coord 0 w • b 0) = p w - w
          rw [map_sub, map_smul, hpz]
          abel
        rw [hpu]
        exact W.sub_mem (hW p hp w hwW) hwW
      have hV'P : ∀ q, DSP 3 b q → ∀ v ∈ V', q v ∈ V' := by
        intro q hq v hv
        refine Submodule.span_induction (p := fun v _ => q v ∈ V') ?_ ?_ ?_ ?_ hv
        · rintro _ ⟨p, hp, rfl⟩
          have hqp : DSP 3 b (q * p) := hdRo7DIrrAux_dsp_mul hq hp
          have hsplit : q (p u - u) = (q * p) u - u - (q u - u) := by
            rw [map_sub, LinearEquiv.mul_apply]
            abel
          rw [hsplit]
          exact V'.sub_mem (Submodule.subset_span ⟨q * p, hqp, rfl⟩)
            (Submodule.subset_span ⟨q, hq, rfl⟩)
        · simp
        · intro x y hx hy hpx hpy
          rw [map_add]
          exact V'.add_mem hpx hpy
        · intro r x hx hpx
          rw [map_smul]
          exact V'.smul_mem r hpx
      have hV'ne : V' ≠ ⊥ := by
        intro hbot
        have hfix : ∀ p, DSP 3 b p → p u = u := by
          intro p hp
          have hmem : p u - u ∈ V' := Submodule.subset_span ⟨p, hp, rfl⟩
          rw [hbot, Submodule.mem_bot] at hmem
          exact sub_eq_zero.mp hmem
        exact hu_not_span (hdRo7DIrrAux_fixed b hn u hfix)
      have hUW : hdRo7DIrrAux_U b ≤ W := by
        have hV'eqU : V' = hdRo7DIrrAux_U b := by
          rcases hdRo7DIrrAux_U_irred b hn V' hV'U hV'P with h | h
          · exact absurd h hV'ne
          · exact h
        rw [← hV'eqU]
        exact hV'W
      have hexw1 : ∃ w1, w1 ∈ W ∧ w1 ∉ hdRo7DIrrAux_U b := by
        by_contra h
        push Not at h
        exact hWU h
      obtain ⟨w1, hw1W, hw1U⟩ := hexw1
      let u1 : V := w1 - b.coord 0 w1 • b 0
      have hu1U : u1 ∈ hdRo7DIrrAux_U b := hdRo7DIrrAux_sub_smul_mem_U b w1
      have hc1 : b.coord 0 w1 ≠ 0 := by
        intro h
        apply hw1U
        rw [hdRo7DIrrAux_U, LinearMap.mem_ker]
        exact h
      have hzW : b 0 ∈ W := by
        have hmem := W.sub_mem hw1W (hUW hu1U)
        have heq : w1 - u1 = b.coord 0 w1 • b 0 := by
          show w1 - (w1 - b.coord 0 w1 • b 0) = b.coord 0 w1 • b 0
          abel
        rw [heq] at hmem
        have hscaled := W.smul_mem (b.coord 0 w1)⁻¹ hmem
        rwa [smul_smul, inv_mul_cancel₀ hc1, one_smul] at hscaled
      have hzle : Submodule.span (ZMod 3) {b 0} ≤ W := by
        rw [Submodule.span_singleton_le_iff_mem]
        exact hzW
      have hsup : hdRo7DIrrAux_U b ⊔ Submodule.span (ZMod 3) {b 0} = ⊤ := by
        rw [Submodule.eq_top_iff']
        intro v
        rw [Submodule.mem_sup]
        refine ⟨v - b.coord 0 v • b 0, hdRo7DIrrAux_sub_smul_mem_U b v,
          b.coord 0 v • b 0,
          Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _)), ?_⟩
        abel
      have htopW : (⊤ : Submodule (ZMod 3) V) ≤ W := by
        rw [← hsup]
        exact sup_le hUW hzle
      exact le_antisymm le_top htopW

private theorem hdRo7DIrrAux_irred
    (hN : DNormalizerLeaf) (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    {H A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hD : DLinData 3 n V b H A)
    (hspan : ∃ r ∈ H, GGLinRefl (p := 3) r ∧
      ¬ ggLinMove (p := 3) r ≤ hdRo7DIrrAux_U b)
    (hmove : ∃ a ∈ H, a (b 0) ≠ b 0) :
    ∀ W : Submodule (ZMod 3) V,
      (∀ a ∈ H, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  have hPinv : ∀ a, DSP 3 b a → ∀ w ∈ W, a w ∈ W :=
    fun a ha w hw => hW a (hD.hPH a ha) w hw
  rcases hdRo7DIrrAux_PInv b (by have := hD.hn; omega) W hPinv with
    h | h | h | h
  · exact Or.inl h
  · exfalso
    apply hdRo7DIrrAux_not_preserves_z hN b hD hmove
    intro a ha
    have hzW : b 0 ∈ W := by
      rw [h]
      exact Submodule.subset_span (Set.mem_singleton _)
    have := hW a ha (b 0) hzW
    rwa [h] at this
  · exfalso
    apply hdRo7DIrrAux_not_preserves_U b hD hspan
    intro a ha w hw
    rw [← h] at hw
    have := hW a ha w hw
    rwa [h] at this
  · exact Or.inr h

private theorem hdRo7DIrrAux_commutant
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    {H A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hD : DLinData 3 n V b H A)
    (hIrr : ∀ W : Submodule (ZMod 3) V,
      (∀ a ∈ H, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ⊤)
    (T : V →ₗ[ZMod 3] V)
    (hT : ∀ a ∈ H, T ∘ₗ (a : V →ₗ[ZMod 3] V) = (a : V →ₗ[ZMod 3] V) ∘ₗ T) :
    ∃ c : ZMod 3, T = c • LinearMap.id := by
  have hn : 3 ≤ n := by have := hD.hn; omega
  have : Module.Finite (ZMod 3) V := Module.Finite.of_basis b
  have hTapply : ∀ a ∈ H, ∀ v, T (a v) = a (T v) := by
    intro a ha v
    have h := LinearMap.congr_fun (hT a ha) v
    simpa using h
  have hTz_mem : T (b 0) ∈ Submodule.span (ZMod 3) {b 0} := by
    apply hdRo7DIrrAux_fixed b hn (T (b 0))
    intro a ha
    have h := hTapply a (hD.hPH a ha) (b 0)
    rw [hdRo7DIrrAux_dsp_apply_zero ha] at h
    exact h.symm
  have hsupp : ∀ i, i ≠ 0 → ∀ l, l ≠ 0 → l ≠ i →
      b.coord l (T (b i)) = 0 := by
    intro i hi l hl0 hli
    obtain ⟨k, hk0, hki, hkl⟩ := exists_ne_zero_ne_ne hn i l
    have hik : i ≠ k := fun h => hki h.symm
    let Tset : Finset (Fin (n + 1)) := {i, k}
    have hcard : Tset.card = 2 := Finset.card_pair hik
    have heven : Tset.card % 2 = 0 := by rw [hcard]
    have h0 : (0 : Fin (n + 1)) ∉ Tset := by
      simp [Tset, Ne.symm hi, Ne.symm hk0]
    have hdsp := hdRo7DIrrAux_signChange_dsp b Tset h0 heven
    have hcomm := hTapply _ (hD.hPH _ hdsp) (b i)
    have hbi : hdRo7DIrrAux_signChange b Tset (b i) = -b i := by
      rw [hdRo7DIrrAux_signChange_apply]
      simp [Tset]
    rw [hbi, map_neg] at hcomm
    have hcoord := congrArg (b.coord l) hcomm
    rw [map_neg, hdRo7DIrrAux_coord_signChange] at hcoord
    have hlT : l ∉ Tset := by
      simp [Tset, hli, Ne.symm hkl]
    rw [if_neg hlT, one_mul] at hcoord
    have h2 : (2 : ZMod 3) * b.coord l (T (b i)) = 0 := by
      linear_combination -hcoord
    exact (mul_eq_zero.mp h2).resolve_left hdRo7DIrrAux_two_ne_zero
  have hTbasis : ∀ i, i ≠ 0 → ∃ a c : ZMod 3,
      T (b i) = a • b 0 + c • b i := by
    intro i hi
    refine ⟨b.coord 0 (T (b i)), b.coord i (T (b i)), ?_⟩
    apply b.ext_elem
    intro l
    by_cases hl0 : l = 0
    · subst hl0
      simp [Ne.symm hi]
    · by_cases hli : l = i
      · subst hli
        change b.coord l (T (b l)) =
          b.coord l (b.coord 0 (T (b l)) • b 0 + b.coord l (T (b l)) • b l)
        rw [map_add, map_smul, map_smul, hdRo7SUReduceVAux_coord_basis b l 0,
          if_neg (fun h : l = 0 => hl0 h), hdRo7SUReduceVAux_coord_basis b l l,
          if_pos rfl]
        simp
      · simpa [map_add, map_smul, hdRo7SUReduceVAux_coord_basis, hl0, hli,
          Module.Basis.coord_apply] using hsupp i hi l hl0 hli
  have hTbasis_form : ∃ γ δ : ZMod 3,
      ∀ i, i ≠ 0 → T (b i) = γ • b 0 + δ • b i := by
    let i0 : Fin (n + 1) := ⟨1, by omega⟩
    have hi0 : i0 ≠ 0 := by simp [i0]
    obtain ⟨γ, δ, hγδ⟩ := hTbasis i0 hi0
    refine ⟨γ, δ, fun i hi => ?_⟩
    by_cases hii0 : i = i0
    · rwa [hii0]
    · let τ : V ≃ₗ[ZMod 3] V := b.equiv b (Equiv.swap i0 i)
      have hτdsp : DSP 3 b τ :=
        hdRo7DIrrAux_perm_dsp (b := b) (Equiv.swap i0 i) (by
          rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hi0) (Ne.symm hi)])
      have hcomm := hTapply τ (hD.hPH τ hτdsp) (b i0)
      have hτb : τ (b i0) = b i := by
        simp [τ, Module.Basis.equiv_apply, Equiv.swap_apply_left]
      have hτz : τ (b 0) = b 0 := by
        simp [τ, Module.Basis.equiv_apply,
          Equiv.swap_apply_of_ne_of_ne (Ne.symm hi0) (Ne.symm hi)]
      rw [hτb, hγδ] at hcomm
      rw [map_add, map_smul, map_smul, hτz, hτb] at hcomm
      exact hcomm
  obtain ⟨γ, δ, hγδ⟩ := hTbasis_form
  have hγ0 : γ = 0 := by
    let i0 : Fin (n + 1) := ⟨1, by omega⟩
    have hi0 : i0 ≠ 0 := by simp [i0]
    obtain ⟨k, hk0, hki, -⟩ := exists_ne_zero_ne_ne hn i0 (0 : Fin (n + 1))
    have hik : i0 ≠ k := fun h => hki h.symm
    let Tset : Finset (Fin (n + 1)) := {i0, k}
    have hcard : Tset.card = 2 := Finset.card_pair hik
    have heven : Tset.card % 2 = 0 := by rw [hcard]
    have h0 : (0 : Fin (n + 1)) ∉ Tset := by
      simp [Tset, Ne.symm hi0, Ne.symm hk0]
    have hdsp := hdRo7DIrrAux_signChange_dsp b Tset h0 heven
    have hcomm := hTapply _ (hD.hPH _ hdsp) (b i0)
    have hbi : hdRo7DIrrAux_signChange b Tset (b i0) = -b i0 := by
      rw [hdRo7DIrrAux_signChange_apply]
      simp [Tset]
    have hzfix : hdRo7DIrrAux_signChange b Tset (b 0) = b 0 := by
      rw [hdRo7DIrrAux_signChange_apply]
      simp [Tset, Ne.symm hi0, Ne.symm hk0]
    rw [hbi, map_neg, hγδ i0 hi0] at hcomm
    rw [map_add, map_smul, map_smul, hzfix, hbi] at hcomm
    have hcoord : -γ = γ := by
      have h := congrArg (b.coord 0) hcomm
      simpa [map_add, map_smul, map_neg, hdRo7SUReduceVAux_coord_basis,
        Ne.symm hi0] using h
    have h2 : (2 : ZMod 3) * γ = 0 := by
      linear_combination -hcoord
    exact (mul_eq_zero.mp h2).resolve_left hdRo7DIrrAux_two_ne_zero
  have hTb : ∀ i, i ≠ 0 → T (b i) = δ • b i := by
    intro i hi
    rw [hγδ i hi, hγ0, zero_smul, zero_add]
  have hTU : ∀ u, u ∈ hdRo7DIrrAux_U b → T u = δ • u := by
    intro u hu
    have hu0 : b.coord 0 u = 0 := by
      rwa [hdRo7DIrrAux_U, LinearMap.mem_ker] at hu
    have hrepr : u = ∑ i, b.coord i u • b i := by
      simp [Module.Basis.coord_apply]
    rw [hrepr, map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i = 0
    · subst hi
      rw [hu0]
      simp
    · rw [map_smul, hTb i hi, smul_smul, smul_smul]
      congr 1
      ring
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp hTz_mem
  by_cases hαδ : α = δ
  · refine ⟨α, ?_⟩
    ext v
    have hvU := hdRo7DIrrAux_sub_smul_mem_U b v
    have hdecomp : v = (v - b.coord 0 v • b 0) + b.coord 0 v • b 0 := by abel
    rw [hdecomp, map_add, map_smul, hTU _ hvU, ← hα]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, map_add, map_smul]
    rw [hαδ]
  · exfalso
    let W : Submodule (ZMod 3) V := LinearMap.ker (T - δ • LinearMap.id)
    have hUle : hdRo7DIrrAux_U b ≤ W := by
      intro u hu
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, hTU u hu]
      module
    have hzW : b 0 ∉ W := by
      intro hz
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply] at hz
      rw [← hα] at hz
      have hzero : (α - δ) • b 0 = 0 := by
        rw [sub_smul]
        exact hz
      have hcoef : α - δ = 0 :=
        (smul_eq_zero.mp hzero).resolve_right (b.ne_zero 0)
      exact hαδ (sub_eq_zero.mp hcoef)
    have hWstab : ∀ a ∈ H, ∀ w ∈ W, a w ∈ W := by
      intro a ha w hw
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply] at hw ⊢
      have hcommv := hTapply a ha w
      have hTw : T w = δ • w := sub_eq_zero.mp hw
      rw [hcommv, hTw, map_smul]
      module
    rcases hIrr W hWstab with hbot | htop
    · let i0 : Fin (n + 1) := ⟨1, by omega⟩
      have hi0 : i0 ≠ 0 := by simp [i0]
      have hmemU : b i0 ∈ hdRo7DIrrAux_U b := by
        rw [hdRo7DIrrAux_U, LinearMap.mem_ker,
          hdRo7SUReduceVAux_coord_basis b 0 i0, if_neg (Ne.symm hi0)]
      have hmemW : b i0 ∈ W := hUle hmemU
      rw [hbot, Submodule.mem_bot] at hmemW
      exact (b.ne_zero i0) hmemW
    · rw [htop] at hzW
      exact hzW Submodule.mem_top

end

theorem d_reduceV_absIrred (hN : DNormalizerLeaf) {p : ℕ} [Fact p.Prime] {n : ℕ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {b : Module.Basis (Fin (n + 1)) (ZMod p) V}
    {H A : Subgroup (V ≃ₗ[ZMod p] V)} (hD : DLinData p n V b H A)
    (hspan : ∃ r ∈ H, GGLinRefl r ∧ ¬ ggLinMove r ≤ LinearMap.ker (b.coord 0))
    (hmove : ∃ a ∈ H, a (b 0) ≠ b 0) : ZS.AbsIrred p H := by
  obtain rfl := hD.hp
  have hIrr := hdRo7DIrrAux_irred hN b hD hspan hmove
  refine ⟨hIrr, ?_⟩
  intro T hT
  exact hdRo7DIrrAux_commutant b hD hIrr T hT

end CFSG.StandardType.HdRo7D
