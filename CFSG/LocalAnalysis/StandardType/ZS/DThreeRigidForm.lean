module

public import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
public import Mathlib.LinearAlgebra.BilinearForm.Basic
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.ZS.ReflProductOrder

public section

namespace CFSG.StandardType.ZS

open Module

variable {U : Type} [AddCommGroup U] [Module (ZMod 3) U] [Module.Finite (ZMod 3) U]
  {A : Subgroup (U ≃ₗ[ZMod 3] U)}

local instance (priority := high) zrf_zmodAddCommGroup : AddCommGroup (ZMod 3) :=
  Ring.toAddCommGroup

omit [Module.Finite (ZMod 3) U] in
private noncomputable def zrf_form {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι (ZMod 3) U) (φ : ι → Dual (ZMod 3) U) :
    LinearMap.BilinForm (ZMod 3) U :=
  ∑ i, LinearMap.BilinForm.linMulLin (φ i) (-(b.coord i))

omit [Module.Finite (ZMod 3) U] in
private theorem zrf_form_apply_basis {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι (ZMod 3) U) (φ : ι → Dual (ZMod 3) U) (x : U) (j : ι) :
    zrf_form b φ x (b j) = -(φ j x) := by
  rw [zrf_form]
  change (∑ i, LinearMap.BilinForm.linMulLin (φ i) (-(b.coord i))) x (b j) = -(φ j x)
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp [LinearMap.BilinForm.linMulLin_apply, Module.Basis.coord_apply, Module.Basis.repr_self]
  · intro i _ hij
    simp [LinearMap.BilinForm.linMulLin_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_of_ne hij]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

omit [Module.Finite (ZMod 3) U] in
private theorem zrf_pair_linearIndependent {ι : Type} [Fintype ι]
    (b : Module.Basis ι (ZMod 3) U) {i j : ι} (hij : i ≠ j) :
    LinearIndependent (ZMod 3) ![b i, b j] := by
  have hb : b i ≠ 0 := b.linearIndependent.ne_zero i
  rw [LinearIndependent.pair_iff' hb]
  intro c hc
  have hmem : b j ∈ Submodule.span (ZMod 3) (b '' ({j}ᶜ : Set ι)) := by
    rw [← hc]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨i, by simp [hij], rfl⟩)
  exact b.linearIndependent.notMem_span j hmem

omit [Module.Finite (ZMod 3) U] in
private theorem zrf_mem_span_of_reflection_eq {u v : U} {φ ψ : Dual (ZMod 3) U}
    (hu : φ u = 2) (hv : ψ v = 2)
    (h : Module.reflection hu = Module.reflection hv) :
    v ∈ Submodule.span (ZMod 3) {u} := by
  have hEq : Module.reflection hv u = Module.reflection hu u := by rw [h]
  rw [Module.reflection_apply u hv, Module.reflection_apply u hu, hu] at hEq
  have hrel : ψ u • v = (2 : ZMod 3) • u := by
    simpa using congrArg (fun w => u - w) hEq
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hu
    exact (by decide : (0 : ZMod 3) ≠ 2) hu
  have hψu : ψ u ≠ 0 := by
    intro h0
    have h2u : (2 : ZMod 3) • u = 0 := by rw [← hrel, h0, zero_smul]
    have hu' : u = 0 := by
      rcases smul_eq_zero.mp h2u with h2 | h2
      · exact absurd h2 (by decide)
      · exact h2
    exact hu0 hu'
  refine Submodule.mem_span_singleton.mpr ⟨(ψ u)⁻¹ * 2, ?_⟩
  rw [← smul_smul, ← hrel, inv_smul_smul₀ hψu]

omit [Module.Finite (ZMod 3) U] in
private theorem zrf_not_mem_span_of_pair {u v : U}
    (hli : LinearIndependent (ZMod 3) ![u, v]) :
    v ∉ Submodule.span (ZMod 3) {u} := by
  intro hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
  have hu0 : u ≠ 0 := by
    simpa using hli.ne_zero 0
  exact (LinearIndependent.pair_iff' hu0).mp hli c hc

private theorem zrf_pair (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl 3 x → IsRefl 3 y →
      orderOf (x * y) ≤ 3)
    {u v : U} {φ ψ : Dual (ZMod 3) U} (hu : φ u = 2) (hv : ψ v = 2)
    (hsu : Module.reflection hu ∈ A) (htv : Module.reflection hv ∈ A)
    (hli : LinearIndependent (ZMod 3) ![u, v]) :
    φ v = ψ u := by
  have hle : orderOf (Module.reflection hu * Module.reflection hv) ≤ 3 :=
    h3 _ hsu _ htv (isRefl_reflection (by decide) hu) (isRefl_reflection (by decide) hv)
  have : Finite (U ≃ₗ[ZMod 3] U) := by
    have : Finite U := Module.finite_of_finite (ZMod 3)
    exact Finite.of_injective (fun e : U ≃ₗ[ZMod 3] U => (e : U → U)) DFunLike.coe_injective
  have hpos : 0 < orderOf (Module.reflection hu * Module.reflection hv) := orderOf_pos _
  have hcases : orderOf (Module.reflection hu * Module.reflection hv) = 1 ∨
      orderOf (Module.reflection hu * Module.reflection hv) = 2 ∨
      orderOf (Module.reflection hu * Module.reflection hv) = 3 := by omega
  rcases hcases with h1 | h2 | h3'
  · exfalso
    have h1' : Module.reflection hu * Module.reflection hv = 1 := orderOf_eq_one_iff.mp h1
    have hvv : Module.reflection hv * Module.reflection hv = 1 := by
      simpa [Module.reflection_inv (h := hv)] using mul_inv_cancel (Module.reflection hv)
    have hst : Module.reflection hu = Module.reflection hv := by
      calc Module.reflection hu
          = Module.reflection hu * (Module.reflection hv * Module.reflection hv) := by
              rw [hvv, mul_one]
        _ = (Module.reflection hu * Module.reflection hv) * Module.reflection hv := by
              rw [mul_assoc]
        _ = Module.reflection hv := by rw [h1', one_mul]
    exact zrf_not_mem_span_of_pair hli (zrf_mem_span_of_reflection_eq hu hv hst)
  · have h0 := eq_zero_of_orderOf_eq_two (by decide) hu hv h2
    rw [h0.1, h0.2]
  · have hprod : φ v * ψ u = 1 := mul_eq_one_of_orderOf_eq_three (by decide) hu hv h3'
    have hunits : ∀ x y : ZMod 3, x * y = 1 → x = y := by decide
    exact hunits (φ v) (ψ u) hprod

omit [Module.Finite (ZMod 3) U] in
private theorem zrf_form_symm {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι (ZMod 3) U) (φ : ι → Dual (ZMod 3) U)
    (hpair : ∀ i j : ι, i ≠ j → φ i (b j) = φ j (b i)) :
    ∀ x y, zrf_form b φ x y = zrf_form b φ y x := by
  have hsymm : (zrf_form b φ).IsSymm := by
    rw [LinearMap.BilinForm.isSymm_iff_basis b]
    intro i j
    rw [zrf_form_apply_basis b φ (b i) j, zrf_form_apply_basis b φ (b j) i]
    by_cases hij : i = j
    · subst hij; rfl
    · rw [hpair i j hij]
  exact hsymm.eq

private theorem zrf_functional_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι (ZMod 3) U) (φ : ι → Dual (ZMod 3) U)
    (hφ : ∀ i, φ i (b i) = 2)
    (hreflA : ∀ i, Module.reflection (hφ i) ∈ A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl 3 x → IsRefl 3 y → orderOf (x * y) ≤ 3)
    (hsymm : ∀ x y, zrf_form b φ x y = zrf_form b φ y x)
    {a : U} {ψ : Dual (ZMod 3) U} (hψ : ψ a = 2)
    (htA : Module.reflection hψ ∈ A) :
    ∀ x, ψ x = -(zrf_form b φ x a) := by
  have hfun : ψ = -(zrf_form b φ).flip a := by
    apply Module.Basis.ext b
    intro i
    have hB : zrf_form b φ a (b i) = -(φ i a) := zrf_form_apply_basis b φ a i
    have hsym : zrf_form b φ (b i) a = -(φ i a) := by
      rw [hsymm (b i) a, hB]
    have hRHS : (-(zrf_form b φ).flip a) (b i) = φ i a := by
      rw [LinearMap.neg_apply, LinearMap.BilinForm.flip_apply, hsym, neg_neg]
    rw [hRHS]
    by_cases hind : LinearIndependent (ZMod 3) ![b i, a]
    · exact (zrf_pair (h3 := h3) (hφ i) hψ (hreflA i) htA hind).symm
    · have hb0 : b i ≠ 0 := b.linearIndependent.ne_zero i
      have hdep : ∃ c : ZMod 3, c • b i = a := by
        by_contra h
        exact hind ((LinearIndependent.pair_iff' hb0).mpr fun c hc => h ⟨c, hc⟩)
      obtain ⟨c, hc⟩ := hdep
      have hc0 : c ≠ 0 := by
        intro h0
        have ha0 : a = 0 := by rw [← hc, h0, zero_smul]
        rw [ha0, map_zero] at hψ
        exact (by decide : (0 : ZMod 3) ≠ 2) hψ
      have hcc : c * c = 1 := by
        have : ∀ c : ZMod 3, c ≠ 0 → c * c = 1 := by decide
        exact this c hc0
      have hψbi : c * ψ (b i) = 2 := by
        have := congrArg ψ hc
        rwa [map_smul, smul_eq_mul, hψ] at this
      have hφa : φ i a = c * 2 := by
        rw [← hc, map_smul, smul_eq_mul, hφ i]
      have hψφ : ψ (b i) = φ i a := by
        calc ψ (b i) = (c * c) * ψ (b i) := by rw [hcc, one_mul]
          _ = c * (c * ψ (b i)) := by ring
          _ = c * 2 := by rw [hψbi]
          _ = φ i a := by rw [hφa]
      rw [hψφ]
  intro x
  have hx := congrArg (fun f : U →ₗ[ZMod 3] ZMod 3 => f x) hfun
  simpa [LinearMap.neg_apply, LinearMap.BilinForm.flip_apply] using hx

omit [Module.Finite (ZMod 3) U] in
private theorem zrf_ne_bot (hn : 2 ≤ Module.finrank (ZMod 3) U) (hirr : AbsIrred 3 A) :
    A ≠ ⊥ := by
  intro hbot
  have hnt : Nontrivial U :=
    Module.nontrivial_of_finrank_pos (R := ZMod 3) (M := U) (by omega)
  obtain ⟨v, hv0⟩ := exists_ne (0 : U)
  let L : Submodule (ZMod 3) U := Submodule.span (ZMod 3) {v}
  have hLbot : L ≠ ⊥ := by
    intro hL
    have hvL : v ∈ L := Submodule.subset_span (Set.mem_singleton v)
    rw [hL] at hvL
    exact hv0 (by simpa using hvL)
  have hLtop : L ≠ ⊤ := by
    intro hL
    have h1 : Module.finrank (ZMod 3) L = 1 := by
      simpa [L] using finrank_span_singleton hv0
    rw [hL, finrank_top] at h1
    omega
  have hinv : ∀ a ∈ A, ∀ w ∈ L, a w ∈ L := by
    intro a ha w hw
    have ha1 : a = 1 := by
      have : a ∈ (⊥ : Subgroup (U ≃ₗ[ZMod 3] U)) := by rw [← hbot]; exact ha
      simpa using this
    simpa [ha1] using hw
  rcases hirr.1 L hinv with h | h
  · exact hLbot h
  · exact hLtop h

private theorem zrf_span_roots_eq_top (hn : 2 ≤ Module.finrank (ZMod 3) U)
    (hgen : ReflGen 3 A) (hirr : AbsIrred 3 A) :
    Submodule.span (ZMod 3) {a : U | ∃ (φ : Dual (ZMod 3) U) (hφ : φ a = 2),
      Module.reflection hφ ∈ A} = ⊤ := by
  let S : Set U := {a | ∃ (φ : Dual (ZMod 3) U) (hφ : φ a = 2),
    Module.reflection hφ ∈ A}
  have hAne : A ≠ ⊥ := zrf_ne_bot hn hirr
  have hRne : ∃ t : U ≃ₗ[ZMod 3] U, t ∈ A ∧ IsRefl 3 t := by
    by_contra h
    have hset : {t : U ≃ₗ[ZMod 3] U | t ∈ A ∧ IsRefl 3 t} = ∅ := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun htA ht => h ⟨t, htA, ht⟩
    have hbot : A = ⊥ := by rw [hgen, hset]; exact Subgroup.closure_empty
    exact hAne hbot
  obtain ⟨t, htA, ht⟩ := hRne
  obtain ⟨a, φ, hφ, rfl⟩ := (isRefl_iff (by decide) t).mp ht
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hφ
    exact (by decide : (0 : ZMod 3) ≠ 2) hφ
  have hSne : Submodule.span (ZMod 3) S ≠ ⊥ := by
    intro hS
    have haS : a ∈ Submodule.span (ZMod 3) S :=
      Submodule.subset_span ⟨φ, hφ, by simpa using htA⟩
    rw [hS] at haS
    exact ha0 (by simpa using haS)
  have hinv : ∀ g ∈ A, ∀ w ∈ Submodule.span (ZMod 3) S,
      g w ∈ Submodule.span (ZMod 3) S := by
    intro g hg w hw
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
    · intro y hy
      obtain ⟨φ, hφ, hrefl⟩ := hy
      let φ' : Dual (ZMod 3) U := φ ∘ₗ (g.symm : U →ₗ[ZMod 3] U)
      have hφ' : φ' (g y) = 2 := by simpa [φ'] using hφ
      have hconj : g * Module.reflection hφ * g⁻¹ = Module.reflection hφ' :=
        conj_reflection g hφ hφ'
      have hmemA : g * Module.reflection hφ * g⁻¹ ∈ A :=
        A.mul_mem (A.mul_mem hg hrefl) (A.inv_mem hg)
      exact Submodule.subset_span ⟨φ', hφ', by rwa [← hconj]⟩
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [map_smul]
      exact Submodule.smul_mem _ c hx
  have htop : Submodule.span (ZMod 3) S = ⊤ := by
    rcases hirr.1 (Submodule.span (ZMod 3) S) hinv with h | h
    · exact (hSne h).elim
    · exact h
  simpa [S] using htop

omit [Module.Finite (ZMod 3) U] in
private theorem zrf_nondegenerate (hn : 2 ≤ Module.finrank (ZMod 3) U)
    (hgen : ReflGen 3 A) (hirr : AbsIrred 3 A)
    {B : LinearMap.BilinForm (ZMod 3) U}
    (hB : ∀ t ∈ A, IsRefl 3 t → ∃ u, B u u = 1 ∧ ∀ x, t x = x + B x u • u) :
    ∀ x, (∀ y, B x y = 0) → x = 0 := by
  intro z hz
  by_contra hz0
  have hfix : ∀ g ∈ A, g z = z := by
    intro g hg
    rw [hgen] at hg
    refine Subgroup.closure_induction (p := fun g _ => g z = z) ?_ ?_ ?_ ?_ hg
    · intro t ht
      obtain ⟨htA, ht⟩ := ht
      obtain ⟨u, -, htu⟩ := hB t htA ht
      rw [htu z, hz u, zero_smul, add_zero]
    · simp
    · intro a b _ _ ha hb
      rw [LinearEquiv.mul_apply, hb, ha]
    · intro a _ ha
      calc a⁻¹ z = a⁻¹ (a z) := by rw [ha]
        _ = z := by simp
  let L : Submodule (ZMod 3) U := Submodule.span (ZMod 3) {z}
  have hLbot : L ≠ ⊥ := by
    intro hL
    have hzL : z ∈ L := Submodule.subset_span (Set.mem_singleton z)
    rw [hL] at hzL
    exact hz0 (by simpa using hzL)
  have hLtop : L ≠ ⊤ := by
    intro hL
    have h1 : Module.finrank (ZMod 3) L = 1 := by
      simpa [L] using finrank_span_singleton hz0
    rw [hL, finrank_top] at h1
    omega
  have hinv : ∀ a ∈ A, ∀ w ∈ L, a w ∈ L := by
    intro a ha w hw
    refine Submodule.span_induction (p := fun y _ => a y ∈ L) (x := w) ?_ ?_ ?_ ?_ hw
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy, hfix a ha]
      exact Submodule.subset_span (Set.mem_singleton z)
    · simp
    · intro y z' _ _ hy hz'
      rw [map_add]
      exact Submodule.add_mem _ hy hz'
    · intro c y _ hy
      rw [map_smul]
      exact Submodule.smul_mem _ c hy
  rcases hirr.1 L hinv with h | h
  · exact hLbot h
  · exact hLtop h

private theorem zrf_isRefl_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι (ZMod 3) U) (φ : ι → Dual (ZMod 3) U)
    (hφ : ∀ i, φ i (b i) = 2)
    (hreflA : ∀ i, Module.reflection (hφ i) ∈ A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl 3 x → IsRefl 3 y → orderOf (x * y) ≤ 3)
    (hsymm : ∀ x y, zrf_form b φ x y = zrf_form b φ y x) :
    ∀ t ∈ A, IsRefl 3 t →
      ∃ u, zrf_form b φ u u = 1 ∧ ∀ x, t x = x + zrf_form b φ x u • u := by
  intro t htA ht
  obtain ⟨a, ψ, hψ, rfl⟩ := (isRefl_iff (by decide) t).mp ht
  have heq := zrf_functional_eq b φ hφ hreflA h3 hsymm hψ htA
  refine ⟨a, ?_, ?_⟩
  · have h2 : (2 : ZMod 3) = -(zrf_form b φ a a) := by
      have := heq a
      rw [hψ] at this
      simpa using this
    rw [← neg_neg (zrf_form b φ a a), ← h2]
    decide
  · intro x
    rw [Module.reflection_apply x hψ, heq x, neg_smul, sub_neg_eq_add]

theorem exists_bilinForm_of_orderOf_mul_le_three (hn : 2 ≤ Module.finrank (ZMod 3) U)
    (hgen : ReflGen 3 A) (hirr : AbsIrred 3 A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl 3 x → IsRefl 3 y → orderOf (x * y) ≤ 3) :
    ∃ B : LinearMap.BilinForm (ZMod 3) U, (∀ x y, B x y = B y x) ∧
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧
      ∀ t ∈ A, IsRefl 3 t → ∃ u, B u u = 1 ∧ ∀ x, t x = x + B x u • u := by
  classical
  let S : Set U := {a | ∃ (φ : Dual (ZMod 3) U) (hφ : φ a = 2),
    Module.reflection hφ ∈ A}
  have hspanS : Submodule.span (ZMod 3) S = ⊤ := zrf_span_roots_eq_top hn hgen hirr
  obtain ⟨t, ht_sub, ht_card, ht_span, -⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn (K := ZMod 3) (M := U) S
  have hspan_t : Submodule.span (ZMod 3) (t : Set U) = ⊤ := by
    rw [ht_span, hspanS]
  have hcard : t.card = Module.finrank (ZMod 3) U := by
    rw [ht_card, hspanS, finrank_top]
  let f : ↥t → U := fun i => (i : U)
  have hrange : Set.range f = (t : Set U) := by
    ext x; simp [f]
  have hle : ⊤ ≤ Submodule.span (ZMod 3) (Set.range f) := by
    rw [hrange, hspan_t]
  have hcard' : Fintype.card ↥t = Module.finrank (ZMod 3) U := by
    rw [Fintype.card_coe, hcard]
  let b : Module.Basis ↥t (ZMod 3) U :=
    basisOfTopLeSpanOfCardEqFinrank f hle hcard'
  have hb : ∀ i : ↥t, b i = (i : U) := by
    intro i
    exact congrFun (coe_basisOfTopLeSpanOfCardEqFinrank f hle hcard') i
  have hbS : ∀ i : ↥t, ∃ (φ : Dual (ZMod 3) U) (hφ : φ (b i) = 2),
      Module.reflection hφ ∈ A := by
    intro i
    have h := ht_sub i.2
    simp only [S, Set.mem_setOf_eq] at h
    rwa [← hb i] at h
  let φ : ↥t → Dual (ZMod 3) U := fun i => (hbS i).choose
  let hφ : ∀ i, φ i (b i) = 2 := fun i => (hbS i).choose_spec.choose
  let hreflA : ∀ i, Module.reflection (hφ i) ∈ A := fun i => (hbS i).choose_spec.choose_spec
  let B : LinearMap.BilinForm (ZMod 3) U := zrf_form b φ
  have hpair : ∀ i j : ↥t, i ≠ j → φ i (b j) = φ j (b i) := by
    intro i j hij
    exact zrf_pair h3 (hφ i) (hφ j) (hreflA i) (hreflA j)
      (zrf_pair_linearIndependent b hij)
  have hsymm : ∀ x y, B x y = B y x := by
    intro x y
    exact zrf_form_symm b φ hpair x y
  have hB := zrf_isRefl_eq b φ hφ hreflA h3 hsymm
  refine ⟨B, hsymm, ?_, hB⟩
  exact zrf_nondegenerate hn hgen hirr hB

end CFSG.StandardType.ZS
