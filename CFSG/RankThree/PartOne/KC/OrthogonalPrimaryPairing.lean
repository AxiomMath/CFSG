module

public import CFSG.RankThree.PartOne.KC.OrthogonalReciprocal
public import CFSG.RankThree.PartOne.KC.PrimaryDecomposition
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

section Setup

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

structure OddOrderIsometry (Q : QuadraticForm K V) (p : ℕ) (x : V ≃ₗ[K] V) : Prop where
  mem : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q
  pow_eq_one : x ^ p = 1
  cast_ne_zero : (p : K) ≠ 0
  regular : ∀ v, (∀ w, QuadraticMap.polar Q v w = 0) → v = 0

variable {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.polar_apply (hx : OddOrderIsometry Q p x) (v w : V) :
    QuadraticMap.polar Q (x v) w = QuadraticMap.polar Q v (x.symm w) := by
  have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hx.mem v (x.symm w)
  rwa [x.apply_symm_apply] at this

theorem OddOrderIsometry.polar_symm_apply (hx : OddOrderIsometry Q p x) (v w : V) :
    QuadraticMap.polar Q (x.symm v) w = QuadraticMap.polar Q v (x w) := by
  have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hx.mem (x.symm v) w
  rw [x.apply_symm_apply] at this
  exact this.symm

theorem OddOrderIsometry.polar_pow (hx : OddOrderIsometry Q p x) (n : ℕ) (v w : V) :
    QuadraticMap.polar Q ((x.toLinearMap ^ n) v) w =
      QuadraticMap.polar Q v ((x.symm.toLinearMap ^ n) w) := by
  induction n generalizing v w with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ' x.symm.toLinearMap, Module.End.mul_apply]
    exact hx.polar_apply v _

theorem OddOrderIsometry.polar_aeval (hx : OddOrderIsometry Q p x) (f : K[X]) (v w : V) :
    QuadraticMap.polar Q (aeval x.toLinearMap f v) w =
      QuadraticMap.polar Q v (aeval x.symm.toLinearMap f w) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    simp only [map_add, LinearMap.add_apply, QuadraticMap.polar_add_left,
      QuadraticMap.polar_add_right, hf, hg]
  | monomial n c =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.mul_apply, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
      Module.End.one_apply]
    rw [hx.polar_pow]

theorem toLinearMap_pow (x : V ≃ₗ[K] V) (n : ℕ) : (x ^ n).toLinearMap = x.toLinearMap ^ n :=
  map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := K) (M := V)) x n

end Setup

section Primary

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

omit [FiniteDimensional K V] in
theorem OddOrderIsometry.aeval_X_pow_sub_one (hx : OddOrderIsometry Q p x) :
    aeval x.toLinearMap (X ^ p - 1 : K[X]) = 0 := by
  rw [map_sub, map_pow, aeval_X, map_one, sub_eq_zero, ← toLinearMap_pow, hx.pow_eq_one]
  rfl

omit [FiniteDimensional K V] in
theorem OddOrderIsometry.squarefree_X_pow_sub_one (hx : OddOrderIsometry Q p x) :
    Squarefree (X ^ p - 1 : K[X]) := by
  have := Polynomial.separable_X_pow_sub_C (1 : K) hx.cast_ne_zero one_ne_zero
  simpa using this.squarefree

theorem OddOrderIsometry.squarefree_minpoly (hx : OddOrderIsometry Q p x) :
    Squarefree (minpoly K x.toLinearMap) :=
  squarefree_minpoly_of_aeval_eq_zero hx.squarefree_X_pow_sub_one hx.aeval_X_pow_sub_one

theorem isCoprime_of_irreducible_monic_ne {a b : K[X]} (ha : Irreducible a) (hb : Irreducible b)
    (hma : a.Monic) (hmb : b.Monic) (hab : a ≠ b) : IsCoprime a b := by
  rw [ha.coprime_iff_not_dvd]
  intro hdvd
  exact hab (eq_of_monic_of_associated hma hmb (ha.associated_of_dvd hb hdvd))

@[expose] def isometryUnit (x : V ≃ₗ[K] V) : (Module.End K V)ˣ :=
  ⟨x.toLinearMap, x.symm.toLinearMap, LinearMap.ext fun v => x.apply_symm_apply v,
    LinearMap.ext fun v => x.symm_apply_apply v⟩

omit [FiniteDimensional K V] in
theorem isometryUnit_val (x : V ≃ₗ[K] V) : ((isometryUnit x : (Module.End K V)ˣ) : Module.End K V) =
    x.toLinearMap := rfl

omit [FiniteDimensional K V] in
theorem isometryUnit_inv_val (x : V ≃ₗ[K] V) :
    (((isometryUnit x)⁻¹ : (Module.End K V)ˣ) : Module.End K V) = x.symm.toLinearMap := rfl


section Factors

variable (hx : OddOrderIsometry Q p x)
include hx

theorem OddOrderIsometry.dvd_X_pow_sub_one {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) : h ∣ (X ^ p - 1 : K[X]) :=
  ((mem_primaryFactors.mp hh).2.2).trans (minpoly.dvd K _ hx.aeval_X_pow_sub_one)

theorem OddOrderIsometry.coeff_zero_ne {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) :
    h.coeff 0 ≠ 0 := by
  obtain ⟨g, hg⟩ := hx.dvd_X_pow_sub_one hh
  have hp : p ≠ 0 := fun h0 => hx.cast_ne_zero (by rw [h0]; simp)
  intro h0
  have := congrArg (fun f : K[X] => f.coeff 0) hg
  simp only [coeff_sub, coeff_X_pow, coeff_one, mul_coeff_zero, h0] at this
  simp [hp.symm] at this

omit hx [FiniteDimensional K V] in
theorem mem_primaryComponent_reciprocalPolynomial {h : K[X]} (h0 : h.coeff 0 ≠ 0) {v : V} :
    v ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h) ↔
      aeval x.symm.toLinearMap h v = 0 := by
  rw [mem_primaryComponent]
  have := aeval_reciprocalPolynomial_of_unit (isometryUnit x) h
  rw [isometryUnit_val, isometryUnit_inv_val] at this
  rw [this]
  simp only [LinearMap.smul_apply, Module.End.mul_apply, smul_eq_zero, inv_eq_zero, h0, false_or]
  have hinj : Function.Injective (x.toLinearMap ^ h.natDegree) := by
    rw [Module.End.coe_pow]
    exact Function.Injective.iterate x.injective h.natDegree
  exact map_eq_zero_iff _ hinj

theorem OddOrderIsometry.polar_primaryComponent_eq_zero {h k : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hk : k ∈ primaryFactors x.toLinearMap)
    (hne : k ≠ reciprocalPolynomial h) {v w : V} (hv : v ∈ primaryComponent x.toLinearMap h)
    (hw : w ∈ primaryComponent x.toLinearMap k) : QuadraticMap.polar Q v w = 0 := by
  have h0 := hx.coeff_zero_ne hh
  have hhi := irreducible_of_mem_primaryFactors hh
  have hki := irreducible_of_mem_primaryFactors hk
  set T : Module.End K V := aeval x.symm.toLinearMap h with hT
  have hcomm : Commute T x.toLinearMap :=
    (commute_aeval (r := x.toLinearMap) (x := x.symm.toLinearMap) (by
      ext u; simp) h).symm
  have hmaps : ∀ u ∈ primaryComponent x.toLinearMap k, T u ∈ primaryComponent x.toLinearMap k :=
    fun u hu => apply_mem_primaryComponent hcomm hu
  let Tk : primaryComponent x.toLinearMap k →ₗ[K] primaryComponent x.toLinearMap k :=
    T.restrict hmaps
  have hinj : Function.Injective Tk := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hTu : T (u : V) = 0 := by
      have := congrArg Subtype.val hu
      simpa [Tk] using this
    have hu' : (u : V) ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h) :=
      (mem_primaryComponent_reciprocalPolynomial h0).mpr hTu
    have hcop : IsCoprime k (reciprocalPolynomial h) :=
      isCoprime_of_irreducible_monic_ne hki (irreducible_reciprocalPolynomial hhi h0)
        (mem_primaryFactors.mp hk).2.1 (monic_reciprocalPolynomial h0) hne
    have hdisj := Polynomial.disjoint_ker_aeval_of_isCoprime x.toLinearMap hcop
    exact Subtype.ext (Submodule.disjoint_def.mp hdisj u u.2 hu')
  obtain ⟨u, hu⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨w, hw⟩
  have hu' : T (u : V) = w := congrArg Subtype.val hu
  rw [← hu', hT, ← hx.polar_aeval h v u, mem_primaryComponent.mp hv]
  simp

theorem OddOrderIsometry.eq_zero_of_polar_primaryComponent {v : V}
    (h : ∀ k ∈ primaryFactors x.toLinearMap, ∀ w ∈ primaryComponent x.toLinearMap k,
      QuadraticMap.polar Q v w = 0) : v = 0 := by
  refine hx.regular v fun w => ?_
  have hsum := congrArg (fun f : Module.End K V => f w)
    (sum_primaryProjection (x := x.toLinearMap) hx.squarefree_minpoly)
  simp only [LinearMap.sum_apply, Module.End.one_apply] at hsum
  have h1 : QuadraticMap.polar Q v w = ∑ k ∈ primaryFactors x.toLinearMap,
      QuadraticMap.polar Q v (primaryProjection x.toLinearMap k w) := by
    conv_lhs => rw [← hsum]
    exact map_sum (QuadraticMap.polarBilin Q v) _ _
  rw [h1]
  exact Finset.sum_eq_zero fun k hk =>
    h k hk _ (primaryProjection_mem hx.squarefree_minpoly hk w)

theorem OddOrderIsometry.reciprocalPolynomial_mem {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) :
    reciprocalPolynomial h ∈ primaryFactors x.toLinearMap := by
  by_contra hnot
  have hk : ∀ k ∈ primaryFactors x.toLinearMap, k ≠ reciprocalPolynomial h := fun k hk heq =>
    hnot (heq ▸ hk)
  refine primaryComponent_ne_bot hx.squarefree_minpoly hh ?_
  rw [eq_bot_iff]
  intro v hv
  exact (Submodule.mem_bot K).mpr (hx.eq_zero_of_polar_primaryComponent fun k hk' w hw =>
    hx.polar_primaryComponent_eq_zero hh hk' (hk k hk') hv hw)

theorem OddOrderIsometry.reciprocal_reciprocal_eq {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) :
    reciprocalPolynomial (reciprocalPolynomial h) = h :=
  reciprocalPolynomial_reciprocalPolynomial (mem_primaryFactors.mp hh).2.1 (hx.coeff_zero_ne hh)

theorem OddOrderIsometry.bijOn_reciprocalPolynomial :
    Set.BijOn (reciprocalPolynomial : K[X] → K[X]) (↑(primaryFactors x.toLinearMap))
      (↑(primaryFactors x.toLinearMap)) := by
  refine ⟨fun h hh => hx.reciprocalPolynomial_mem hh, fun h hh k hk hhk => ?_, fun k hk => ?_⟩
  · rw [← hx.reciprocal_reciprocal_eq hh,
      ← hx.reciprocal_reciprocal_eq hk]
    exact congrArg reciprocalPolynomial hhk
  · exact ⟨reciprocalPolynomial k, hx.reciprocalPolynomial_mem hk,
      hx.reciprocal_reciprocal_eq hk⟩

theorem OddOrderIsometry.eq_zero_of_polar_orbit {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    {u : V} (hu : u ∈ primaryComponent x.toLinearMap h ⊔
      primaryComponent x.toLinearMap (reciprocalPolynomial h))
    (hperp : ∀ w ∈ primaryComponent x.toLinearMap h ⊔
      primaryComponent x.toLinearMap (reciprocalPolynomial h), QuadraticMap.polar Q u w = 0) :
    u = 0 := by
  classical
  have hh' := hx.reciprocalPolynomial_mem hh
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
  refine hx.eq_zero_of_polar_primaryComponent fun k hk w hw => ?_
  by_cases hkh : k = h
  · subst hkh
    exact hperp w (Submodule.mem_sup_left hw)
  by_cases hkh' : k = reciprocalPolynomial h
  · subst hkh'
    exact hperp w (Submodule.mem_sup_right hw)
  rw [QuadraticMap.polar_add_left, hx.polar_primaryComponent_eq_zero hh hk hkh' hu₁ hw,
    hx.polar_primaryComponent_eq_zero hh' hk (by rwa [hx.reciprocal_reciprocal_eq hh]) hu₂ hw,
    add_zero]

theorem OddOrderIsometry.polar_eq_zero_of_ne {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hne : h ≠ reciprocalPolynomial h) {v w : V} (hv : v ∈ primaryComponent x.toLinearMap h)
    (hw : w ∈ primaryComponent x.toLinearMap h) : QuadraticMap.polar Q v w = 0 :=
  hx.polar_primaryComponent_eq_zero hh hh hne hv hw

theorem OddOrderIsometry.polar_reciprocal_eq_zero_of_ne {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ reciprocalPolynomial h) {v w : V}
    (hv : v ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h))
    (hw : w ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h)) :
    QuadraticMap.polar Q v w = 0 := by
  refine hx.polar_primaryComponent_eq_zero (hx.reciprocalPolynomial_mem hh)
    (hx.reciprocalPolynomial_mem hh) ?_ hv hw
  rwa [hx.reciprocal_reciprocal_eq hh, ne_comm]

theorem OddOrderIsometry.eq_zero_of_polar_paired_left {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) {v : V} (hv : v ∈ primaryComponent x.toLinearMap h)
    (hperp : ∀ w ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h),
      QuadraticMap.polar Q v w = 0) : v = 0 := by
  refine hx.eq_zero_of_polar_primaryComponent fun k hk w hw => ?_
  by_cases hkh' : k = reciprocalPolynomial h
  · subst hkh'
    exact hperp w hw
  · exact hx.polar_primaryComponent_eq_zero hh hk hkh' hv hw

theorem OddOrderIsometry.eq_zero_of_polar_paired_right {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) {w : V}
    (hw : w ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h))
    (hperp : ∀ v ∈ primaryComponent x.toLinearMap h, QuadraticMap.polar Q v w = 0) : w = 0 := by
  have hh' := hx.reciprocalPolynomial_mem hh
  refine hx.eq_zero_of_polar_primaryComponent fun k hk v hv => ?_
  by_cases hkh : k = h
  · subst hkh
    rw [QuadraticMap.polar_comm]
    exact hperp v hv
  · exact hx.polar_primaryComponent_eq_zero hh' hk (by rwa [hx.reciprocal_reciprocal_eq hh]) hw hv

theorem OddOrderIsometry.eq_zero_of_polar_selfdual {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hself : h = reciprocalPolynomial h) {v : V}
    (hv : v ∈ primaryComponent x.toLinearMap h)
    (hperp : ∀ w ∈ primaryComponent x.toLinearMap h, QuadraticMap.polar Q v w = 0) : v = 0 := by
  refine hx.eq_zero_of_polar_primaryComponent fun k hk w hw => ?_
  by_cases hkh : k = h
  · subst hkh
    exact hperp w hw
  · exact hx.polar_primaryComponent_eq_zero hh hk (by rwa [← hself]) hv hw

end Factors

end Primary


@[expose] noncomputable def orbitSpace {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (x : Module.End K V) (h : K[X]) : Submodule K V :=
  primaryComponent x h ⊔ primaryComponent x (reciprocalPolynomial h)

end CFSG.RankThree.PartOne.KCOrthogonal
