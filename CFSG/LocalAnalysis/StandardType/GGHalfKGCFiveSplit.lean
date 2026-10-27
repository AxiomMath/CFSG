module

public import CFSG.LocalAnalysis.StandardType.GGHalfKGCADefs
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization

public section

namespace CFSG.StandardType

open Polynomial

@[expose] noncomputable def ggKGCFiveU
    {V : Type} [AddCommGroup V] [Module GGKGCF V]
    (y : V ≃ₗ[GGKGCF] V) : Submodule GGKGCF V :=
  LinearMap.ker ((y : V →ₗ[GGKGCF] V) ^ 4 + (y : V →ₗ[GGKGCF] V) ^ 3 +
    (y : V →ₗ[GGKGCF] V) ^ 2 + (y : V →ₗ[GGKGCF] V) + 1)

private lemma ggKGCFive_coe_pow {M : Type} [AddCommGroup M] [Module GGKGCF M]
    (y : M ≃ₗ[GGKGCF] M) (n : ℕ) :
    (↑(y ^ n) : M →ₗ[GGKGCF] M) = (↑y : M →ₗ[GGKGCF] M) ^ n := by
  induction n with
  | zero => simp [LinearEquiv.coe_toLinearMap_one, Module.End.one_eq_id]
  | succ n ih => rw [pow_succ, pow_succ, LinearEquiv.coe_toLinearMap_mul, ih]

private lemma ggKGCFive_irred : Irreducible (cyclotomic 5 (ZMod 2)) := by
  refine ZMod.irreducible_of_dvd_cyclotomic_of_natDegree (p := 2) (n := 5)
    (P := cyclotomic 5 (ZMod 2)) ?_ dvd_rfl ?_
  · norm_num
  · rw [Polynomial.natDegree_cyclotomic]
    rw [show Nat.totient 5 = 4 by decide]
    symm
    rw [orderOf_eq_iff (x := ZMod.unitOfCoprime 2 _) (n := 4) (by norm_num)]
    constructor
    · apply Units.ext
      rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime]
      decide
    · intro m hm4 hm0
      interval_cases m <;>
        (intro h
         have hh := congrArg (fun u : (ZMod 5)ˣ => (u : ZMod 5)) h
         rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime] at hh
         exact absurd hh (by decide))

private lemma ggKGCFive_irred_GF : Irreducible (cyclotomic 5 (GaloisField 2 1)) := by
  have h2 : Irreducible (cyclotomic 5 (ZMod 2)) := ggKGCFive_irred
  let e : GaloisField 2 1 ≃+* ZMod 2 := (GaloisField.equivZmodP 2).toRingEquiv
  have hmap : (Polynomial.mapEquiv e) (cyclotomic 5 (GaloisField 2 1)) =
      cyclotomic 5 (ZMod 2) := by
    rw [Polynomial.mapEquiv_apply, Polynomial.map_cyclotomic]
  exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv e)).mp (by rwa [hmap])

private lemma ggKGCFive_aeval_sum {M : Type} [AddCommGroup M] [Module GGKGCF M]
    (a : M →ₗ[GGKGCF] M) (c : Fin 4 → GGKGCF) :
    aeval a (∑ i : Fin 4, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)) =
      ∑ i : Fin 4, c i • a ^ (i : ℕ) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow,
    Module.algebraMap_end_eq_smul_id, smul_mul_assoc, ← Module.End.one_eq_id, one_mul]

private lemma ggKGCFive_coeff {c : Fin 4 → GGKGCF} {i : Fin 4}
    (h : (∑ j : Fin 4, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)) = 0) :
    c i = 0 := by
  have hc := congrArg (fun p : GGKGCF[X] => p.coeff (i : ℕ)) h
  rw [Polynomial.finset_sum_coeff] at hc
  simp only [Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc
  rw [Finset.sum_eq_single i] at hc
  · simpa using hc
  · intro j _ hj
    rw [if_neg (fun hji => hj (Fin.ext hji).symm)]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private lemma ggKGCFive_linearIndependent {M : Type} [AddCommGroup M] [Module GGKGCF M]
    (a : M →ₗ[GGKGCF] M) {v : M} (hv : v ≠ 0)
    (ha : (aeval a (cyclotomic 5 GGKGCF)) v = 0) :
    LinearIndependent GGKGCF (fun i : Fin 4 => (a ^ (i : ℕ)) v) := by
  have hP : Irreducible (cyclotomic 5 GGKGCF) := ggKGCFive_irred_GF
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let p : GGKGCF[X] := ∑ i : Fin 4, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)
  have hpdeg : p.natDegree ≤ 3 := by
    change (∑ i : Fin 4, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)).natDegree ≤ 3
    refine Polynomial.natDegree_sum_le_of_forall_le (s := Finset.univ) (n := 3) _ ?_
    intro i _
    calc (Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)).natDegree ≤ (i : ℕ) :=
          Polynomial.natDegree_C_mul_X_pow_le _ _
      _ ≤ 3 := by have := i.isLt; omega
  have hp_aeval : (aeval a p) v = 0 := by
    have h1 : aeval a p = ∑ i : Fin 4, c i • a ^ (i : ℕ) := by
      simpa only [p] using ggKGCFive_aeval_sum a c
    rw [h1, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply]
    exact hc
  by_cases hp0 : p = 0
  · intro i
    exact ggKGCFive_coeff hp0
  · exfalso
    have hPN : p.natDegree < (cyclotomic 5 GGKGCF).natDegree := by
      rw [Polynomial.natDegree_cyclotomic]
      rw [show Nat.totient 5 = 4 by decide]
      omega
    have hnot : ¬ (cyclotomic 5 GGKGCF) ∣ p :=
      Polynomial.not_dvd_of_natDegree_lt hp0 hPN
    have hcop : IsCoprime (cyclotomic 5 GGKGCF) p :=
      (hP.coprime_iff_not_dvd).mpr hnot
    obtain ⟨s, t, hst⟩ := hcop
    have h2 : (aeval a (s * cyclotomic 5 GGKGCF + t * p)) v =
        (1 : M →ₗ[GGKGCF] M) v := by rw [hst, map_one]
    rw [map_add, map_mul, map_mul, LinearMap.add_apply] at h2
    change aeval a s ((aeval a (cyclotomic 5 GGKGCF)) v) +
      aeval a t ((aeval a p) v) = (1 : M →ₗ[GGKGCF] M) v at h2
    rw [ha, hp_aeval, map_zero, map_zero, add_zero, Module.End.one_apply] at h2
    exact hv h2.symm

private lemma ggKGCFive_aeval_comm {M : Type} [AddCommGroup M] [Module GGKGCF M]
    {f g : M →ₗ[GGKGCF] M} (h : g * f = f * g) (p : GGKGCF[X]) :
    g * aeval f p = aeval f p * g := by
  induction p using Polynomial.induction_on with
  | C a =>
      rw [Polynomial.aeval_C]
      exact Algebra.commute_algebraMap_right a g
  | add p q hp hq =>
      rw [map_add, mul_add, add_mul, hp, hq]
  | monomial n a ih =>
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X,
        ← mul_assoc, ih, mul_assoc, h, mul_assoc]

private lemma ggKGCFive_coprime :
    IsCoprime (Polynomial.X - 1) (cyclotomic 5 GGKGCF) := by
  have hP : Irreducible (cyclotomic 5 GGKGCF) := ggKGCFive_irred_GF
  have hne : (Polynomial.X - 1 : GGKGCF[X]) ≠ 0 := by
    simpa using (Polynomial.X_sub_C_ne_zero (1 : GGKGCF))
  have hdeg : (Polynomial.X - 1 : GGKGCF[X]).natDegree <
      (cyclotomic 5 GGKGCF).natDegree := by
    rw [Polynomial.natDegree_cyclotomic]
    rw [show (Polynomial.X - 1 : GGKGCF[X]).natDegree = 1 by
      simpa using (Polynomial.natDegree_X_sub_C (1 : GGKGCF))]
    rw [show Nat.totient 5 = 4 by decide]
    norm_num
  have hnot : ¬ (cyclotomic 5 GGKGCF) ∣ (Polynomial.X - 1 : GGKGCF[X]) :=
    Polynomial.not_dvd_of_natDegree_lt hne hdeg
  exact (hP.coprime_iff_not_dvd.mpr hnot).symm

private lemma ggKGCFive_Ueq
    {V : Type} [AddCommGroup V] [Module GGKGCF V] [FiniteDimensional GGKGCF V]
    (y : V ≃ₗ[GGKGCF] V) :
    ggKGCFiveU y = LinearMap.ker (aeval (y : V →ₗ[GGKGCF] V) (cyclotomic 5 GGKGCF)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [ggKGCFiveU, Polynomial.cyclotomic_prime]
  congr 1
  rw [map_sum]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Polynomial.aeval_X_pow,
    Polynomial.aeval_X, pow_zero, pow_one, Polynomial.aeval_one]
  abel_nf

private lemma ggKGCFive_neg_eq {M : Type} [AddCommGroup M] [Module GGKGCF M] (x : M) :
    -x = x := by
  have h1 : (-1 : GGKGCF) = 1 := CharTwo.neg_eq 1
  calc -x = (-1 : GGKGCF) • x := by rw [neg_smul, one_smul]
    _ = (1 : GGKGCF) • x := by rw [h1]
    _ = x := one_smul _ _

private lemma ggKGCFive_rel
    {V : Type} [AddCommGroup V] [Module GGKGCF V] [FiniteDimensional GGKGCF V]
    (y : V ≃ₗ[GGKGCF] V) {v : V} (hv : v ∈ ggKGCFiveU y) :
    ((y : V →ₗ[GGKGCF] V) ^ 4) v =
      ((y : V →ₗ[GGKGCF] V) ^ 3) v + ((y : V →ₗ[GGKGCF] V) ^ 2) v +
        (y : V →ₗ[GGKGCF] V) v + v := by
  set f : V →ₗ[GGKGCF] V := (y : V →ₗ[GGKGCF] V) with hf
  have h0 : ((f ^ 4 + f ^ 3 + f ^ 2 + f + (1 : V →ₗ[GGKGCF] V))) v = 0 := by
    rw [ggKGCFiveU] at hv
    exact LinearMap.mem_ker.mp hv
  have h : (f ^ 4) v + ((f ^ 3) v + (f ^ 2) v + f v + v) = 0 := by
    simpa only [LinearMap.add_apply, Module.End.one_apply, add_assoc] using h0
  rw [hf]
  calc (f ^ 4) v = -((f ^ 3) v + (f ^ 2) v + f v + v) :=
        (neg_eq_of_add_eq_zero_left h).symm
    _ = (f ^ 3) v + (f ^ 2) v + f v + v := ggKGCFive_neg_eq _

private lemma ggKGCFive_orbit_mem {M : Type} [AddCommGroup M] [Module GGKGCF M]
    {f : M →ₗ[GGKGCF] M} {C : Submodule GGKGCF M}
    (hstab : ∀ x ∈ C, f x ∈ C) {z : M} (hz : z ∈ C) :
    ∀ i : Fin 4, (f ^ (i : ℕ)) z ∈ C := by
  intro i
  have h : ∀ n : ℕ, (f ^ n) z ∈ C := by
    intro n
    induction n with
    | zero => simpa using hz
    | succ n ih => rw [pow_succ']; exact hstab _ ih
  exact h (i : ℕ)

private lemma ggKGCFive_orbit_stable
    {V : Type} [AddCommGroup V] [Module GGKGCF V] [FiniteDimensional GGKGCF V]
    (y : V ≃ₗ[GGKGCF] V) {v : V}
    (hv : v ∈ ggKGCFiveU y) :
    ∀ x ∈ Submodule.span GGKGCF
      (Set.range (fun i : Fin 4 => ((y : V →ₗ[GGKGCF] V) ^ (i : ℕ)) v)),
      (y : V →ₗ[GGKGCF] V) x ∈ Submodule.span GGKGCF
        (Set.range (fun i : Fin 4 => ((y : V →ₗ[GGKGCF] V) ^ (i : ℕ)) v)) := by
  set f : V →ₗ[GGKGCF] V := (y : V →ₗ[GGKGCF] V) with hf
  have hrel : (f ^ 4) v = (f ^ 3) v + (f ^ 2) v + f v + v := by
    rw [hf]
    exact ggKGCFive_rel y hv
  have hgen : ∀ i : Fin 4, f ((f ^ (i : ℕ)) v) ∈
      Submodule.span GGKGCF (Set.range (fun i : Fin 4 => (f ^ (i : ℕ)) v)) := by
    intro i
    fin_cases i
    · have h1 : f ((f ^ (0 : ℕ)) v) = (f ^ ((1 : Fin 4) : ℕ)) v := by
        change (f * f ^ (0 : ℕ)) v = (f ^ (1 : ℕ)) v
        rw [← pow_succ']
      rw [h1]
      exact Submodule.subset_span (Set.mem_range.mpr ⟨(1 : Fin 4), rfl⟩)
    · have h2 : f ((f ^ (1 : ℕ)) v) = (f ^ ((2 : Fin 4) : ℕ)) v := by
        change (f * f ^ (1 : ℕ)) v = (f ^ (2 : ℕ)) v
        rw [← pow_succ']
      rw [h2]
      exact Submodule.subset_span (Set.mem_range.mpr ⟨(2 : Fin 4), rfl⟩)
    · have h3 : f ((f ^ (2 : ℕ)) v) = (f ^ ((3 : Fin 4) : ℕ)) v := by
        change (f * f ^ (2 : ℕ)) v = (f ^ (3 : ℕ)) v
        rw [← pow_succ']
      rw [h3]
      exact Submodule.subset_span (Set.mem_range.mpr ⟨(3 : Fin 4), rfl⟩)
    · have h4 : f ((f ^ (3 : ℕ)) v) = (f ^ 3) v + (f ^ 2) v + f v + v := by
        change (f ^ 4) v = (f ^ 3) v + (f ^ 2) v + f v + v
        exact hrel
      rw [h4]
      exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
        (Submodule.subset_span (Set.mem_range.mpr ⟨(3 : Fin 4), rfl⟩))
        (Submodule.subset_span (Set.mem_range.mpr ⟨(2 : Fin 4), rfl⟩)))
        (Submodule.subset_span (Set.mem_range.mpr ⟨(1 : Fin 4), rfl⟩)))
        (Submodule.subset_span (Set.mem_range.mpr ⟨(0 : Fin 4), rfl⟩))
  have hstab : Submodule.span GGKGCF (Set.range (fun i : Fin 4 => (f ^ (i : ℕ)) v)) ≤
      (Submodule.span GGKGCF (Set.range (fun i : Fin 4 => (f ^ (i : ℕ)) v))).comap f := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact hgen i
  intro x hx
  exact Submodule.mem_comap.mp (hstab hx)

private lemma ggKGCFive_span_finrank
    {V : Type} [AddCommGroup V] [Module GGKGCF V] [FiniteDimensional GGKGCF V]
    (y : V ≃ₗ[GGKGCF] V) {v : V}
    (hv : v ∈ ggKGCFiveU y) (hv0 : v ≠ 0) :
    Module.finrank GGKGCF (Submodule.span GGKGCF
      (Set.range (fun i : Fin 4 => ((y : V →ₗ[GGKGCF] V) ^ (i : ℕ)) v))) = 4 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have ha : (aeval (y : V →ₗ[GGKGCF] V) (cyclotomic 5 GGKGCF)) v = 0 := by
    rw [ggKGCFive_Ueq y, LinearMap.mem_ker] at hv
    exact hv
  have hli := ggKGCFive_linearIndependent (y : V →ₗ[GGKGCF] V) hv0 ha
  simpa using finrank_span_eq_card hli

theorem ggKGCFive_isCompl
    {V : Type} [AddCommGroup V] [Module GGKGCF V] [FiniteDimensional GGKGCF V]
    (y : V ≃ₗ[GGKGCF] V) (hy : y ^ 5 = 1) :
    IsCompl (ggKGCAFix y) (ggKGCFiveU y) := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hcop := ggKGCFive_coprime
  set f : V →ₗ[GGKGCF] V := (y : V →ₗ[GGKGCF] V) with hf
  have hFix : ggKGCAFix y = LinearMap.ker (aeval f (Polynomial.X - 1 : GGKGCF[X])) := by
    rw [ggKGCAFix, hf]
    congr 1
    rw [Polynomial.aeval_sub, Polynomial.aeval_X, Polynomial.aeval_one]
  have hU : ggKGCFiveU y = LinearMap.ker (aeval f (cyclotomic 5 GGKGCF)) := by
    rw [ggKGCFive_Ueq y, hf]
  have hdisj : Disjoint (LinearMap.ker (aeval f (Polynomial.X - 1 : GGKGCF[X])))
      (LinearMap.ker (aeval f (cyclotomic 5 GGKGCF))) :=
    Polynomial.disjoint_ker_aeval_of_isCoprime f hcop
  have hsup : LinearMap.ker (aeval f (Polynomial.X - 1 : GGKGCF[X])) ⊔
      LinearMap.ker (aeval f (cyclotomic 5 GGKGCF)) = ⊤ := by
    rw [Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hcop]
    have hprod : (Polynomial.X - 1 : GGKGCF[X]) * cyclotomic 5 GGKGCF = Polynomial.X ^ 5 - (1 : GGKGCF[X]) := by
      rw [mul_comm, Polynomial.cyclotomic_prime_mul_X_sub_one]
    rw [hprod]
    have hzero : aeval f (Polynomial.X ^ 5 - (1 : GGKGCF[X])) = 0 := by
      rw [Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_one]
      have hf5 : f ^ 5 = 1 := by
        rw [hf, ← ggKGCFive_coe_pow y 5, hy, LinearEquiv.coe_toLinearMap_one,
          Module.End.one_eq_id]
      rw [hf5, sub_self]
    rw [hzero, LinearMap.ker_zero]
  rw [hFix, hU]
  exact ⟨hdisj, codisjoint_iff.mpr hsup⟩

theorem ggKGCFive_stable
    {V : Type} [AddCommGroup V] [Module GGKGCF V] [FiniteDimensional GGKGCF V]
    {y g : V ≃ₗ[GGKGCF] V} (hgy : g * y = y * g) :
    (∀ w ∈ ggKGCAFix y, g w ∈ ggKGCAFix y) ∧ (∀ u ∈ ggKGCFiveU y, g u ∈ ggKGCFiveU y) := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  set f : V →ₗ[GGKGCF] V := (y : V →ₗ[GGKGCF] V) with hf
  have hcomm : (g : V →ₗ[GGKGCF] V) * f = f * (g : V →ₗ[GGKGCF] V) := by
    have h := congrArg (fun z : V ≃ₗ[GGKGCF] V => (z : V →ₗ[GGKGCF] V)) hgy
    rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul] at h
    rw [hf]
    exact h
  have hcomm' := ggKGCFive_aeval_comm hcomm
  have hFix : ggKGCAFix y = LinearMap.ker (aeval f (Polynomial.X - 1 : GGKGCF[X])) := by
    rw [ggKGCAFix, hf]
    congr 1
    rw [Polynomial.aeval_sub, Polynomial.aeval_X, Polynomial.aeval_one]
  have hU : ggKGCFiveU y = LinearMap.ker (aeval f (cyclotomic 5 GGKGCF)) := by
    rw [ggKGCFive_Ueq y, hf]
  constructor
  · intro w hw
    rw [hFix, LinearMap.mem_ker] at hw ⊢
    have h2 := congrArg (fun h : V →ₗ[GGKGCF] V => h w) (hcomm' (Polynomial.X - 1))
    change (g : V →ₗ[GGKGCF] V) ((aeval f (Polynomial.X - 1 : GGKGCF[X])) w) =
      (aeval f (Polynomial.X - 1 : GGKGCF[X])) ((g : V →ₗ[GGKGCF] V) w) at h2
    rw [hw, map_zero] at h2
    exact h2.symm
  · intro u hu
    rw [hU, LinearMap.mem_ker] at hu ⊢
    have h2 := congrArg (fun h : V →ₗ[GGKGCF] V => h u) (hcomm' (cyclotomic 5 GGKGCF))
    change (g : V →ₗ[GGKGCF] V) ((aeval f (cyclotomic 5 GGKGCF)) u) =
      (aeval f (cyclotomic 5 GGKGCF)) ((g : V →ₗ[GGKGCF] V) u) at h2
    rw [hu, map_zero] at h2
    exact h2.symm

private lemma ggKGCFive_U_stable_y
    {V : Type} [AddCommGroup V] [Module GGKGCF V] [FiniteDimensional GGKGCF V]
    (y : V ≃ₗ[GGKGCF] V) :
    ∀ u ∈ ggKGCFiveU y, (y : V →ₗ[GGKGCF] V) u ∈ ggKGCFiveU y :=
  (ggKGCFive_stable (y := y) (g := y) rfl).2

theorem ggKGCFive_finrank_U
    {V : Type} [AddCommGroup V] [Module GGKGCF V] [FiniteDimensional GGKGCF V]
    (y : V ≃ₗ[GGKGCF] V) (hy : y ^ 5 = 1) (hy1 : y ≠ 1)
    (hV : Module.finrank GGKGCF V = 6) : Module.finrank GGKGCF (ggKGCFiveU y) = 4 := by
  have hcompl := ggKGCFive_isCompl y hy
  have hUne : ggKGCFiveU y ≠ ⊥ := by
    intro hbot
    have htop : ggKGCAFix y = ⊤ := by
      have hc := hcompl.2
      rw [codisjoint_iff] at hc
      rwa [hbot, sup_bot_eq] at hc
    apply hy1
    apply LinearEquiv.ext
    intro v
    have hv : v ∈ ggKGCAFix y := by rw [htop]; exact Submodule.mem_top
    rw [ggKGCAFix, LinearMap.mem_ker] at hv
    have := sub_eq_zero.mp hv
    simpa [Module.End.one_apply] using this
  obtain ⟨u₀, hu₀U, hu₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
  set f : V →ₗ[GGKGCF] V := (y : V →ₗ[GGKGCF] V) with hf
  let C : Submodule GGKGCF V :=
    Submodule.span GGKGCF (Set.range (fun i : Fin 4 => (f ^ (i : ℕ)) u₀))
  have hCfin : Module.finrank GGKGCF C = 4 := by
    change Module.finrank GGKGCF (Submodule.span GGKGCF
      (Set.range (fun i : Fin 4 => (f ^ (i : ℕ)) u₀))) = 4
    exact ggKGCFive_span_finrank y hu₀U hu₀ne
  have hCU : C ≤ ggKGCFiveU y := by
    change Submodule.span GGKGCF (Set.range (fun i : Fin 4 => (f ^ (i : ℕ)) u₀)) ≤
      ggKGCFiveU y
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    have h : ∀ n : ℕ, (f ^ n) u₀ ∈ ggKGCFiveU y := by
      intro n
      induction n with
      | zero => simpa using hu₀U
      | succ n ih => rw [pow_succ']; exact ggKGCFive_U_stable_y y _ ih
    exact h (i : ℕ)
  have hCstab : ∀ x ∈ C, f x ∈ C := by
    change ∀ x ∈ Submodule.span GGKGCF (Set.range (fun i : Fin 4 => (f ^ (i : ℕ)) u₀)),
      f x ∈ Submodule.span GGKGCF (Set.range (fun i : Fin 4 => (f ^ (i : ℕ)) u₀))
    exact ggKGCFive_orbit_stable y hu₀U
  have hCUeq : C = ggKGCFiveU y := by
    by_contra hne
    have hlt : C < ggKGCFiveU y := lt_of_le_of_ne hCU hne
    have hnotle : ¬ ggKGCFiveU y ≤ C := hlt.not_ge
    rw [SetLike.le_def] at hnotle
    push Not at hnotle
    obtain ⟨u₁, hu₁U, hu₁C⟩ := hnotle
    have hu₁ne : u₁ ≠ 0 := by
      intro h
      exact hu₁C (h ▸ C.zero_mem)
    let C₁ : Submodule GGKGCF V :=
      Submodule.span GGKGCF (Set.range (fun i : Fin 4 => (f ^ (i : ℕ)) u₁))
    have hC₁fin : Module.finrank GGKGCF C₁ = 4 := by
      change Module.finrank GGKGCF (Submodule.span GGKGCF
        (Set.range (fun i : Fin 4 => (f ^ (i : ℕ)) u₁))) = 4
      exact ggKGCFive_span_finrank y hu₁U hu₁ne
    have hC₁stab : ∀ x ∈ C₁, f x ∈ C₁ := by
      change ∀ x ∈ Submodule.span GGKGCF (Set.range (fun i : Fin 4 => (f ^ (i : ℕ)) u₁)),
        f x ∈ Submodule.span GGKGCF (Set.range (fun i : Fin 4 => (f ^ (i : ℕ)) u₁))
      exact ggKGCFive_orbit_stable y hu₁U
    have hdim : Module.finrank GGKGCF ↥(C ⊔ C₁) + Module.finrank GGKGCF ↥(C ⊓ C₁) =
        Module.finrank GGKGCF ↥C + Module.finrank GGKGCF ↥C₁ :=
      Submodule.finrank_sup_add_finrank_inf_eq C C₁
    have hsup_le : Module.finrank GGKGCF ↥(C ⊔ C₁) ≤ 6 := by
      have := Submodule.finrank_le (C ⊔ C₁)
      rwa [hV] at this
    have hinf_ge : 2 ≤ Module.finrank GGKGCF ↥(C ⊓ C₁) := by omega
    have hinf_ne : C ⊓ C₁ ≠ ⊥ := by
      intro hbot
      rw [hbot] at hinf_ge
      simp at hinf_ge
    obtain ⟨z, hzinf, hzne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf_ne
    have hzC : z ∈ C := hzinf.1
    have hzC₁ : z ∈ C₁ := hzinf.2
    have hzU : z ∈ ggKGCFiveU y := hCU hzC
    have hzfin : Module.finrank GGKGCF (Submodule.span GGKGCF
        (Set.range (fun i : Fin 4 => (f ^ (i : ℕ)) z))) = 4 := by
      change Module.finrank GGKGCF (Submodule.span GGKGCF
        (Set.range (fun i : Fin 4 => ((y : V →ₗ[GGKGCF] V) ^ (i : ℕ)) z))) = 4
      exact ggKGCFive_span_finrank y hzU hzne
    have hzle : Submodule.span GGKGCF (Set.range (fun i : Fin 4 => (f ^ (i : ℕ)) z)) ≤
        C ⊓ C₁ := by
      apply le_inf
      · rw [Submodule.span_le]
        rintro x ⟨i, rfl⟩
        exact ggKGCFive_orbit_mem hCstab hzC i
      · rw [Submodule.span_le]
        rintro x ⟨i, rfl⟩
        exact ggKGCFive_orbit_mem hC₁stab hzC₁ i
    have hfour : 4 ≤ Module.finrank GGKGCF ↥(C ⊓ C₁) := by
      rw [← hzfin]
      exact Submodule.finrank_mono hzle
    have hle4 : Module.finrank GGKGCF ↥(C ⊓ C₁) ≤ 4 := by
      calc Module.finrank GGKGCF ↥(C ⊓ C₁) ≤ Module.finrank GGKGCF ↥C :=
            Submodule.finrank_mono inf_le_left
        _ = 4 := hCfin
    have hinf_eq : Module.finrank GGKGCF ↥(C ⊓ C₁) = 4 := le_antisymm hle4 hfour
    have hCeq : C ⊓ C₁ = C :=
      Submodule.eq_of_le_of_finrank_le inf_le_left (by rw [hCfin, hinf_eq])
    have hC₁eq : C ⊓ C₁ = C₁ :=
      Submodule.eq_of_le_of_finrank_le inf_le_right (by rw [hC₁fin, hinf_eq])
    have hCC₁ : C = C₁ := by rw [← hCeq, hC₁eq]
    have hu₁C₁ : u₁ ∈ C₁ := Submodule.subset_span (Set.mem_range.mpr ⟨(0 : Fin 4), rfl⟩)
    exact hu₁C (hCC₁.symm ▸ hu₁C₁)
  rw [← hCUeq, hCfin]

theorem ggKGCFive_commutant
    {V : Type} [AddCommGroup V] [Module GGKGCF V] [FiniteDimensional GGKGCF V]
    (y : V ≃ₗ[GGKGCF] V) (hy : y ^ 5 = 1)
    (hU : Module.finrank GGKGCF (ggKGCFiveU y) = 4) {g : V ≃ₗ[GGKGCF] V} (hgy : g * y = y * g) :
    ∃ c : Fin 4 → GGKGCF, ∀ u ∈ ggKGCFiveU y,
      g u = ∑ i : Fin 4, c i • (y ^ (i : ℕ)) u := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  set f : V →ₗ[GGKGCF] V := (y : V →ₗ[GGKGCF] V) with hf
  have hUne : ggKGCFiveU y ≠ ⊥ := by
    intro hbot
    rw [hbot] at hU
    simp at hU
  obtain ⟨u₀, hu₀U, hu₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
  have hu₀aeval : (aeval f (cyclotomic 5 GGKGCF)) u₀ = 0 := by
    rw [ggKGCFive_Ueq y, LinearMap.mem_ker] at hu₀U
    exact hu₀U
  have hli : LinearIndependent GGKGCF (fun i : Fin 4 => (f ^ (i : ℕ)) u₀) :=
    ggKGCFive_linearIndependent f hu₀ne hu₀aeval
  let b : Fin 4 → V := fun i => (f ^ (i : ℕ)) u₀
  have hmem : ∀ i : Fin 4, b i ∈ ggKGCFiveU y := by
    intro i
    have h : ∀ n : ℕ, (f ^ n) u₀ ∈ ggKGCFiveU y := by
      intro n
      induction n with
      | zero => simpa using hu₀U
      | succ n ih => rw [pow_succ']; exact ggKGCFive_U_stable_y y _ ih
    exact h (i : ℕ)
  have hspan : Submodule.span GGKGCF (Set.range b) = ggKGCFiveU y := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      exact hmem i
    · rw [finrank_span_eq_card hli, hU]
      simp
  have hgu₀U : g u₀ ∈ ggKGCFiveU y :=
    (ggKGCFive_stable (y := y) (g := g) hgy).2 u₀ hu₀U
  have hmem_span : g u₀ ∈ Submodule.span GGKGCF (Set.range b) := by
    rw [hspan]
    exact hgu₀U
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (v := b) GGKGCF).mp hmem_span
  refine ⟨c, ?_⟩
  have hc' : g u₀ = ∑ i : Fin 4, c i • b i := hc.symm
  let T : V →ₗ[GGKGCF] V := ∑ i : Fin 4, c i • f ^ (i : ℕ)
  have hTu₀ : T u₀ = g u₀ := by
    rw [hc']
    simp only [T, LinearMap.sum_apply, LinearMap.smul_apply, b]
  have hcomm_base : (g : V →ₗ[GGKGCF] V) * f = f * (g : V →ₗ[GGKGCF] V) := by
    have h := congrArg (fun z : V ≃ₗ[GGKGCF] V => (z : V →ₗ[GGKGCF] V)) hgy
    rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul] at h
    rw [hf]
    exact h
  have hgcomm : ∀ n : ℕ, (g : V →ₗ[GGKGCF] V) * f ^ n = f ^ n * (g : V →ₗ[GGKGCF] V) := by
    intro n
    induction n with
    | zero => rw [pow_zero, mul_one, one_mul]
    | succ n ih =>
        rw [pow_succ']
        calc (g : V →ₗ[GGKGCF] V) * (f * f ^ n) = ((g : V →ₗ[GGKGCF] V) * f) * f ^ n :=
              (mul_assoc _ _ _).symm
          _ = (f * (g : V →ₗ[GGKGCF] V)) * f ^ n := by rw [hcomm_base]
          _ = f * ((g : V →ₗ[GGKGCF] V) * f ^ n) := mul_assoc _ _ _
          _ = f * (f ^ n * (g : V →ₗ[GGKGCF] V)) := by rw [ih]
          _ = (f * f ^ n) * (g : V →ₗ[GGKGCF] V) := (mul_assoc _ _ _).symm
  have hTcomm : ∀ n : ℕ, T * f ^ n = f ^ n * T := by
    intro n
    rw [show T = ∑ i : Fin 4, c i • f ^ (i : ℕ) from rfl, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_mul_assoc, mul_smul_comm, ← pow_add, ← pow_add, Nat.add_comm]
  have hmain : ∀ x ∈ Submodule.span GGKGCF (Set.range b), g x = T x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        have h1 : g (b i) = (f ^ (i : ℕ)) (g u₀) := by
          have h := congrArg (fun h : V →ₗ[GGKGCF] V => h u₀) (hgcomm (i : ℕ))
          change g ((f ^ (i : ℕ)) u₀) = (f ^ (i : ℕ)) (g u₀) at h
          simpa only [b] using h
        have h2 : T (b i) = (f ^ (i : ℕ)) (g u₀) := by
          have h := congrArg (fun h : V →ₗ[GGKGCF] V => h u₀) (hTcomm (i : ℕ))
          change T ((f ^ (i : ℕ)) u₀) = (f ^ (i : ℕ)) (T u₀) at h
          rw [hTu₀] at h
          simpa only [b] using h
        rw [h1, h2]
    | zero => simp
    | add y z hy hz ihy ihz => rw [map_add, map_add, ihy, ihz]
    | smul a y hy ihy => rw [map_smul, map_smul, ihy]
  intro u hu
  rw [hmain u (by rw [hspan]; exact hu)]
  simp only [T, LinearMap.sum_apply, LinearMap.smul_apply]
  rfl

end CFSG.StandardType

end
