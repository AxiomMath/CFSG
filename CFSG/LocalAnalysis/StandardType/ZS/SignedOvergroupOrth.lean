module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.GGWitSlpmConjAux
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.ZS.ClassReflClosure
import CFSG.LocalAnalysis.StandardType.ZS.ClassReflOrder
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
import CFSG.LocalAnalysis.StandardType.ZS.MonomialStab
import CFSG.LocalAnalysis.StandardType.GGWitSlpm

public section

namespace CFSG.StandardType.ZS

open QuadraticMap

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U] {n : ℕ}

private lemma exists_coords_ne {n m : ℕ} (hm : m + 1 ≤ n) (i₀ : Fin n) :
    ∃ a : Fin m → Fin n, Function.Injective a ∧ ∀ k, a k ≠ i₀ := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  refine ⟨fun k => i₀.succAbove (Fin.castLE (by omega : m ≤ N) k), ?_, ?_⟩
  · intro x y hxy
    exact Fin.castLE_injective _ (Fin.succAbove_right_injective hxy)
  · intro k
    exact Fin.succAbove_ne i₀ _

private noncomputable def coefRoot {m : ℕ} (b : Module.Basis (Fin n) (ZMod p) U)
    (a : Fin m → Fin n) (c : Fin m → ZMod p) : U :=
  ∑ k, c k • b (a k)

private noncomputable def coefForm {m : ℕ} (b : Module.Basis (Fin n) (ZMod p) U)
    (a : Fin m → Fin n) (c : Fin m → ZMod p) : Module.Dual (ZMod p) U :=
  ∑ k, c k • b.coord (a k)

private noncomputable def coefReflForm {m : ℕ} (b : Module.Basis (Fin n) (ZMod p) U)
    (a : Fin m → Fin n) (c : Fin m → ZMod p) : Module.Dual (ZMod p) U :=
  (2 * (∑ k, c k * c k)⁻¹) • coefForm b a c

private lemma coord_coefRoot {m : ℕ} (b : Module.Basis (Fin n) (ZMod p) U)
    (a : Fin m → Fin n) (c : Fin m → ZMod p) (hinj : Function.Injective a)
    (j : Fin m) : b.coord (a j) (coefRoot b a c) = c j := by
  rw [coefRoot, map_sum]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    have hak : a j ≠ a k := fun h => hk (hinj h).symm
    simp [hak]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

private lemma coefForm_coefRoot {m : ℕ} (b : Module.Basis (Fin n) (ZMod p) U)
    (a : Fin m → Fin n) (c : Fin m → ZMod p) (hinj : Function.Injective a) :
    coefForm b a c (coefRoot b a c) = ∑ k, c k * c k := by
  rw [coefForm]
  change (∑ k ∈ Finset.univ, c k • b.coord (a k)) (coefRoot b a c) =
    ∑ k, c k * c k
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, coord_coefRoot b a c hinj, smul_eq_mul]

private lemma coefForm_apply_basis_ne {m : ℕ} (b : Module.Basis (Fin n) (ZMod p) U)
    (a : Fin m → Fin n) (c : Fin m → ZMod p) {i : Fin n} (hi : ∀ k, i ≠ a k) :
    coefForm b a c (b i) = 0 := by
  rw [coefForm]
  change (∑ k ∈ Finset.univ, c k • b.coord (a k)) (b i) = 0
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self_apply,
    smul_eq_mul]
  simp [hi]

private lemma coord_sum_basis (b : Module.Basis (Fin n) (ZMod p) U) (k : Fin n) :
    b.coord k (∑ i, b i) = 1 := by
  rw [map_sum]
  simp

private lemma coefForm_apply_sum_basis {m : ℕ} (b : Module.Basis (Fin n) (ZMod p) U)
    (a : Fin m → Fin n) (c : Fin m → ZMod p) :
    coefForm b a c (∑ i, b i) = ∑ k, c k := by
  rw [coefForm]
  change (∑ k ∈ Finset.univ, c k • b.coord (a k)) (∑ i, b i) = ∑ k, c k
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, coord_sum_basis, smul_eq_mul, mul_one]

private lemma coefForm_apply_basis {m : ℕ} (b : Module.Basis (Fin n) (ZMod p) U)
    (a : Fin m → Fin n) (c : Fin m → ZMod p) (hinj : Function.Injective a)
    (j : Fin m) : coefForm b a c (b (a j)) = c j := by
  rw [coefForm]
  change (∑ k ∈ Finset.univ, c k • b.coord (a k)) (b (a j)) = c j
  rw [LinearMap.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    have hak : a j ≠ a k := fun h => hk (hinj h).symm
    simp [hak]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

private lemma coefReflForm_apply_basis {m : ℕ} (b : Module.Basis (Fin n) (ZMod p) U)
    (a : Fin m → Fin n) (c : Fin m → ZMod p) (hinj : Function.Injective a)
    (j : Fin m) :
    coefReflForm b a c (b (a j)) = (2 * (∑ k, c k * c k)⁻¹) * c j := by
  rw [coefReflForm, LinearMap.smul_apply, coefForm_apply_basis b a c hinj j, smul_eq_mul]

private lemma two_mul_inv_four (hp : p ≠ 2) :
    (2 : ZMod p) * (4 : ZMod p)⁻¹ = (2 : ZMod p)⁻¹ := by
  have h2 : (2 : ZMod p) ≠ 0 := wSlpmC_two_ne_zero hp
  rw [show (4 : ZMod p) = 2 * 2 by norm_num, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ h2, one_mul]

private lemma two_smul_coord_apply_self (b : Module.Basis (Fin n) (ZMod p) U) (k : Fin n) :
    ((2 : ZMod p) • b.coord k) (b k) = 2 := by
  simp

private lemma signChange_eq_reflection (b : Module.Basis (Fin n) (ZMod p) U) (k : Fin n) :
    diagMap p b (fun j => if j = k then -1 else 1) =
      Module.reflection (x := b k) (f := (2 : ZMod p) • b.coord k)
        (two_smul_coord_apply_self b k) := by
  refine b.ext' fun i => ?_
  rw [diagMap_apply_basis, Module.reflection_apply]
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl, Units.val_neg, Units.val_one, neg_one_smul,
      show ((2 : ZMod p) • b.coord i) (b i) = 2 from two_smul_coord_apply_self b i, two_smul]
    abel
  · rw [if_neg hik, Units.val_one, one_smul,
      show ((2 : ZMod p) • b.coord k) (b i) = 0 by simp [hik], zero_smul, sub_zero]


private lemma one_sub_inv_two (hp : p ≠ 2) :
    (1 : ZMod p) - (2 : ZMod p)⁻¹ = (2 : ZMod p)⁻¹ := by
  have h2 : (2 : ZMod p) ≠ 0 := wSlpmC_two_ne_zero hp
  have h : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  calc (1 : ZMod p) - 2⁻¹ = (2 * 2⁻¹) - 2⁻¹ := by rw [h]
    _ = 2⁻¹ := by ring

private lemma Q_basis_eq (b : Module.Basis (Fin n) (ZMod p) U) {Q : QuadraticForm (ZMod p) U}
    (hP : ∀ σ, IsIsom p Q (permMap p b σ)) (i₀ k : Fin n) :
    Q (b k) = Q (b i₀) := by
  have h := hP (Equiv.swap i₀ k) (b i₀)
  rwa [permMap_apply_basis, Equiv.swap_apply_left] at h

private lemma polar_basis_eq_zero (hp : p ≠ 2) (b : Module.Basis (Fin n) (ZMod p) U)
    {Q : QuadraticForm (ZMod p) U}
    (hS : ∀ i, IsIsom p Q (diagMap p b (fun j => if j = i then -1 else 1)))
    {i k : Fin n} (hik : i ≠ k) : polar Q (b i) (b k) = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := wSlpmC_two_ne_zero hp
  have hiso := hS i (b i + b k)
  have hmove : diagMap p b (fun j => if j = i then -1 else 1) (b i + b k) = -b i + b k := by
    rw [map_add, diagMap_apply_basis, diagMap_apply_basis]
    simp [show k ≠ i from hik.symm]
  rw [hmove] at hiso
  have h1 : Q (b i + b k) = Q (b i) + Q (b k) + polar Q (b i) (b k) :=
    QuadraticMap.map_add Q (b i) (b k)
  have h2' : Q (-b i + b k) = Q (b i) + Q (b k) - polar Q (b i) (b k) := by
    rw [QuadraticMap.map_add Q (-b i) (b k), QuadraticMap.map_neg Q (b i),
      QuadraticMap.polar_neg_left Q (b i) (b k)]
    ring
  have hEq : Q (b i) + Q (b k) + polar Q (b i) (b k)
      = Q (b i) + Q (b k) - polar Q (b i) (b k) := by
    rw [← h1, ← h2']
    exact hiso.symm
  have hpneg : polar Q (b i) (b k) = -polar Q (b i) (b k) := by
    have h' : Q (b i) + Q (b k) + polar Q (b i) (b k)
        = Q (b i) + Q (b k) + (-polar Q (b i) (b k)) := by
      simpa [sub_eq_add_neg] using hEq
    exact add_left_cancel h'
  have h2p : (2 : ZMod p) * polar Q (b i) (b k) = 0 := by
    calc (2 : ZMod p) * polar Q (b i) (b k)
        = polar Q (b i) (b k) + polar Q (b i) (b k) := two_mul _
      _ = -polar Q (b i) (b k) + polar Q (b i) (b k) := by
        nth_rewrite 1 [hpneg]
        rfl
      _ = 0 := neg_add_cancel _
  exact (mul_eq_zero.mp h2p).resolve_left h2

private lemma flip_polarBilin_basis (hp : p ≠ 2) (b : Module.Basis (Fin n) (ZMod p) U)
    {Q : QuadraticForm (ZMod p) U}
    (hS : ∀ i, IsIsom p Q (diagMap p b (fun j => if j = i then -1 else 1)))
    (k : Fin n) :
    (QuadraticMap.polarBilin Q).flip (b k) = (2 * Q (b k)) • b.coord k := by
  refine b.ext fun i => ?_
  rw [LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply, LinearMap.smul_apply,
    Module.Basis.coord_apply, Module.Basis.repr_self_apply]
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl, smul_eq_mul, mul_one, QuadraticMap.polar_self, nsmul_eq_mul]
    norm_num
  · rw [if_neg hik, smul_zero]
    exact polar_basis_eq_zero hp b hS hik

private lemma flip_polarBilin_coefRoot {m : ℕ} (hp : p ≠ 2)
    (b : Module.Basis (Fin n) (ZMod p) U) (a : Fin m → Fin n) (c : Fin m → ZMod p)
    {Q : QuadraticForm (ZMod p) U} (hP : ∀ σ, IsIsom p Q (permMap p b σ))
    (hS : ∀ i, IsIsom p Q (diagMap p b (fun j => if j = i then -1 else 1)))
    (i₀ : Fin n) :
    (QuadraticMap.polarBilin Q).flip (coefRoot b a c) =
      (2 * Q (b i₀)) • coefForm b a c := by
  rw [coefRoot, map_sum]
  simp only [map_smul]
  have hb : ∀ k : Fin m,
      (QuadraticMap.polarBilin Q).flip (b (a k)) = (2 * Q (b i₀)) • b.coord (a k) := by
    intro k
    rw [flip_polarBilin_basis hp b hS (a k), Q_basis_eq b hP i₀ (a k)]
  simp only [hb]
  rw [coefForm, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [smul_smul, smul_smul, mul_comm (c k) (2 * Q (b i₀))]

private lemma Q_coefRoot {m : ℕ} (hp : p ≠ 2) (b : Module.Basis (Fin n) (ZMod p) U)
    (a : Fin m → Fin n) (c : Fin m → ZMod p) (hinj : Function.Injective a)
    {Q : QuadraticForm (ZMod p) U} (hP : ∀ σ, IsIsom p Q (permMap p b σ))
    (hS : ∀ i, IsIsom p Q (diagMap p b (fun j => if j = i then -1 else 1)))
    (i₀ : Fin n) :
    Q (coefRoot b a c) = (∑ k, c k * c k) * Q (b i₀) := by
  have h2 : (2 : ZMod p) ≠ 0 := wSlpmC_two_ne_zero hp
  have h := congrArg (fun g : Module.Dual (ZMod p) U => g (coefRoot b a c))
    (flip_polarBilin_coefRoot hp b a c hP hS i₀)
  rw [LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply, LinearMap.smul_apply,
    QuadraticMap.polar_self, nsmul_eq_mul, coefForm_coefRoot b a c hinj, smul_eq_mul] at h
  exact mul_left_cancel₀ h2 (by
    calc (2 : ZMod p) * Q (coefRoot b a c) = (2 * Q (b i₀)) * (∑ k, c k * c k) := h
      _ = 2 * ((∑ k, c k * c k) * Q (b i₀)) := by ring)

private lemma isIsom_reflection_of_flip_polarBilin_eq_smul {Q : QuadraticForm (ZMod p) U}
    {v : U} {f : Module.Dual (ZMod p) U} (hf : f v = 2)
    (hflip : (QuadraticMap.polarBilin Q).flip v = Q v • f) :
    IsIsom p Q (Module.reflection hf) := by
  intro w
  have hpv : polar Q w v = Q v * f w := by
    have h := congrArg (fun g : Module.Dual (ZMod p) U => g w) hflip
    rwa [LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply, LinearMap.smul_apply,
      smul_eq_mul] at h
  rw [Module.reflection_apply]
  have hstep : Q (w + (-(f w)) • v) = Q w := by
    rw [QuadraticMap.map_add Q w (-(f w) • v),
      QuadraticMap.map_smul Q (-(f w)) v,
      QuadraticMap.polar_smul_right Q (-(f w)) w v, hpv]
    simp only [smul_eq_mul]
    ring
  have hw : w - f w • v = w + (-(f w)) • v := by
    rw [sub_eq_add_neg, neg_smul]
  rw [hw]
  exact hstep

private lemma coefReflForm_coefRoot {m : ℕ} (b : Module.Basis (Fin n) (ZMod p) U)
    (a : Fin m → Fin n) (c : Fin m → ZMod p) (hinj : Function.Injective a)
    (hs : (∑ k, c k * c k) ≠ 0) :
    coefReflForm b a c (coefRoot b a c) = 2 := by
  rw [coefReflForm, LinearMap.smul_apply, coefForm_coefRoot b a c hinj, smul_eq_mul]
  calc (2 * (∑ k, c k * c k)⁻¹) * (∑ k, c k * c k)
      = 2 * ((∑ k, c k * c k)⁻¹ * (∑ k, c k * c k)) := by ring
    _ = 2 := by rw [inv_mul_cancel₀ hs, mul_one]

private lemma isIsom_reflection_coefRoot {m : ℕ} (hp : p ≠ 2)
    (b : Module.Basis (Fin n) (ZMod p) U) (a : Fin m → Fin n) (c : Fin m → ZMod p)
    (hinj : Function.Injective a) (hs : (∑ k, c k * c k) ≠ 0)
    {Q : QuadraticForm (ZMod p) U} (hP : ∀ σ, IsIsom p Q (permMap p b σ))
    (hS : ∀ i, IsIsom p Q (diagMap p b (fun j => if j = i then -1 else 1)))
    (i₀ : Fin n) :
    IsIsom p Q (Module.reflection (coefReflForm_coefRoot b a c hinj hs)) := by
  refine isIsom_reflection_of_flip_polarBilin_eq_smul
    (coefReflForm_coefRoot b a c hinj hs) ?_
  rw [flip_polarBilin_coefRoot hp b a c hP hS i₀, Q_coefRoot hp b a c hinj hP hS i₀,
    coefReflForm, smul_smul]
  congr 1
  calc 2 * Q (b i₀) = (2 * Q (b i₀)) *
        ((∑ k, c k * c k) * (∑ k, c k * c k)⁻¹) := by
        rw [mul_inv_cancel₀ hs, mul_one]
    _ = ((∑ k, c k * c k) * Q (b i₀)) * (2 * (∑ k, c k * c k)⁻¹) := by ring

private lemma coefReflection_apply_basis_ne {m : ℕ} (b : Module.Basis (Fin n) (ZMod p) U)
    (a : Fin m → Fin n) (c : Fin m → ZMod p) (hinj : Function.Injective a)
    (hs : (∑ k, c k * c k) ≠ 0) {i : Fin n} (hi : ∀ k, i ≠ a k) :
    Module.reflection (coefReflForm_coefRoot b a c hinj hs) (b i) = b i := by
  rw [Module.reflection_apply, coefReflForm, LinearMap.smul_apply,
    coefForm_apply_basis_ne b a c hi, smul_zero, zero_smul, sub_zero]

private lemma coefReflection_apply_sum {m : ℕ} (b : Module.Basis (Fin n) (ZMod p) U)
    (a : Fin m → Fin n) (c : Fin m → ZMod p) (hinj : Function.Injective a)
    (hsum : (∑ k, c k) = 0) (hs : (∑ k, c k * c k) ≠ 0) :
    Module.reflection (coefReflForm_coefRoot b a c hinj hs) (∑ i, b i) = ∑ i, b i := by
  rw [Module.reflection_apply, coefReflForm, LinearMap.smul_apply,
    coefForm_apply_sum_basis b a c, hsum]
  simp

private def orthC (p : ℕ) : Fin 4 → ZMod p := ![1, 1, -1, -1]

private lemma orthC_sq_sum : (∑ k, (orthC p) k * (orthC p) k) = (4 : ZMod p) := by
  rw [Fin.sum_univ_four]
  norm_num [orthC]

private lemma orthC_sum : (∑ k, (orthC p) k) = (0 : ZMod p) := by
  rw [Fin.sum_univ_four]
  norm_num [orthC]

private lemma orthC_sq_sum_ne_zero (hp : p ≠ 2) :
    ((∑ k, (orthC p) k * (orthC p) k) : ZMod p) ≠ 0 := by
  rw [orthC_sq_sum, show (4 : ZMod p) = 2 * 2 by norm_num]
  exact mul_ne_zero (wSlpmC_two_ne_zero hp) (wSlpmC_two_ne_zero hp)

private lemma not_monomial_reflection (hp : p ≠ 2) (b : Module.Basis (Fin n) (ZMod p) U)
    (a : Fin 4 → Fin n) (hinj : Function.Injective a) (hs : (∑ k, (orthC p) k * (orthC p) k) ≠ 0) :
    ¬ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      ∀ i, Module.reflection (coefReflForm_coefRoot b a (orthC p) hinj hs) (b i) =
        c i • b (σ i) := by
  rintro ⟨σ, c, hc⟩
  have h2 : (2 : ZMod p) ≠ 0 := wSlpmC_two_ne_zero hp
  have h2inv : (2 : ZMod p)⁻¹ ≠ 0 := inv_ne_zero h2
  have hf0 : coefReflForm b a (orthC p) (b (a 0)) = (2 : ZMod p)⁻¹ := by
    rw [coefReflForm_apply_basis b a (orthC p) hinj 0, orthC_sq_sum,
      show (orthC p) 0 = 1 from rfl]
    simpa using two_mul_inv_four hp
  have hc0 : b.coord (a 0) (coefRoot b a (orthC p)) = 1 := by
    rw [coord_coefRoot b a (orthC p) hinj 0]
    simp [orthC]
  have hc1 : b.coord (a 1) (coefRoot b a (orthC p)) = 1 := by
    rw [coord_coefRoot b a (orthC p) hinj 1]
    simp [orthC]
  have hcoord0 : b.coord (a 0)
      (Module.reflection (coefReflForm_coefRoot b a (orthC p) hinj hs) (b (a 0))) =
      (2 : ZMod p)⁻¹ := by
    rw [Module.reflection_apply, map_sub, map_smul, hf0, hc0]
    simp only [smul_eq_mul, mul_one]
    rw [show b.coord (a 0) (b (a 0)) = 1 from by simp]
    exact one_sub_inv_two hp
  have hcoord1 : b.coord (a 1)
      (Module.reflection (coefReflForm_coefRoot b a (orthC p) hinj hs) (b (a 0))) =
      -((2 : ZMod p)⁻¹) := by
    rw [Module.reflection_apply, map_sub, map_smul, hf0, hc1]
    simp only [smul_eq_mul, mul_one]
    rw [show b.coord (a 1) (b (a 0)) = 0 from by simp [hinj.eq_iff]]
    ring
  have hσ0 : σ (a 0) = a 0 := by
    have h := congrArg (b.coord (a 0)) (hc (a 0))
    rw [hcoord0, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self_apply] at h
    by_contra hne
    rw [if_neg hne, smul_zero] at h
    exact h2inv h
  have hσ1 : σ (a 0) = a 1 := by
    have h := congrArg (b.coord (a 1)) (hc (a 0))
    rw [hcoord1, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self_apply] at h
    by_contra hne
    rw [if_neg hne, smul_zero] at h
    exact (neg_ne_zero.mpr h2inv) h
  exact absurd (hinj (hσ0.symm.trans hσ1)) (by decide)

private lemma exists_smul_basis_of_signChange (hp : p ≠ 2)
    (b : Module.Basis (Fin n) (ZMod p) U) (k : Fin n)
    {Q : QuadraticForm (ZMod p) U}
    (hP : ∀ σ, IsIsom p Q (permMap p b σ)) (i₀ : Fin n) {c : ZMod p} {x : U}
    (hQx : Q x = c)
    (hsx : diagMap p b (fun j => if j = k then -1 else 1) x = -x) :
    ∃ μ : ZMod p, x = μ • b k ∧ μ * μ * Q (b i₀) = c := by
  have h2 : (2 : ZMod p) ≠ 0 := wSlpmC_two_ne_zero hp
  have hsx' : Module.reflection (two_smul_coord_apply_self b k) x = -x := by
    rw [← signChange_eq_reflection b k]
    exact hsx
  rw [Module.reflection_apply, LinearMap.smul_apply, smul_eq_mul] at hsx'
  set μ : ZMod p := b.coord k x
  have hx : x = μ • b k := by
    have hdouble : x + x = (2 * μ) • b k :=
      (congrArg (fun y => y + x) ((sub_eq_iff_eq_add).mp hsx')).trans (by abel)
    have hmain : (2 : ZMod p) • x = (2 : ZMod p) • (μ • b k) := by
      rw [show (2 : ZMod p) • x = x + x from two_smul (ZMod p) x, hdouble, smul_smul]
    have hcancel := congrArg (fun z => (2 : ZMod p)⁻¹ • z) hmain
    rw [smul_smul, smul_smul, inv_mul_cancel₀ h2] at hcancel
    simpa using hcancel
  refine ⟨μ, hx, ?_⟩
  have hQa0 : Q (b k) = Q (b i₀) := Q_basis_eq b hP i₀ k
  have h := hQx
  rw [hx, QuadraticMap.map_smul, hQa0, smul_eq_mul] at h
  exact h

private lemma reflection_mem_classRefl (hp : p ≠ 2) (b : Module.Basis (Fin n) (ZMod p) U)
    (a : Fin 4 → Fin n) (hinj : Function.Injective a) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0)
    (hP : ∀ σ, IsIsom p Q (permMap p b σ))
    (hS : ∀ i, IsIsom p Q (diagMap p b (fun j => if j = i then -1 else 1)))
    (i₀ : Fin n)
    (hs : (∑ k, (orthC p) k * (orthC p) k) ≠ 0)
    (hmem : diagMap p b (fun j => if j = a 0 then -1 else 1) ∈
      Subgroup.closure (ClassRefl p Q c)) :
    Module.reflection (coefReflForm_coefRoot b a (orthC p) hinj hs) ∈ ClassRefl p Q c := by
  have hsign : diagMap p b (fun j => if j = a 0 then -1 else 1) ∈ ClassRefl p Q c :=
    @mem_classRefl_of_isRefl_mem_closure p _ U _ _ hp (Module.Finite.of_basis b) Q hQ c hc
      (diagMap p b (fun j => if j = a 0 then -1 else 1)) hmem
      (isRefl_diagMap_sign hp b (a 0))
  obtain ⟨-, -, x, hQx, hsx⟩ := hsign
  obtain ⟨μ, hx, hQμ⟩ := exists_smul_basis_of_signChange hp b (a 0) hP i₀ hQx hsx
  have h2 : (2 : ZMod p) ≠ 0 := wSlpmC_two_ne_zero hp
  have h4 : (4 : ZMod p) ≠ 0 := by
    simpa [show (4 : ZMod p) = 2 * 2 by norm_num] using mul_ne_zero h2 h2
  have hQv : Q (coefRoot b a (orthC p)) = (4 : ZMod p) * Q (b i₀) := by
    rw [Q_coefRoot hp b a (orthC p) hinj hP hS i₀, orthC_sq_sum]
  have hForm : coefForm b a (orthC p) (coefRoot b a (orthC p)) = (4 : ZMod p) := by
    rw [coefForm_coefRoot b a (orthC p) hinj, orthC_sq_sum]
  have hQw : Q ((μ * (2 : ZMod p)⁻¹) • coefRoot b a (orthC p)) = c := by
    rw [QuadraticMap.map_smul, hQv, smul_eq_mul]
    have hinv : (2 : ZMod p)⁻¹ * 2⁻¹ * 4 = 1 := by
      calc (2 : ZMod p)⁻¹ * 2⁻¹ * 4 = (2⁻¹ * 2) * (2⁻¹ * 2) := by ring
        _ = 1 := by rw [inv_mul_cancel₀ h2, one_mul]
    calc (μ * 2⁻¹) * (μ * 2⁻¹) * (4 * Q (b i₀))
        = (μ * μ * Q (b i₀)) * ((2 : ZMod p)⁻¹ * 2⁻¹ * 4) := by ring
      _ = c := by rw [hinv, mul_one, hQμ]
  have hfw : coefReflForm b a (orthC p) ((μ * (2 : ZMod p)⁻¹) • coefRoot b a (orthC p)) = μ := by
    rw [coefReflForm, LinearMap.smul_apply, map_smul, hForm, orthC_sq_sum,
      smul_eq_mul]
    calc (2 * (4 : ZMod p)⁻¹) * ((μ * 2⁻¹) * 4)
        = μ * (2 * 2⁻¹) * (4 * 4⁻¹) := by ring
      _ = μ := by rw [mul_inv_cancel₀ h2, mul_inv_cancel₀ h4]; ring
  have hμe : (2 : ZMod p) * (μ * 2⁻¹) = μ := by
    field_simp [h2]
  have h2w : (2 : ZMod p) • ((μ * (2 : ZMod p)⁻¹) • coefRoot b a (orthC p)) =
      μ • coefRoot b a (orthC p) := by
    rw [smul_smul, hμe]
  have hrw : Module.reflection (coefReflForm_coefRoot b a (orthC p) hinj hs)
      ((μ * (2 : ZMod p)⁻¹) • coefRoot b a (orthC p)) =
      -((μ * (2 : ZMod p)⁻¹) • coefRoot b a (orthC p)) := by
    rw [Module.reflection_apply, hfw, ← h2w, two_smul]
    abel
  exact ⟨isRefl_reflection hp (coefReflForm_coefRoot b a (orthC p) hinj hs),
    isIsom_reflection_coefRoot hp b a (orthC p) hinj hs hP hS i₀,
    (μ * (2 : ZMod p)⁻¹) • coefRoot b a (orthC p), hQw, hrw⟩

theorem exists_isRefl_fix_not_monomial_of_orth (hp : p ≠ 2) (hn : 5 ≤ n)
    (b : Module.Basis (Fin n) (ZMod p) U) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hperm : ∀ σ, permMap p b σ ∈ A)
    (hsgn : ∀ i, diagMap p b (fun j => if j = i then -1 else 1) ∈ A)
    (Q : QuadraticForm (ZMod p) U) (hA : ∀ g, g ∈ A ↔ IsIsom p Q g) (i₀ : Fin n) :
    ∃ r ∈ A, IsRefl p r ∧ r (b i₀) = b i₀ ∧ r (∑ i, b i) = ∑ i, b i ∧
      ¬ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), ∀ i, r (b i) = c i • b (σ i) := by
  obtain ⟨a, hinj, hne⟩ := exists_coords_ne (m := 4) (by omega) i₀
  have hP : ∀ σ, IsIsom p Q (permMap p b σ) := fun σ => (hA _).1 (hperm σ)
  have hS : ∀ i, IsIsom p Q (diagMap p b (fun j => if j = i then -1 else 1)) :=
    fun i => (hA _).1 (hsgn i)
  have hs : (∑ k, (orthC p) k * (orthC p) k) ≠ 0 := orthC_sq_sum_ne_zero hp
  refine ⟨Module.reflection (coefReflForm_coefRoot b a (orthC p) hinj hs),
    (hA _).2 (isIsom_reflection_coefRoot hp b a (orthC p) hinj hs hP hS i₀),
    isRefl_reflection hp (coefReflForm_coefRoot b a (orthC p) hinj hs), ?_, ?_,
    not_monomial_reflection hp b a hinj hs⟩
  · exact coefReflection_apply_basis_ne b a (orthC p) hinj hs (fun k => (hne k).symm)
  · exact coefReflection_apply_sum b a (orthC p) hinj orthC_sum hs

theorem exists_isRefl_fix_not_monomial_of_orthClass (hp : p ≠ 2) (hn : 5 ≤ n)
    (b : Module.Basis (Fin n) (ZMod p) U) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hperm : ∀ σ, permMap p b σ ∈ A)
    (hsgn : ∀ i, diagMap p b (fun j => if j = i then -1 else 1) ∈ A)
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p}
    (hc : c ≠ 0) (hA : A = Subgroup.closure (ClassRefl p Q c)) (i₀ : Fin n) :
    ∃ r ∈ A, IsRefl p r ∧ r (b i₀) = b i₀ ∧ r (∑ i, b i) = ∑ i, b i ∧
      ¬ ∃ (σ : Equiv.Perm (Fin n)) (c' : Fin n → ZMod p), ∀ i, r (b i) = c' i • b (σ i) := by
  obtain ⟨a, hinj, hne⟩ := exists_coords_ne (m := 4) (by omega) i₀
  have hP : ∀ σ, IsIsom p Q (permMap p b σ) :=
    fun σ => isIsom_of_mem_closure_classRefl (hA ▸ hperm σ)
  have hS : ∀ i, IsIsom p Q (diagMap p b (fun j => if j = i then -1 else 1)) :=
    fun i => isIsom_of_mem_closure_classRefl (hA ▸ hsgn i)
  have hs : (∑ k, (orthC p) k * (orthC p) k) ≠ 0 := orthC_sq_sum_ne_zero hp
  have hmem : diagMap p b (fun j => if j = a 0 then -1 else 1) ∈
      Subgroup.closure (ClassRefl p Q c) := hA ▸ hsgn (a 0)
  have hrmem : Module.reflection (coefReflForm_coefRoot b a (orthC p) hinj hs) ∈ ClassRefl p Q c :=
    reflection_mem_classRefl hp b a hinj hQ hc hP hS i₀ hs hmem
  refine ⟨Module.reflection (coefReflForm_coefRoot b a (orthC p) hinj hs), ?_,
    isRefl_reflection hp (coefReflForm_coefRoot b a (orthC p) hinj hs), ?_, ?_,
    not_monomial_reflection hp b a hinj hs⟩
  · rw [hA]
    exact Subgroup.subset_closure hrmem
  · exact coefReflection_apply_basis_ne b a (orthC p) hinj hs (fun k => (hne k).symm)
  · exact coefReflection_apply_sum b a (orthC p) hinj orthC_sum hs

private lemma three_ne_zero_of_ne_three (hp3 : p ≠ 3) : (3 : ZMod p) ≠ 0 := by
  intro h
  exact hp3 ((Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num)).mp
    ((ZMod.natCast_eq_zero_iff 3 p).mp h))

private lemma nine_ne_zero_of_ne_three (hp3 : p ≠ 3) : (9 : ZMod p) ≠ 0 := by
  have h3 := three_ne_zero_of_ne_three hp3
  rw [show (9 : ZMod p) = 3 * 3 by norm_num]
  exact mul_ne_zero h3 h3

private def threeC (p : ℕ) : Fin 3 → ZMod p := ![1, 2, 2]

private lemma threeC_sq_sum : (∑ k, (threeC p) k * (threeC p) k) = (9 : ZMod p) := by
  rw [Fin.sum_univ_three]
  norm_num [threeC]

private lemma threeC_sq_sum_ne_zero (hp3 : p ≠ 3) :
    ((∑ k, (threeC p) k * (threeC p) k) : ZMod p) ≠ 0 := by
  rw [threeC_sq_sum]
  exact nine_ne_zero_of_ne_three hp3

private lemma not_monomial_reflection_three (hp : p ≠ 2) (hp3 : p ≠ 3)
    (b : Module.Basis (Fin n) (ZMod p) U) (a : Fin 3 → Fin n)
    (hinj : Function.Injective a) (hs : (∑ k, (threeC p) k * (threeC p) k) ≠ 0) :
    ¬ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      ∀ i, Module.reflection (coefReflForm_coefRoot b a (threeC p) hinj hs) (b i) =
        c i • b (σ i) := by
  rintro ⟨σ, c, hc⟩
  have h9 : (9 : ZMod p) ≠ 0 := nine_ne_zero_of_ne_three hp3
  have h2 : (2 : ZMod p) ≠ 0 := wSlpmC_two_ne_zero hp
  have h4 : (4 : ZMod p) ≠ 0 := by
    simpa [show (4 : ZMod p) = 2 * 2 by norm_num] using mul_ne_zero h2 h2
  have h49 : (4 * (9 : ZMod p)⁻¹) ≠ 0 := mul_ne_zero h4 (inv_ne_zero h9)
  have hf0 : coefReflForm b a (threeC p) (b (a 0)) = 2 * (9 : ZMod p)⁻¹ := by
    rw [coefReflForm_apply_basis b a (threeC p) hinj 0, threeC_sq_sum]
    simp [threeC]
  have hc1 : b.coord (a 1) (coefRoot b a (threeC p)) = 2 := by
    rw [coord_coefRoot b a (threeC p) hinj 1]
    simp [threeC]
  have hc2 : b.coord (a 2) (coefRoot b a (threeC p)) = 2 := by
    rw [coord_coefRoot b a (threeC p) hinj 2]
    simp [threeC]
  have hcoord1 : b.coord (a 1)
      (Module.reflection (coefReflForm_coefRoot b a (threeC p) hinj hs) (b (a 0))) =
      -(4 * 9⁻¹) := by
    rw [Module.reflection_apply, map_sub, map_smul, hf0, hc1,
      show b.coord (a 1) (b (a 0)) = 0 from by simp [hinj.eq_iff]]
    ring
  have hcoord2 : b.coord (a 2)
      (Module.reflection (coefReflForm_coefRoot b a (threeC p) hinj hs) (b (a 0))) =
      -(4 * 9⁻¹) := by
    rw [Module.reflection_apply, map_sub, map_smul, hf0, hc2,
      show b.coord (a 2) (b (a 0)) = 0 from by simp [hinj.eq_iff]]
    ring
  have hσ1 : σ (a 0) = a 1 := by
    have h := congrArg (b.coord (a 1)) (hc (a 0))
    rw [hcoord1, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self_apply] at h
    by_contra hne
    rw [if_neg hne, smul_zero] at h
    exact (neg_ne_zero.mpr h49) h
  have hσ2 : σ (a 0) = a 2 := by
    have h := congrArg (b.coord (a 2)) (hc (a 0))
    rw [hcoord2, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self_apply] at h
    by_contra hne
    rw [if_neg hne, smul_zero] at h
    exact (neg_ne_zero.mpr h49) h
  exact absurd (hinj (hσ1.symm.trans hσ2)) (by decide)

theorem exists_isRefl_fix_not_monomial_of_orth_of_ne_three (hp : p ≠ 2) (hp3 : p ≠ 3)
    (hn : 4 ≤ n) (b : Module.Basis (Fin n) (ZMod p) U) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hperm : ∀ σ, permMap p b σ ∈ A)
    (hsgn : ∀ i, diagMap p b (fun j => if j = i then -1 else 1) ∈ A)
    (Q : QuadraticForm (ZMod p) U) (hA : ∀ g, g ∈ A ↔ IsIsom p Q g) (i₀ : Fin n) :
    ∃ r ∈ A, IsRefl p r ∧ r (b i₀) = b i₀ ∧
      ¬ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), ∀ i, r (b i) = c i • b (σ i) := by
  obtain ⟨a, hinj, hne⟩ := exists_coords_ne (m := 3) (by omega) i₀
  have hP : ∀ σ, IsIsom p Q (permMap p b σ) := fun σ => (hA _).1 (hperm σ)
  have hS : ∀ i, IsIsom p Q (diagMap p b (fun j => if j = i then -1 else 1)) :=
    fun i => (hA _).1 (hsgn i)
  have hs : (∑ k, (threeC p) k * (threeC p) k) ≠ 0 := threeC_sq_sum_ne_zero hp3
  refine ⟨Module.reflection (coefReflForm_coefRoot b a (threeC p) hinj hs),
    (hA _).2 (isIsom_reflection_coefRoot hp b a (threeC p) hinj hs hP hS i₀),
    isRefl_reflection hp (coefReflForm_coefRoot b a (threeC p) hinj hs), ?_,
    not_monomial_reflection_three hp hp3 b a hinj hs⟩
  exact coefReflection_apply_basis_ne b a (threeC p) hinj hs (fun k => (hne k).symm)

theorem exists_isRefl_fix_not_monomial_of_orthClass_of_ne_three (hp : p ≠ 2) (hp3 : p ≠ 3)
    (hn : 4 ≤ n) (b : Module.Basis (Fin n) (ZMod p) U) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hperm : ∀ σ, permMap p b σ ∈ A)
    (hsgn : ∀ i, diagMap p b (fun j => if j = i then -1 else 1) ∈ A)
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p}
    (hc : c ≠ 0) (hA : A = Subgroup.closure (ClassRefl p Q c)) (i₀ : Fin n) :
    ∃ r ∈ A, IsRefl p r ∧ r (b i₀) = b i₀ ∧
      ¬ ∃ (σ : Equiv.Perm (Fin n)) (c' : Fin n → ZMod p), ∀ i, r (b i) = c' i • b (σ i) := by
  obtain ⟨a, hinj, hne⟩ := exists_coords_ne (m := 3) (by omega) i₀
  have hP : ∀ σ, IsIsom p Q (permMap p b σ) :=
    fun σ => isIsom_of_mem_closure_classRefl (hA ▸ hperm σ)
  have hS : ∀ i, IsIsom p Q (diagMap p b (fun j => if j = i then -1 else 1)) :=
    fun i => isIsom_of_mem_closure_classRefl (hA ▸ hsgn i)
  have hs : (∑ k, (threeC p) k * (threeC p) k) ≠ 0 := threeC_sq_sum_ne_zero hp3
  have hsign : diagMap p b (fun j => if j = a 0 then -1 else 1) ∈ ClassRefl p Q c :=
    @mem_classRefl_of_isRefl_mem_closure p _ U _ _ hp (Module.Finite.of_basis b) Q hQ c hc
      (diagMap p b (fun j => if j = a 0 then -1 else 1)) (hA ▸ hsgn (a 0))
      (isRefl_diagMap_sign hp b (a 0))
  obtain ⟨-, -, x, hQx, hsx⟩ := hsign
  obtain ⟨μ, -, hQμ⟩ := exists_smul_basis_of_signChange hp b (a 0) hP i₀ hQx hsx
  have h3 : (3 : ZMod p) ≠ 0 := three_ne_zero_of_ne_three hp3
  have hQv : Q (coefRoot b a (threeC p)) = (9 : ZMod p) * Q (b i₀) := by
    rw [Q_coefRoot hp b a (threeC p) hinj hP hS i₀, threeC_sq_sum]
  have hQw : Q ((μ * (3 : ZMod p)⁻¹) • coefRoot b a (threeC p)) = c := by
    rw [QuadraticMap.map_smul, hQv, smul_eq_mul]
    have hinv : (3 : ZMod p)⁻¹ * 3⁻¹ * 9 = 1 := by
      calc (3 : ZMod p)⁻¹ * 3⁻¹ * 9 = (3⁻¹ * 3) * (3⁻¹ * 3) := by ring
        _ = 1 := by rw [inv_mul_cancel₀ h3, one_mul]
    calc (μ * 3⁻¹) * (μ * 3⁻¹) * (9 * Q (b i₀))
        = (μ * μ * Q (b i₀)) * ((3 : ZMod p)⁻¹ * 3⁻¹ * 9) := by ring
      _ = c := by rw [hinv, mul_one, hQμ]
  have hrv : Module.reflection (coefReflForm_coefRoot b a (threeC p) hinj hs)
      (coefRoot b a (threeC p)) = -coefRoot b a (threeC p) := by
    rw [Module.reflection_apply, coefReflForm_coefRoot b a (threeC p) hinj hs, two_smul]
    abel
  have hrw : Module.reflection (coefReflForm_coefRoot b a (threeC p) hinj hs)
      ((μ * (3 : ZMod p)⁻¹) • coefRoot b a (threeC p)) =
      -((μ * (3 : ZMod p)⁻¹) • coefRoot b a (threeC p)) := by
    rw [map_smul, hrv, smul_neg]
  have hrmem : Module.reflection (coefReflForm_coefRoot b a (threeC p) hinj hs) ∈ ClassRefl p Q c :=
    ⟨isRefl_reflection hp (coefReflForm_coefRoot b a (threeC p) hinj hs),
      isIsom_reflection_coefRoot hp b a (threeC p) hinj hs hP hS i₀,
      (μ * (3 : ZMod p)⁻¹) • coefRoot b a (threeC p), hQw, hrw⟩
  refine ⟨Module.reflection (coefReflForm_coefRoot b a (threeC p) hinj hs), ?_,
    isRefl_reflection hp (coefReflForm_coefRoot b a (threeC p) hinj hs), ?_,
    not_monomial_reflection_three hp hp3 b a hinj hs⟩
  · rw [hA]
    exact Subgroup.subset_closure hrmem
  · exact coefReflection_apply_basis_ne b a (threeC p) hinj hs (fun k => (hne k).symm)

private lemma coord_permMap (b : Module.Basis (Fin n) (ZMod p) U) (σ : Equiv.Perm (Fin n))
    (y : U) (k : Fin n) :
    b.coord k (permMap p b σ y) = b.coord (σ.symm k) y := by
  rw [← b.sum_repr y]
  simp only [map_sum, map_smul, permMap_apply_basis, Module.Basis.coord_apply,
    Module.Basis.repr_self_apply]
  rw [Finset.sum_eq_single (σ.symm k)]
  · simp
  · intro l _ hl
    have hlk : σ l ≠ k :=
      fun h => hl (σ.injective (h.trans (Equiv.apply_symm_apply σ k).symm))
    simp [hlk]
  · intro hk
    exact absurd (Finset.mem_univ (σ.symm k)) hk

private lemma exists_smul_sub_of_permMap_swap_eq_neg (hp : p ≠ 2)
    (b : Module.Basis (Fin n) (ZMod p) U) {i j : Fin n} (hij : i ≠ j) {y : U}
    (hy : permMap p b (Equiv.swap i j) y = -y) :
    ∃ ν : ZMod p, y = ν • (b i - b j) := by
  have hcoord (k : Fin n) : b.coord (Equiv.swap i j k) y = -b.coord k y := by
    have h := congrArg (b.coord k) hy
    rw [map_neg, coord_permMap b (Equiv.swap i j) y k, Equiv.symm_swap] at h
    exact h
  have hji : b.coord j y = -b.coord i y := by
    have h := hcoord j
    rw [Equiv.swap_apply_right] at h
    rw [h, neg_neg]
  have hzero (k : Fin n) (hki : k ≠ i) (hkj : k ≠ j) : b.coord k y = 0 := by
    have h := hcoord k
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj] at h
    have hneg : b.coord k y = -b.coord k y := h
    have h2 : (2 : ZMod p) * b.coord k y = 0 := by
      calc (2 : ZMod p) * b.coord k y = b.coord k y + b.coord k y := two_mul _
        _ = -b.coord k y + b.coord k y := by
          nth_rewrite 1 [hneg]
          rfl
        _ = 0 := neg_add_cancel _
    exact (mul_eq_zero.mp h2).resolve_left (wSlpmC_two_ne_zero hp)
  have hy' : y = b.coord i y • b i + b.coord j y • b j := by
    conv_lhs => rw [← b.sum_repr y]
    rw [Finset.sum_eq_add_of_mem (s := Finset.univ) i j (Finset.mem_univ _)
      (Finset.mem_univ _) hij (fun k _ hk => by
        change b.coord k y • b k = 0
        rw [hzero k hk.1 hk.2, zero_smul])]
    simp only [Module.Basis.coord_apply]
  refine ⟨b.coord i y, ?_⟩
  conv_lhs => rw [hy']
  rw [hji, smul_sub, neg_smul, sub_eq_add_neg]

private lemma Q_smul_sub_basis (hp : p ≠ 2) (b : Module.Basis (Fin n) (ZMod p) U)
    {Q : QuadraticForm (ZMod p) U} (hP : ∀ σ, IsIsom p Q (permMap p b σ))
    (hS : ∀ i, IsIsom p Q (diagMap p b (fun j => if j = i then -1 else 1)))
    {i j : Fin n} (hij : i ≠ j) (ν : ZMod p) :
    Q (ν • (b i - b j)) = 2 * (ν * ν * Q (b i)) := by
  have hQsub : Q (b i - b j) = 2 * Q (b i) := by
    rw [sub_eq_add_neg, QuadraticMap.map_add Q (b i) (-b j), QuadraticMap.map_neg Q (b j),
      QuadraticMap.polar_neg_right, polar_basis_eq_zero hp b hS hij,
      Q_basis_eq b hP i j]
    ring
  rw [QuadraticMap.map_smul, hQsub]
  simp only [smul_eq_mul]
  ring

private lemma zmod_three_sq_ne_two : ∀ x : ZMod 3, x * x ≠ 2 := by
  intro x h
  have hval := congrArg ZMod.val h
  rw [ZMod.val_mul, ZMod.val_two_eq_two_mod] at hval
  have hx3 : x.val < 3 := ZMod.val_lt x
  interval_cases x.val <;> norm_num at hval

theorem false_of_orthClass_of_signed_three (hp3 : p = 3) (hn : 2 ≤ n)
    (b : Module.Basis (Fin n) (ZMod p) U) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hperm : ∀ σ, permMap p b σ ∈ A)
    (hsgn : ∀ i, diagMap p b (fun j => if j = i then -1 else 1) ∈ A)
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p}
    (hc : c ≠ 0) (hA : A = Subgroup.closure (ClassRefl p Q c)) : False := by
  subst p
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  have hP : ∀ σ, IsIsom 3 Q (permMap 3 b σ) :=
    fun σ => isIsom_of_mem_closure_classRefl (hA ▸ hperm σ)
  have hS : ∀ k, IsIsom 3 Q (diagMap 3 b (fun l => if l = k then -1 else 1)) :=
    fun k => isIsom_of_mem_closure_classRefl (hA ▸ hsgn k)
  have hsign_i : diagMap 3 b (fun l => if l = i then -1 else 1) ∈ ClassRefl 3 Q c :=
    @mem_classRefl_of_isRefl_mem_closure 3 _ U _ _ hp2 (Module.Finite.of_basis b) Q hQ c hc
      (diagMap 3 b (fun l => if l = i then -1 else 1)) (hA ▸ hsgn i)
      (isRefl_diagMap_sign hp2 b i)
  obtain ⟨-, -, x, hQx, hsx⟩ := hsign_i
  obtain ⟨μ, hx, hQμ⟩ := exists_smul_basis_of_signChange hp2 b i hP i hQx hsx
  have hQi0 : Q (b i) ≠ 0 := by
    intro h
    exact hc (by simpa [h] using hQμ.symm)
  have hswap : permMap 3 b (Equiv.swap i j) ∈ ClassRefl 3 Q c :=
    @mem_classRefl_of_isRefl_mem_closure 3 _ U _ _ hp2 (Module.Finite.of_basis b) Q hQ c hc
      (permMap 3 b (Equiv.swap i j)) (hA ▸ hperm (Equiv.swap i j))
      (isRefl_permMap_swap b hij)
  obtain ⟨-, -, y, hQy, hsy⟩ := hswap
  obtain ⟨ν, hyν⟩ := exists_smul_sub_of_permMap_swap_eq_neg hp2 b hij hsy
  have hQyν : Q y = 2 * (ν * ν * Q (b i)) := by
    rw [hyν, Q_smul_sub_basis hp2 b hP hS hij]
  have hν0 : ν ≠ 0 := by
    intro h
    have hzero : Q y = 0 := by rw [hQyν, h]; ring
    rw [hQy] at hzero
    exact hc hzero
  have h_eq : μ * μ * Q (b i) = 2 * (ν * ν * Q (b i)) :=
    hQμ.trans (hQy.symm.trans hQyν)
  have h_eq2 : μ * μ = 2 * (ν * ν) := by
    refine mul_right_cancel₀ hQi0 ?_
    calc μ * μ * Q (b i) = 2 * (ν * ν * Q (b i)) := h_eq
      _ = (2 * (ν * ν)) * Q (b i) := by ring
  have hsq : (μ * ν⁻¹) * (μ * ν⁻¹) = 2 := by
    calc (μ * ν⁻¹) * (μ * ν⁻¹) = (μ * μ) * (ν⁻¹ * ν⁻¹) := by ring
      _ = (2 * (ν * ν)) * (ν⁻¹ * ν⁻¹) := by rw [h_eq2]
      _ = 2 * (ν * ν * (ν⁻¹ * ν⁻¹)) := by ring
      _ = 2 := by
        field_simp [hν0]
  exact zmod_three_sq_ne_two (μ * ν⁻¹) hsq

private lemma Q_add_smul_basis (b : Module.Basis (Fin n) (ZMod p) U)
    {Q : QuadraticForm (ZMod p) U} {x : U} {c : ZMod p} {k : Fin n}
    (hx : polar Q x (b k) = 0) :
    Q (x + c • b k) = Q x + c * c * Q (b k) := by
  rw [QuadraticMap.map_add Q x (c • b k), QuadraticMap.map_smul,
    QuadraticMap.polar_smul_right, hx, smul_zero, add_zero]
  simp only [smul_eq_mul]

private lemma Q_sum_four_basis (hp : p ≠ 2) (b : Module.Basis (Fin 4) (ZMod p) U)
    {Q : QuadraticForm (ZMod p) U} (hP : ∀ σ, IsIsom p Q (permMap p b σ))
    (hS : ∀ i, IsIsom p Q (diagMap p b (fun j => if j = i then -1 else 1)))
    (i₀ : Fin 4) (c : Fin 4 → ZMod p) :
    Q (∑ k, c k • b k) = (∑ k, c k * c k) * Q (b i₀) := by
  rw [Fin.sum_univ_four, Fin.sum_univ_four]
  have h0 : Q (c 0 • b 0) = c 0 * c 0 * Q (b 0) := by
    rw [QuadraticMap.map_smul]
    simp only [smul_eq_mul]
  have h1p : polar Q (c 0 • b 0) (b 1) = 0 := by
    rw [QuadraticMap.polar_smul_left, polar_basis_eq_zero hp b hS (by decide), smul_zero]
  have h1 : Q (c 0 • b 0 + c 1 • b 1) =
      c 0 * c 0 * Q (b 0) + c 1 * c 1 * Q (b 1) := by
    rw [Q_add_smul_basis b h1p, h0]
  have h2p : polar Q (c 0 • b 0 + c 1 • b 1) (b 2) = 0 := by
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_smul_left, polar_basis_eq_zero hp b hS (by decide),
      polar_basis_eq_zero hp b hS (by decide)]
    simp
  have h2 : Q (c 0 • b 0 + c 1 • b 1 + c 2 • b 2) =
      c 0 * c 0 * Q (b 0) + c 1 * c 1 * Q (b 1) + c 2 * c 2 * Q (b 2) := by
    rw [Q_add_smul_basis b h2p, h1]
  have h3p : polar Q (c 0 • b 0 + c 1 • b 1 + c 2 • b 2) (b 3) = 0 := by
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_add_left,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_smul_left, polar_basis_eq_zero hp b hS (by decide),
      polar_basis_eq_zero hp b hS (by decide),
      polar_basis_eq_zero hp b hS (by decide)]
    simp
  rw [Q_add_smul_basis b h3p, h2,
    Q_basis_eq b hP i₀ 0, Q_basis_eq b hP i₀ 1, Q_basis_eq b hP i₀ 2,
    Q_basis_eq b hP i₀ 3]
  ring

private noncomputable def sigW1 (b : Module.Basis (Fin 4) (ZMod p) U) : U :=
  b 0 + b 1 + b 2

private noncomputable def sigW2 (b : Module.Basis (Fin 4) (ZMod p) U) : U :=
  b 1 - b 2 + b 3

private def sigC1 : Fin 4 → ZMod 3 := ![1, 1, 1, 0]

private def sigC2 : Fin 4 → ZMod 3 := ![0, 1, -1, 1]

private def sigC12 : Fin 4 → ZMod 3 := ![1, 2, 0, 1]

private lemma sigC1_sq_sum : (∑ k, sigC1 k * sigC1 k) = 0 := by
  rw [Fin.sum_univ_four]
  simp [sigC1]
  change (3 : ZMod 3) = 0
  exact (ZMod.natCast_eq_zero_iff 3 3).mpr (by norm_num)

private lemma sigC2_sq_sum : (∑ k, sigC2 k * sigC2 k) = 0 := by
  rw [Fin.sum_univ_four]
  simp [sigC2]
  change (3 : ZMod 3) = 0
  exact (ZMod.natCast_eq_zero_iff 3 3).mpr (by norm_num)

private lemma sigC12_sq_sum : (∑ k, sigC12 k * sigC12 k) = 0 := by
  rw [Fin.sum_univ_four]
  simp [sigC12]
  change (6 : ZMod 3) = 0
  exact (ZMod.natCast_eq_zero_iff 6 3).mpr (by norm_num)

private lemma sigW1_eq_sum [Module (ZMod 3) U] (b : Module.Basis (Fin 4) (ZMod 3) U) :
    sigW1 (p := 3) b = ∑ k, sigC1 k • b k := by
  rw [Fin.sum_univ_four]
  simp [sigW1, sigC1]

private lemma sigW2_eq_sum [Module (ZMod 3) U] (b : Module.Basis (Fin 4) (ZMod 3) U) :
    sigW2 (p := 3) b = ∑ k, sigC2 k • b k := by
  rw [Fin.sum_univ_four]
  simp [sigW2, sigC2, sub_eq_add_neg]

private lemma sigW1_add_sigW2_eq_sum [Module (ZMod 3) U]
    (b : Module.Basis (Fin 4) (ZMod 3) U) :
    sigW1 (p := 3) b + sigW2 (p := 3) b = ∑ k, sigC12 k • b k := by
  rw [Fin.sum_univ_four]
  simp [sigW1, sigW2, sigC12]
  module

private lemma singular_plane_Q_zero (hp3 : p = 3) (b : Module.Basis (Fin 4) (ZMod p) U)
    {Q : QuadraticForm (ZMod p) U} (hP : ∀ σ, IsIsom p Q (permMap p b σ))
    (hS : ∀ i, IsIsom p Q (diagMap p b (fun j => if j = i then -1 else 1))) :
    Q (sigW1 b) = 0 ∧ Q (sigW2 b) = 0 ∧ Q (sigW1 b + sigW2 b) = 0 := by
  subst p
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hQ1 : Q (sigW1 b) = 0 := by
    rw [sigW1_eq_sum b, Q_sum_four_basis hp2 b hP hS 0 sigC1, sigC1_sq_sum,
      zero_mul]
  have hQ2 : Q (sigW2 b) = 0 := by
    rw [sigW2_eq_sum b, Q_sum_four_basis hp2 b hP hS 3 sigC2, sigC2_sq_sum,
      zero_mul]
  have hQ12 : Q (sigW1 b + sigW2 b) = 0 := by
    rw [sigW1_add_sigW2_eq_sum b, Q_sum_four_basis hp2 b hP hS 0 sigC12,
      sigC12_sq_sum, zero_mul]
  exact ⟨hQ1, hQ2, hQ12⟩

private lemma singular_plane_finrank (hp3 : p = 3) (b : Module.Basis (Fin 4) (ZMod p) U) :
    Module.finrank (ZMod p) (Submodule.span (ZMod p) ({sigW1 b, sigW2 b} : Set U)) = 2 := by
  subst p
  have hli : LinearIndependent (ZMod 3) ![sigW1 b, sigW2 b] := by
    rw [LinearIndependent.pair_iff]
    intro α β hαβ
    have h0 : α = 0 := by
      have h := congrArg (b.coord 0) hαβ
      simpa [sigW1, sigW2, map_add, map_smul, smul_eq_mul] using h
    have h3 : β = 0 := by
      have h := congrArg (b.coord 3) hαβ
      simpa [sigW1, sigW2, map_add, map_smul, smul_eq_mul] using h
    exact ⟨h0, h3⟩
  have hspan : Submodule.span (ZMod 3) (Set.range ![sigW1 b, sigW2 b]) =
      Submodule.span (ZMod 3) ({sigW1 b, sigW2 b} : Set U) := by
    congr 1
    ext x
    simp [Set.range, eq_comm]
  rw [← hspan, finrank_span_eq_card hli]
  simp

theorem exists_singular_plane_of_signed_three (hp3 : p = 3) (b : Module.Basis (Fin 4) (ZMod p) U)
    {Q : QuadraticForm (ZMod p) U} (hP : ∀ σ, IsIsom p Q (permMap p b σ))
    (hS : ∀ i, IsIsom p Q (diagMap p b (fun j => if j = i then -1 else 1))) :
    ∃ W : Submodule (ZMod p) U, Module.finrank (ZMod p) W = 2 ∧ ∀ w ∈ W, Q w = 0 := by
  refine ⟨Submodule.span (ZMod p) ({sigW1 b, sigW2 b} : Set U),
    singular_plane_finrank hp3 b, ?_⟩
  intro w hw
  rw [Submodule.mem_span_pair] at hw
  obtain ⟨α, β, rfl⟩ := hw
  obtain ⟨h1, h2, h12'⟩ := singular_plane_Q_zero hp3 b hP hS
  have h12 : polar Q (sigW1 b) (sigW2 b) = 0 := by
    have h := QuadraticMap.map_add Q (sigW1 b) (sigW2 b)
    rw [h12', h1, h2] at h
    simpa using h.symm
  rw [QuadraticMap.map_add Q (α • sigW1 b) (β • sigW2 b), QuadraticMap.map_smul,
    QuadraticMap.map_smul, QuadraticMap.polar_smul_left,
    QuadraticMap.polar_smul_right, h1, h2, h12]
  simp

private def sumC (p : ℕ) : Fin 4 → ZMod p := ![5, -1, -1, -3]

private lemma sumC_sq_sum : (∑ k, (sumC p) k * (sumC p) k) = (36 : ZMod p) := by
  rw [Fin.sum_univ_four]
  norm_num [sumC]

private lemma sumC_sum : (∑ k, (sumC p) k) = (0 : ZMod p) := by
  rw [Fin.sum_univ_four]
  norm_num [sumC]

private lemma six_ne_zero_of_ne_two_of_ne_three (hp : p ≠ 2) (hp3 : p ≠ 3) :
    (6 : ZMod p) ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := wSlpmC_two_ne_zero hp
  have h3 : (3 : ZMod p) ≠ 0 := three_ne_zero_of_ne_three hp3
  rw [show (6 : ZMod p) = 2 * 3 by norm_num]
  exact mul_ne_zero h2 h3

private lemma sumC_sq_sum_ne_zero (hp : p ≠ 2) (hp3 : p ≠ 3) :
    ((∑ k, (sumC p) k * (sumC p) k) : ZMod p) ≠ 0 := by
  rw [sumC_sq_sum, show (36 : ZMod p) = 6 * 6 by norm_num]
  exact mul_ne_zero (six_ne_zero_of_ne_two_of_ne_three hp hp3)
    (six_ne_zero_of_ne_two_of_ne_three hp hp3)

private lemma coord_reflection_sumC (hp : p ≠ 2) (hp3 : p ≠ 3)
    (b : Module.Basis (Fin 4) (ZMod p) U)
    (hs : (∑ k, (sumC p) k * (sumC p) k) ≠ 0) (j : Fin 4) :
    b.coord j
        (Module.reflection (coefReflForm_coefRoot b id (sumC p) Function.injective_id hs)
          (b 3)) =
      (if (3 : Fin 4) = j then 1 else 0) + (6 : ZMod p)⁻¹ * (sumC p) j := by
  have h6 : (6 : ZMod p) ≠ 0 := six_ne_zero_of_ne_two_of_ne_three hp hp3
  have hf : coefReflForm b id (sumC p) (b 3) = -(6 : ZMod p)⁻¹ := by
    have h := coefReflForm_apply_basis b id (sumC p) Function.injective_id 3
    change coefReflForm b id (sumC p) (b 3) =
      (2 * (∑ k, (sumC p) k * (sumC p) k)⁻¹) * (sumC p) 3 at h
    rw [h, sumC_sq_sum, show (sumC p) 3 = -3 from rfl,
      show (36 : ZMod p) = 6 * 6 by norm_num, mul_inv]
    calc (2 : ZMod p) * (6⁻¹ * 6⁻¹) * -3
        = -((6 * 6⁻¹) * 6⁻¹) := by ring
      _ = -(6 : ZMod p)⁻¹ := by rw [mul_inv_cancel₀ h6, one_mul]
  have hw : b.coord j (coefRoot b id (sumC p)) = (sumC p) j := by
    simpa using coord_coefRoot b id (sumC p) Function.injective_id j
  have hb3 : b.coord j (b 3) = (if (3 : Fin 4) = j then 1 else 0) := by
    rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply]
  rw [Module.reflection_apply, map_sub, map_smul, smul_eq_mul, hb3, hf, hw]
  ring

private lemma coord_smul_basis_add_sum (b : Module.Basis (Fin 4) (ZMod p) U)
    (k j : Fin 4) (c s : ZMod p) :
    b.coord j (c • b k + s • ∑ i, b i) = c * (if k = j then 1 else 0) + s := by
  rw [map_add, map_smul, map_smul, coord_sum_basis, Module.Basis.coord_apply,
    Module.Basis.repr_self_apply]
  simp [smul_eq_mul]

private lemma reflection_sumC_ne (hp : p ≠ 2) (hp3 : p ≠ 3) (b : Module.Basis (Fin 4) (ZMod p) U)
    (hs : (∑ k, (sumC p) k * (sumC p) k) ≠ 0) (k : Fin 4) (c s : ZMod p) :
    Module.reflection (coefReflForm_coefRoot b id (sumC p) Function.injective_id hs) (b 3) ≠
      c • b k + s • ∑ i, b i := by
  intro h
  have h6 : (6 : ZMod p) ≠ 0 := six_ne_zero_of_ne_two_of_ne_three hp hp3
  have hR (j : Fin 4) := coord_reflection_sumC hp hp3 b hs j
  have hL (j : Fin 4) := coord_smul_basis_add_sum b k j c s
  fin_cases k
  · have h1 := congrArg (b.coord 3) h
    have h2 := congrArg (b.coord 1) h
    rw [hR 3, hL 3] at h1
    rw [hR 1, hL 1] at h2
    simp [sumC] at h1 h2
    have hAB := h1.trans h2.symm
    field_simp [h6] at hAB
    have h4 : (4 : ZMod p) = 0 := by linear_combination hAB
    have h2ne : (2 : ZMod p) ≠ 0 := wSlpmC_two_ne_zero hp
    have h4ne : (4 : ZMod p) ≠ 0 := by
      rw [show (4 : ZMod p) = 2 * 2 by norm_num]
      exact mul_ne_zero h2ne h2ne
    exact h4ne h4
  · have h1 := congrArg (b.coord 0) h
    have h2 := congrArg (b.coord 2) h
    rw [hR 0, hL 0] at h1
    rw [hR 2, hL 2] at h2
    simp [sumC] at h1 h2
    have hAB := h1.trans h2.symm
    field_simp [h6] at hAB
    exact h6 (by linear_combination hAB)
  · have h1 := congrArg (b.coord 0) h
    have h2 := congrArg (b.coord 1) h
    rw [hR 0, hL 0] at h1
    rw [hR 1, hL 1] at h2
    simp [sumC] at h1 h2
    have hAB := h1.trans h2.symm
    field_simp [h6] at hAB
    exact h6 (by linear_combination hAB)
  · have h1 := congrArg (b.coord 0) h
    have h2 := congrArg (b.coord 1) h
    rw [hR 0, hL 0] at h1
    rw [hR 1, hL 1] at h2
    simp [sumC] at h1 h2
    have hAB := h1.trans h2.symm
    field_simp [h6] at hAB
    exact h6 (by linear_combination hAB)

theorem exists_isRefl_fix_sum_of_orth_four (hp : p ≠ 2) (hp3 : p ≠ 3)
    (b : Module.Basis (Fin 4) (ZMod p) U) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hperm : ∀ σ, permMap p b σ ∈ A)
    (hsgn : ∀ i, diagMap p b (fun j => if j = i then -1 else 1) ∈ A)
    (Q : QuadraticForm (ZMod p) U) (hA : ∀ g, g ∈ A ↔ IsIsom p Q g) :
    ∃ r ∈ A, IsRefl p r ∧ r (∑ i, b i) = ∑ i, b i ∧
      ∀ (k : Fin 4) (c s : ZMod p), r (b 3) ≠ c • b k + s • ∑ i, b i := by
  have hP : ∀ σ, IsIsom p Q (permMap p b σ) := fun σ => (hA _).1 (hperm σ)
  have hS : ∀ i, IsIsom p Q (diagMap p b (fun j => if j = i then -1 else 1)) :=
    fun i => (hA _).1 (hsgn i)
  have hs : (∑ k, (sumC p) k * (sumC p) k) ≠ 0 := sumC_sq_sum_ne_zero hp hp3
  refine ⟨Module.reflection (coefReflForm_coefRoot b id (sumC p) Function.injective_id hs),
    (hA _).2 (isIsom_reflection_coefRoot hp b id (sumC p) Function.injective_id hs hP hS 0),
    isRefl_reflection hp (coefReflForm_coefRoot b id (sumC p) Function.injective_id hs), ?_,
    reflection_sumC_ne hp hp3 b hs⟩
  exact coefReflection_apply_sum b id (sumC p) Function.injective_id sumC_sum hs

theorem exists_isRefl_fix_sum_of_orthClass_four (hp : p ≠ 2) (hp3 : p ≠ 3)
    (b : Module.Basis (Fin 4) (ZMod p) U) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hperm : ∀ σ, permMap p b σ ∈ A)
    (hsgn : ∀ i, diagMap p b (fun j => if j = i then -1 else 1) ∈ A)
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p}
    (hc : c ≠ 0) (hA : A = Subgroup.closure (ClassRefl p Q c)) :
    ∃ r ∈ A, IsRefl p r ∧ r (∑ i, b i) = ∑ i, b i ∧
      ∀ (k : Fin 4) (c' s : ZMod p), r (b 3) ≠ c' • b k + s • ∑ i, b i := by
  have hP : ∀ σ, IsIsom p Q (permMap p b σ) :=
    fun σ => isIsom_of_mem_closure_classRefl (hA ▸ hperm σ)
  have hS : ∀ i, IsIsom p Q (diagMap p b (fun j => if j = i then -1 else 1)) :=
    fun i => isIsom_of_mem_closure_classRefl (hA ▸ hsgn i)
  have hs : (∑ k, (sumC p) k * (sumC p) k) ≠ 0 := sumC_sq_sum_ne_zero hp hp3
  have hsign : diagMap p b (fun j => if j = 0 then -1 else 1) ∈ ClassRefl p Q c :=
    @mem_classRefl_of_isRefl_mem_closure p _ U _ _ hp (Module.Finite.of_basis b) Q hQ c hc
      (diagMap p b (fun j => if j = 0 then -1 else 1)) (hA ▸ hsgn 0)
      (isRefl_diagMap_sign hp b 0)
  obtain ⟨-, -, x, hQx, hsx⟩ := hsign
  obtain ⟨μ, -, hQμ⟩ := exists_smul_basis_of_signChange hp b 0 hP 0 hQx hsx
  have h6 : (6 : ZMod p) ≠ 0 := six_ne_zero_of_ne_two_of_ne_three hp hp3
  have hQv : Q (coefRoot b id (sumC p)) = (36 : ZMod p) * Q (b 0) := by
    rw [Q_coefRoot hp b id (sumC p) Function.injective_id hP hS 0, sumC_sq_sum]
  have hQw : Q ((μ * (6 : ZMod p)⁻¹) • coefRoot b id (sumC p)) = c := by
    rw [QuadraticMap.map_smul, hQv, smul_eq_mul]
    have hinv : (6 : ZMod p)⁻¹ * 6⁻¹ * 36 = 1 := by
      calc (6 : ZMod p)⁻¹ * 6⁻¹ * 36 = (6⁻¹ * 6) * (6⁻¹ * 6) := by ring
        _ = 1 := by rw [inv_mul_cancel₀ h6, one_mul]
    calc (μ * 6⁻¹) * (μ * 6⁻¹) * (36 * Q (b 0))
        = (μ * μ * Q (b 0)) * ((6 : ZMod p)⁻¹ * 6⁻¹ * 36) := by ring
      _ = c := by rw [hinv, mul_one, hQμ]
  have hrv : Module.reflection (coefReflForm_coefRoot b id (sumC p) Function.injective_id hs)
      (coefRoot b id (sumC p)) = -coefRoot b id (sumC p) := by
    rw [Module.reflection_apply, coefReflForm_coefRoot b id (sumC p) Function.injective_id hs,
      two_smul]
    abel
  have hrw : Module.reflection (coefReflForm_coefRoot b id (sumC p) Function.injective_id hs)
      ((μ * (6 : ZMod p)⁻¹) • coefRoot b id (sumC p)) =
      -((μ * (6 : ZMod p)⁻¹) • coefRoot b id (sumC p)) := by
    rw [map_smul, hrv, smul_neg]
  have hrmem : Module.reflection (coefReflForm_coefRoot b id (sumC p) Function.injective_id hs) ∈
      ClassRefl p Q c :=
    ⟨isRefl_reflection hp (coefReflForm_coefRoot b id (sumC p) Function.injective_id hs),
      isIsom_reflection_coefRoot hp b id (sumC p) Function.injective_id hs hP hS 0,
      (μ * (6 : ZMod p)⁻¹) • coefRoot b id (sumC p), hQw, hrw⟩
  refine ⟨Module.reflection (coefReflForm_coefRoot b id (sumC p) Function.injective_id hs), ?_,
    isRefl_reflection hp (coefReflForm_coefRoot b id (sumC p) Function.injective_id hs), ?_,
    reflection_sumC_ne hp hp3 b hs⟩
  · rw [hA]
    exact Subgroup.subset_closure hrmem
  · exact coefReflection_apply_sum b id (sumC p) Function.injective_id sumC_sum hs

end CFSG.StandardType.ZS

end
