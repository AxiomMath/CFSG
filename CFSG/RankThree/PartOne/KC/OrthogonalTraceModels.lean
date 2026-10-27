module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace
public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module

section Trace

variable (K E : Type*) [Field K] [Field E] [Algebra K E] [Finite E]

theorem trace_fieldEquiv (σ : K ≃+* K) (τ : E ≃+* E)
    (hτ : ∀ c, τ (algebraMap K E c) = algebraMap K E (σ c)) (z : E) :
    Algebra.trace K E (τ z) = σ (Algebra.trace K E z) := by
  apply (algebraMap K E).injective
  calc algebraMap K E (Algebra.trace K E (τ z))
      = ∑ i ∈ Finset.range (Module.finrank K E), (τ z) ^ Nat.card K ^ i :=
        FiniteField.algebraMap_trace_eq_sum_pow K E (τ z)
    _ = τ (∑ i ∈ Finset.range (Module.finrank K E), z ^ Nat.card K ^ i) := by
      simp only [map_sum, map_pow]
    _ = τ (algebraMap K E (Algebra.trace K E z)) := by
      rw [FiniteField.algebraMap_trace_eq_sum_pow]
    _ = algebraMap K E (σ (Algebra.trace K E z)) := hτ _

theorem exists_trace_mul_ne_zero {a : E} (ha : a ≠ 0) :
    ∃ b : E, Algebra.trace K E (a * b) ≠ 0 := by
  by_contra hb
  push Not at hb
  exact ha ((traceForm_nondegenerate K E).1 a fun b => by simpa using hb b)

theorem eq_zero_of_trace_mul_eq_zero {a : E} (h : ∀ b : E, Algebra.trace K E (a * b) = 0) :
    a = 0 := by
  by_contra ha
  obtain ⟨b, hb⟩ := exists_trace_mul_ne_zero K E ha
  exact hb (h b)

theorem traceTransfer_semilin {W : Type*} [AddCommGroup W] [Module E W]
    (σ : K ≃+* K) (τ : E ≃+* E)
    (hτ : ∀ c, τ (algebraMap K E c) = algebraMap K E (σ c))
    (S : W → W) (hS : ∀ (c : E) w, S (c • w) = τ c • S w)
    (B : W → W → K) (hBS : ∀ u w, B (S u) (S w) = σ (B u w))
    (H : W → W → E)
    (htr : ∀ u w c, Algebra.trace K E (H u w * c) = B u (c • w))
    (u w : W) : H (S u) (S w) = τ (H u w) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_trace_mul_eq_zero K E
  intro c
  rw [sub_mul, map_sub, sub_eq_zero]
  calc Algebra.trace K E (H (S u) (S w) * c)
      = B (S u) (c • S w) := htr _ _ _
    _ = B (S u) (S (τ.symm c • w)) := by rw [hS, τ.apply_symm_apply]
    _ = σ (B u (τ.symm c • w)) := hBS _ _
    _ = σ (Algebra.trace K E (H u w * τ.symm c)) :=
      congrArg σ (htr u w (τ.symm c)).symm
    _ = Algebra.trace K E (τ (H u w * τ.symm c)) :=
      (trace_fieldEquiv K E σ τ hτ _).symm
    _ = Algebra.trace K E (τ (H u w) * c) := by rw [map_mul, τ.apply_symm_apply]

end Trace

section Unitary

variable (K E : Type*) [Field K] [Field E] [Algebra K E] [Finite K] [Finite E]

@[expose] noncomputable def frobPow (d : ℕ) : E ≃ₐ[K] E :=
  haveI := Fintype.ofFinite K
  FiniteField.frobeniusAlgEquivOfAlgebraic K E ^ d

theorem frobPow_apply (d : ℕ) (z : E) : frobPow K E d z = z ^ (Nat.card K ^ d) := by
  have := Fintype.ofFinite K
  rw [frobPow, AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  simp only [Fintype.card_eq_nat_card]

theorem frobPow_frobPow {d : ℕ} (hd : finrank K E = 2 * d) (z : E) :
    frobPow K E d (frobPow K E d z) = z := by
  have := Fintype.ofFinite E
  rw [frobPow_apply, frobPow_apply, ← pow_mul, ← pow_add, ← two_mul, ← hd,
    ← Module.natCard_eq_pow_finrank, Nat.card_eq_fintype_card, FiniteField.pow_card]

@[expose] noncomputable def fixedSubfield (d : ℕ) : IntermediateField K E where
  toSubalgebra := AlgHom.equalizer (frobPow K E d : E →ₐ[K] E) (AlgHom.id K E)
  inv_mem' := fun x hx => by
    have hx' : frobPow K E d x = x := hx
    show frobPow K E d x⁻¹ = x⁻¹
    rw [map_inv₀, hx']

theorem mem_fixedSubfield (d : ℕ) (z : E) :
    z ∈ fixedSubfield K E d ↔ z ^ (Nat.card K ^ d) = z := by
  rw [← frobPow_apply]
  exact Iff.rfl

theorem map_mem_fixedSubfield_iff (d : ℕ) (τ : E ≃+* E) (z : E) :
    z ∈ fixedSubfield K E d ↔ τ z ∈ fixedSubfield K E d := by
  rw [mem_fixedSubfield, mem_fixedSubfield, ← map_pow, τ.injective.eq_iff]

@[expose] noncomputable def fixedSubfieldAut (d : ℕ) (τ : E ≃+* E) :
    fixedSubfield K E d ≃+* fixedSubfield K E d :=
  τ.restrict _ _ (map_mem_fixedSubfield_iff K E d τ)

theorem fixedSubfieldAut_ne_one (d : ℕ) (σ : K ≃+* K) (τ : E ≃+* E)
    (hτ : ∀ c, τ (algebraMap K E c) = algebraMap K E (σ c)) (hσ : σ ≠ 1) :
    fixedSubfieldAut K E d τ ≠ 1 := by
  intro h
  apply hσ
  ext c
  apply (algebraMap K E).injective
  have hc := congrArg (fun f : fixedSubfield K E d ≃+* fixedSubfield K E d =>
    (f ⟨algebraMap K E c, (fixedSubfield K E d).algebraMap_mem c⟩ : E)) h
  change τ (algebraMap K E c) = algebraMap K E c at hc
  rw [hτ] at hc
  exact hc

theorem exists_unitaryFieldData {d : ℕ} (hd : finrank K E = 2 * d) :
    ∃ (ℓ f : ℕ) (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ (f * d) E),
      Nat.card K = ℓ ^ f ∧ ∀ z, hU.bar z = z ^ (Nat.card K ^ d) := by
  have := Fintype.ofFinite K
  have hcharP : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨n, hℓ, hcard⟩ := FiniteField.card K (ringChar K)
  have hq : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hd0 : 0 < d := by
    have := Module.finrank_pos (R := K) (M := E)
    omega
  refine ⟨ringChar K, n, ⟨hℓ, Nat.mul_pos n.pos hd0, ?_⟩, hq, fun z => ?_⟩
  · rw [Module.natCard_eq_pow_finrank (K := K), hd, hq, ← pow_mul]
    congr 1
    ring
  · rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply, hq, ← pow_mul]

theorem card_fixedSubfield {d : ℕ} (hd : finrank K E = 2 * d) :
    Nat.card (fixedSubfield K E d) = Nat.card K ^ d := by
  obtain ⟨ℓ, f, hU, hq, hbar⟩ := exists_unitaryFieldData K E hd
  have h1 : Nat.card (fixedSubfield K E d) = Nat.card hU.fixedField :=
    Nat.card_congr (Equiv.subtypeEquivRight fun z => by
      rw [mem_fixedSubfield,
        CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.mem_fixedField, hbar])
  rw [h1, hU.card_fixedField, hq, ← pow_mul, mul_comm]

theorem finrank_fixedSubfield {d : ℕ} (hd : finrank K E = 2 * d) :
    finrank K (fixedSubfield K E d) = d := by
  have h := card_fixedSubfield K E hd
  rw [Module.natCard_eq_pow_finrank (K := K)] at h
  exact Nat.pow_right_injective (Nat.succ_le_of_lt Finite.one_lt_card) h

theorem algebraMap_trace_fixedSubfield {d : ℕ} (hd : finrank K E = 2 * d)
    (s : fixedSubfield K E d) :
    algebraMap K E (Algebra.trace K (fixedSubfield K E d) s) =
      ∑ i ∈ Finset.range d, (s : E) ^ (Nat.card K ^ i) := by
  have h := FiniteField.algebraMap_trace_eq_sum_pow K (fixedSubfield K E d) s
  have h2 := congrArg (algebraMap (fixedSubfield K E d) E) h
  rw [← IsScalarTower.algebraMap_apply, finrank_fixedSubfield K E hd] at h2
  simpa using h2

theorem trace_eq_trace_fixedSubfield {d : ℕ} (hd : finrank K E = 2 * d) (z : E)
    (s : fixedSubfield K E d) (hs : (s : E) = z + z ^ (Nat.card K ^ d)) :
    Algebra.trace K E z = Algebra.trace K (fixedSubfield K E d) s := by
  apply (algebraMap K E).injective
  rw [algebraMap_trace_fixedSubfield K E hd, FiniteField.algebraMap_trace_eq_sum_pow, hd,
    two_mul, Finset.sum_range_add, hs]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (z + z ^ (Nat.card K ^ d)) ^ (Nat.card K ^ i) =
      z ^ (Nat.card K ^ i) + (z ^ (Nat.card K ^ d)) ^ (Nat.card K ^ i) := by
    rw [← frobPow_apply K E i, map_add, frobPow_apply, frobPow_apply]
  rw [h1, ← pow_mul, ← pow_add]

theorem isUnitaryInvolution {d : ℕ} (hd : finrank K E = 2 * d) :
    CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution (frobPow K E d).toRingEquiv := by
  obtain ⟨ℓ, f, hU, hq, hbar⟩ := exists_unitaryFieldData K E hd
  have hb : ∀ z, hU.bar z = frobPow K E d z := fun z => by rw [hbar, frobPow_apply]
  refine ⟨frobPow_frobPow K E hd, ?_, fun a ha => ?_, fun a ha _ => ?_⟩
  · obtain ⟨c, hc⟩ := hU.exists_bar_ne
    exact ⟨c, by rwa [hb] at hc⟩
  · have hm : hU.bar a = a := by rw [hb]; exact ha
    obtain ⟨c, hc⟩ := hU.traceLin_surjective ⟨a, hm⟩
    refine ⟨c, ?_⟩
    have := congrArg Subtype.val hc
    simpa [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.traceLin,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.trace, hb] using this
  · have hm : hU.bar a = a := by rw [hb]; exact ha
    obtain ⟨c, hc⟩ := hU.normHom_surjective ⟨a, hm⟩
    refine ⟨c, ?_⟩
    have := congrArg Subtype.val hc
    simp only [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.coe_normHom,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.norm, hb] at this
    simpa [mul_comm] using this

section Forms

variable {K E}

theorem mul_frobPow_mem_fixedSubfield {d : ℕ} (hd : finrank K E = 2 * d) (a : E) :
    a * frobPow K E d a ∈ fixedSubfield K E d := by
  rw [mem_fixedSubfield, ← frobPow_apply, map_mul, frobPow_frobPow K E hd, mul_comm]

@[expose] noncomputable def unitaryNorm {d : ℕ} (hd : finrank K E = 2 * d) (a : E) :
    fixedSubfield K E d :=
  ⟨a * frobPow K E d a, mul_frobPow_mem_fixedSubfield hd a⟩

theorem coe_unitaryNorm {d : ℕ} (hd : finrank K E = 2 * d) (a : E) :
    (unitaryNorm hd a : E) = a * frobPow K E d a := rfl

@[expose] noncomputable def hermitianForm {d : ℕ} (hd : finrank K E = 2 * d) :
    QuadraticForm K E where
  toFun a := Algebra.trace K (fixedSubfield K E d) (unitaryNorm hd a)
  toFun_smul c a := by
    have : unitaryNorm hd (c • a) = (c * c) • unitaryNorm hd a := by
      apply Subtype.ext
      simp only [coe_unitaryNorm, map_smul, smul_mul_smul_comm, IntermediateField.coe_smul]
    rw [this, map_smul]
  exists_companion' := ⟨(Algebra.traceForm K E).compl₁₂ LinearMap.id
      (frobPow K E d).toLinearMap, fun x y => by
    have key : Algebra.trace K E (x * frobPow K E d y) =
        Algebra.trace K _ (unitaryNorm hd (x + y) - unitaryNorm hd x - unitaryNorm hd y) := by
      apply trace_eq_trace_fixedSubfield K E hd
      simp only [AddSubgroupClass.coe_sub, coe_unitaryNorm, map_add]
      rw [← frobPow_apply, map_mul, frobPow_frobPow K E hd]
      ring
    simp only [map_sub] at key
    show Algebra.trace K _ (unitaryNorm hd (x + y)) = Algebra.trace K _ (unitaryNorm hd x) +
      Algebra.trace K _ (unitaryNorm hd y) + Algebra.trace K E (x * frobPow K E d y)
    linear_combination (-1 : K) * key⟩

theorem hermitianForm_apply {d : ℕ} (hd : finrank K E = 2 * d) (a : E) :
    hermitianForm hd a = Algebra.trace K (fixedSubfield K E d) (unitaryNorm hd a) := rfl

theorem hermitianForm_polar {d : ℕ} (hd : finrank K E = 2 * d) (a b : E) :
    QuadraticMap.polar (hermitianForm hd) a b = Algebra.trace K E (a * frobPow K E d b) := by
  have key : Algebra.trace K E (a * frobPow K E d b) =
      Algebra.trace K _ (unitaryNorm hd (a + b) - unitaryNorm hd a - unitaryNorm hd b) := by
    apply trace_eq_trace_fixedSubfield K E hd
    simp only [AddSubgroupClass.coe_sub, coe_unitaryNorm, map_add]
    rw [← frobPow_apply, map_mul, frobPow_frobPow K E hd]
    ring
  simp only [map_sub] at key
  rw [QuadraticMap.polar, key]
  simp only [hermitianForm_apply]

end Forms

end Unitary

section Paired

variable (K E : Type*) [Field K] [Field E] [Algebra K E]

@[expose] noncomputable def pairedForm : QuadraticForm K (E × E) :=
  LinearMap.BilinMap.toQuadraticMap
    ((Algebra.traceForm K E).compl₁₂ (LinearMap.fst K E E) (LinearMap.snd K E E))

theorem pairedForm_apply (a b : E) :
    pairedForm K E (a, b) = Algebra.trace K E (a * b) := by
  simp [pairedForm, LinearMap.BilinMap.toQuadraticMap_apply]

theorem pairedForm_polar (a b a' b' : E) :
    QuadraticMap.polar (pairedForm K E) (a, b) (a', b') =
      Algebra.trace K E (a * b' + a' * b) := by
  rw [QuadraticMap.polar, Prod.mk_add_mk, pairedForm_apply, pairedForm_apply, pairedForm_apply,
    ← map_sub, ← map_sub]
  congr 1
  ring

theorem polarBilin_nondegenerate_of_separating {M : Type*} [AddCommGroup M] [Module K M]
    {Q : QuadraticForm K M} (h : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) :
    (QuadraticMap.polarBilin Q).Nondegenerate :=
  ⟨h, fun y hy => h y fun x => by rw [QuadraticMap.polar_comm]; exact hy x⟩

theorem pairedForm_nondegenerate [Finite E] :
    (QuadraticMap.polarBilin (pairedForm K E)).Nondegenerate := by
  refine polarBilin_nondegenerate_of_separating K fun x hx => ?_
  obtain ⟨a, b⟩ := x
  have h1 : ∀ b' : E, Algebra.trace K E (a * b') = 0 := fun b' => by
    simpa [pairedForm_polar] using hx (0, b')
  have h2 : ∀ a' : E, Algebra.trace K E (b * a') = 0 := fun a' => by
    simpa [pairedForm_polar, mul_comm] using hx (a', 0)
  rw [eq_zero_of_trace_mul_eq_zero K E h1, eq_zero_of_trace_mul_eq_zero K E h2]
  rfl

variable {K E}

@[expose] def mulEquiv (u : Eˣ) : E ≃ₗ[K] E where
  toFun a := u * a
  invFun a := ((u⁻¹ : Eˣ) : E) * a
  map_add' a b := mul_add _ _ _
  map_smul' c a := by simp
  left_inv a := by simp
  right_inv a := by simp

@[simp] theorem mulEquiv_apply (u : Eˣ) (a : E) : mulEquiv (K := K) u a = u * a := rfl

variable (K E) in
@[expose] def mulEquivHom : Eˣ →* (E ≃ₗ[K] E) where
  toFun := mulEquiv
  map_one' := by ext a; simp
  map_mul' u v := by ext a; simp [mul_assoc]

theorem mulEquivHom_injective : Function.Injective (mulEquivHom K E) := fun u v h => by
  have := congrArg (fun g : E ≃ₗ[K] E => g 1) h
  exact Units.ext (by simpa [mulEquivHom] using this)

@[expose] def pairedRotation (u : Eˣ) : (E × E) ≃ₗ[K] (E × E) :=
  (mulEquiv u).prodCongr (mulEquiv u⁻¹)

@[simp] theorem pairedRotation_apply (u : Eˣ) (a b : E) :
    pairedRotation (K := K) u (a, b) = (u * a, ((u⁻¹ : Eˣ) : E) * b) := rfl

variable (K E) in
@[expose] def pairedRotationHom : Eˣ →* ((E × E) ≃ₗ[K] (E × E)) where
  toFun := pairedRotation
  map_one' := by
    refine LinearEquiv.ext fun ⟨a, b⟩ => ?_
    simp
  map_mul' u v := by
    refine LinearEquiv.ext fun ⟨a, b⟩ => ?_
    simp only [pairedRotation_apply, LinearEquiv.mul_apply, Units.val_mul, mul_inv_rev,
      Prod.mk.injEq]
    constructor <;> ring

theorem pairedRotationHom_injective : Function.Injective (pairedRotationHom K E) := fun u v h => by
  have := congrArg (fun g : (E × E) ≃ₗ[K] (E × E) => (g (1, 0)).1) h
  exact Units.ext (by simpa [pairedRotationHom] using this)

theorem pairedForm_pairedRotation (u : Eˣ) (a b : E) :
    pairedForm K E (pairedRotation (K := K) u (a, b)) = pairedForm K E (a, b) := by
  rw [pairedRotation_apply, pairedForm_apply, pairedForm_apply]
  congr 1
  calc (u : E) * a * (((u⁻¹ : Eˣ) : E) * b) = ((u * u⁻¹ : Eˣ) : E) * (a * b) := by
        rw [Units.val_mul]; ring
    _ = a * b := by simp

theorem pairedRotation_mem_orthogonalGroup (u : Eˣ) :
    pairedRotation (K := K) u ∈ TauCeti.QuadraticMap.orthogonalGroup (pairedForm K E) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  rintro ⟨a, b⟩
  exact pairedForm_pairedRotation u a b

end Paired

section UnitaryRotation

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Finite K] [Finite E] {d : ℕ}

theorem hermitianForm_nondegenerate (hd : finrank K E = 2 * d) :
    (QuadraticMap.polarBilin (hermitianForm hd)).Nondegenerate := by
  refine polarBilin_nondegenerate_of_separating K fun a ha => ?_
  refine eq_zero_of_trace_mul_eq_zero K E fun b => ?_
  have := ha ((frobPow K E d).symm b)
  rwa [hermitianForm_polar, AlgEquiv.apply_symm_apply] at this

theorem hermitianForm_mulEquiv (hd : finrank K E = 2 * d) (u : Eˣ)
    (hu : (u : E) * frobPow K E d u = 1) (a : E) :
    hermitianForm hd (mulEquiv (K := K) u a) = hermitianForm hd a := by
  rw [hermitianForm_apply, hermitianForm_apply]
  congr 1
  apply Subtype.ext
  simp only [coe_unitaryNorm, mulEquiv_apply, map_mul]
  calc (u : E) * a * (frobPow K E d u * frobPow K E d a) =
      ((u : E) * frobPow K E d u) * (a * frobPow K E d a) := by ring
    _ = a * frobPow K E d a := by rw [hu, one_mul]

theorem mulEquiv_mem_orthogonalGroup (hd : finrank K E = 2 * d) (u : Eˣ)
    (hu : (u : E) * frobPow K E d u = 1) :
    mulEquiv (K := K) u ∈ TauCeti.QuadraticMap.orthogonalGroup (hermitianForm hd) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  exact hermitianForm_mulEquiv hd u hu

end UnitaryRotation


section Galois

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Finite K] [Finite E]

theorem frobPow_zero : frobPow K E 0 = 1 := by
  rw [frobPow, pow_zero]

theorem frobPow_add (m n : ℕ) : frobPow K E (m + n) = frobPow K E m * frobPow K E n := by
  rw [frobPow, frobPow, frobPow, pow_add]

theorem frobPow_eq_one_iff (n : ℕ) : frobPow K E n = 1 ↔ finrank K E ∣ n := by
  let _ := Fintype.ofFinite K
  rw [frobPow, ← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic K E, orderOf_dvd_iff_pow_eq_one]

theorem exists_frobPow_eq (σ : E ≃ₐ[K] E) : ∃ j < finrank K E, frobPow K E j = σ := by
  let _ := Fintype.ofFinite K
  obtain ⟨j, hj⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K E).2 σ
  refine ⟨j.1, j.2, ?_⟩
  unfold frobPow
  exact hj

theorem exists_involution_eq_frobPow (σ : E ≃ₐ[K] E) (hσσ : ∀ z, σ (σ z) = z) (hne : σ ≠ 1) :
    ∃ d, finrank K E = 2 * d ∧ σ = frobPow K E d := by
  obtain ⟨j, hj, rfl⟩ := exists_frobPow_eq (K := K) (E := E) σ
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hne (by rw [frobPow_zero])
  have hsq : frobPow K E (j + j) = 1 := by
    rw [frobPow_add]
    ext z
    exact hσσ z
  obtain ⟨k, hk⟩ := (frobPow_eq_one_iff (j + j)).mp hsq
  have hk1 : k = 1 := by
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · rcases Nat.lt_or_ge k 1 with hk0 | hk0
      · have : k = 0 := by omega
        subst this
        omega
      · omega
    · nlinarith
  subst hk1
  exact ⟨j, by omega, rfl⟩

end Galois

end CFSG.RankThree.PartOne.KCOrthogonal
