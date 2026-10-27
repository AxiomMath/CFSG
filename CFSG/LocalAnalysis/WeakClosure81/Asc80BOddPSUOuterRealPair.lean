module

public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
import CFSG.Mathlib.FieldTheory.Finite.QuadraticZero
import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LocalAnalysis.WeakClosure81.UOuter

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

private lemma exists_isotropic_span_pair (h : UnitaryFieldData p f K)
    {G X : Matrix (Fin n) (Fin n) K} {m α : K} (hXG : Xᵀ * G * X = m • G)
    (hX2 : X * X = α • 1) {u v : Fin n → K} (hu0 : u ≠ 0)
    (hur : ∀ i, h.bar (u i) = u i) (hvr : ∀ i, h.bar (v i) = v i) (hXu : X *ᵥ u = v)
    (huu : u ⬝ᵥ (G *ᵥ u) = 0) (huv : u ⬝ᵥ (G *ᵥ v) = 0)
    (hvu : v ⬝ᵥ (G *ᵥ u) = 0) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, gramForm h G x y = 0) ∧
      (∀ w ∈ W, X *ᵥ w ∈ W) ∧ ∀ w ∈ W, (fun i => h.bar (w i)) ∈ W := by
  have hbaru : (fun i => h.bar (u i)) = u := funext hur
  have hbarv : (fun i => h.bar (v i)) = v := funext hvr
  have hXu2 : X *ᵥ v = α • u := by
    rw [← hXu, Matrix.mulVec_mulVec, hX2, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hvv : v ⬝ᵥ (G *ᵥ v) = 0 := by
    have h1 : v ⬝ᵥ (G *ᵥ v) = u ⬝ᵥ ((Xᵀ * G * X) *ᵥ u) := by
      rw [← hXu]
      rw [Matrix.mulVec_mulVec, dotProduct_mulVec, vecMul_mulVec, ← Matrix.mul_assoc,
        ← dotProduct_mulVec]
    rw [h1, hXG, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, huu, mul_zero]
  have hgvv : gramForm h G v v = 0 := by rw [gramForm_apply, hbarv, hvv]
  have hgvu : gramForm h G v u = 0 := by rw [gramForm_apply, hbarv, hvu]
  have hguv : gramForm h G u v = 0 := by rw [gramForm_apply, hbaru, huv]
  have hguu : gramForm h G u u = 0 := by rw [gramForm_apply, hbaru, huu]
  refine ⟨Submodule.span K {u, v}, ?_, ?_, ?_, ?_⟩
  · intro hbot
    have hu' : u ∈ (⊥ : Submodule K (Fin n → K)) := by
      rw [← hbot]
      exact Submodule.subset_span (by simp)
    rw [Submodule.mem_bot] at hu'
    exact hu0 hu'
  · intro a ha b hb
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp ha
    obtain ⟨e, g, rfl⟩ := Submodule.mem_span_pair.mp hb
    simp only [map_add, LinearMap.map_smulₛₗ₂, map_smul, LinearMap.add_apply, smul_eq_mul,
      hguu, hguv, hgvu, hgvv, mul_zero, add_zero]
  · intro w hw
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hw
    have hXw : X *ᵥ (a • u + b • v) = a • v + (b * α) • u := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hXu2, hXu, smul_smul]
    rw [hXw]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · intro w hw
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hw
    have hbar : (fun i => h.bar ((a • u + b • v) i)) = h.bar a • u + h.bar b • v := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, hur i, hvr i]
    rw [hbar]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem exists_real_isotropic_stable_of_skew (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    (hn : 3 ≤ n) {G X : Matrix (Fin n) (Fin n) K} (hGr : G.map h.bar = G)
    (hXr : X.map h.bar = X) {m α : K} (hX : Xᵀ * G * X = m • G) (hX2 : X * X = α • 1)
    (hGX : Gᵀ = -G ∨ (Gᵀ = G ∧ Xᵀ * G = -(G * X))) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, gramForm h G x y = 0) ∧
      (∀ w ∈ W, X *ᵥ w ∈ W) ∧ ∀ w ∈ W, (fun i => h.bar (w i)) ∈ W := by
  classical
  have hKfin : Finite K := h.finite
  have hkfin : Finite h.fixedField :=
    Finite.of_injective (Subfield.subtype h.fixedField) (Subfield.subtype_injective h.fixedField)
  have hchar : CharP K p := h.charP
  have htwo : (2 : K) ≠ 0 := by
    intro h2
    have hpdiv : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp h2
    exact hp ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp hpdiv)
  let φ : h.fixedField →+* K := Subfield.subtype h.fixedField
  have hGmem : ∀ i j, h.bar (G i j) = G i j := by
    intro i j
    have := congrFun (congrFun hGr i) j
    simpa using this
  have hXmem : ∀ i j, h.bar (X i j) = X i j := by
    intro i j
    have := congrFun (congrFun hXr i) j
    simpa using this
  let G₀ : Matrix (Fin n) (Fin n) h.fixedField :=
    fun i j => ⟨G i j, h.mem_fixedField.mpr (hGmem i j)⟩
  let X₀ : Matrix (Fin n) (Fin n) h.fixedField :=
    fun i j => ⟨X i j, h.mem_fixedField.mpr (hXmem i j)⟩
  have hG₀ : G₀.map φ = G := by
    ext i j
    rfl
  have hX₀ : X₀.map φ = X := by
    ext i j
    rfl
  have hM₀ : (G₀ * X₀).map φ = G * X := by
    rw [Matrix.map_mul, hG₀, hX₀]
  have hzex : ∃ z : Fin n → h.fixedField, z ≠ 0 ∧
      ((Gᵀ = -G ∧ z ⬝ᵥ ((G₀ * X₀) *ᵥ z) = 0) ∨
       (Gᵀ = G ∧ Xᵀ * G = -(G * X) ∧ z ⬝ᵥ (G₀ *ᵥ z) = 0)) := by
    rcases hGX with hneg | ⟨hsym, hskew⟩
    · obtain ⟨z, hz0, hz⟩ := CFSG.FiniteField.exists_ne_zero_dotProduct_mulVec_eq_zero
        (σ := Fin n) (by simpa using hn) (G₀ * X₀)
      exact ⟨z, hz0, Or.inl ⟨hneg, hz⟩⟩
    · obtain ⟨z, hz0, hz⟩ := CFSG.FiniteField.exists_ne_zero_dotProduct_mulVec_eq_zero
        (σ := Fin n) (by simpa using hn) G₀
      exact ⟨z, hz0, Or.inr ⟨hsym, hskew, hz⟩⟩
  obtain ⟨z, hz0, hzcase⟩ := hzex
  let u : Fin n → K := fun i => φ (z i)
  let v : Fin n → K := X *ᵥ u
  have hu0 : u ≠ 0 := by
    intro hu
    apply hz0
    funext i
    have hi : φ (z i) = 0 := by
      have := congrFun hu i
      simpa [u] using this
    exact (Subfield.subtype_injective h.fixedField) (by simpa using hi)
  have hur : ∀ i, h.bar (u i) = u i := fun i => h.mem_fixedField.mp (z i).2
  have hvr : ∀ i, h.bar (v i) = v i := by
    intro i
    have hh := RingHom.map_mulVec h.bar X u i
    have hcomp : h.bar ∘ u = u := funext hur
    rw [hXr, hcomp] at hh
    simpa [v] using hh
  have hcast : ∀ M : Matrix (Fin n) (Fin n) h.fixedField,
      u ⬝ᵥ (M.map φ *ᵥ u) = φ (z ⬝ᵥ (M *ᵥ z)) := by
    intro M
    rw [RingHom.map_dotProduct]
    have h1 : M.map φ *ᵥ u = φ ∘ (M *ᵥ z) := by
      funext i
      exact (RingHom.map_mulVec φ M z i).symm
    rw [h1]
    rfl
  have htrans : ∀ (M : Matrix (Fin n) (Fin n) K) (a b : Fin n → K),
      a ⬝ᵥ (M *ᵥ b) = b ⬝ᵥ (Mᵀ *ᵥ a) := by
    intro M a b
    simpa using (Matrix.dotProduct_transpose_mulVec (A := Mᵀ) (x := a) (y := b))
  rcases hzcase with ⟨hneg, hzGX⟩ | ⟨hsym, hskew, hzG⟩
  · have huGX : u ⬝ᵥ ((G * X) *ᵥ u) = 0 := by
      rw [← hM₀, hcast (G₀ * X₀), hzGX, map_zero]
    have huu : u ⬝ᵥ (G *ᵥ u) = 0 := by
      have h1 : u ⬝ᵥ (G *ᵥ u) = u ⬝ᵥ (Gᵀ *ᵥ u) := htrans G u u
      have h2 : u ⬝ᵥ (Gᵀ *ᵥ u) = -(u ⬝ᵥ (G *ᵥ u)) := by
        rw [hneg, Matrix.neg_mulVec, dotProduct_neg]
      have h3 : u ⬝ᵥ (G *ᵥ u) = -(u ⬝ᵥ (G *ᵥ u)) := h1.trans h2
      have h4 : (2 : K) * (u ⬝ᵥ (G *ᵥ u)) = 0 := by
        rw [two_mul]
        nth_rewrite 2 [h3]
        ring
      exact (mul_eq_zero.mp h4).resolve_left htwo
    have huv : u ⬝ᵥ (G *ᵥ v) = 0 := by
      rw [show v = X *ᵥ u from rfl, Matrix.mulVec_mulVec]
      exact huGX
    have hvu : v ⬝ᵥ (G *ᵥ u) = 0 := by
      rw [htrans G v u, hneg, Matrix.neg_mulVec, dotProduct_neg, huv, neg_zero]
    exact exists_isotropic_span_pair h hX hX2 hu0 hur hvr rfl huu huv hvu
  · have huu : u ⬝ᵥ (G *ᵥ u) = 0 := by
      rw [← hG₀, hcast G₀, hzG, map_zero]
    have huGX : u ⬝ᵥ ((G * X) *ᵥ u) = 0 := by
      have h1 : u ⬝ᵥ ((G * X) *ᵥ u) = u ⬝ᵥ ((G * X)ᵀ *ᵥ u) := htrans (G * X) u u
      have h2 : u ⬝ᵥ ((G * X)ᵀ *ᵥ u) = u ⬝ᵥ ((Xᵀ * G) *ᵥ u) := by
        rw [Matrix.transpose_mul, hsym]
      have h3 : u ⬝ᵥ ((Xᵀ * G) *ᵥ u) = -(u ⬝ᵥ ((G * X) *ᵥ u)) := by
        rw [hskew, Matrix.neg_mulVec, dotProduct_neg]
      have h4 : (2 : K) * (u ⬝ᵥ ((G * X) *ᵥ u)) = 0 := by
        rw [two_mul]
        nth_rewrite 2 [h1.trans (h2.trans h3)]
        ring
      exact (mul_eq_zero.mp h4).resolve_left htwo
    have huv : u ⬝ᵥ (G *ᵥ v) = 0 := by
      rw [show v = X *ᵥ u from rfl, Matrix.mulVec_mulVec]
      exact huGX
    have hvu : v ⬝ᵥ (G *ᵥ u) = 0 := by
      rw [show v = X *ᵥ u from rfl]
      have h1 : (X *ᵥ u) ⬝ᵥ (G *ᵥ u) = u ⬝ᵥ ((Xᵀ * G) *ᵥ u) := by
        rw [dotProduct_mulVec, vecMul_mulVec, ← dotProduct_mulVec]
      rw [h1, hskew, Matrix.neg_mulVec, dotProduct_neg, huGX, neg_zero]
    exact exists_isotropic_span_pair h hX hX2 hu0 hur hvr rfl huu huv hvu

end CFSG.LocalAnalysis.WeakClosure81.UOuter
