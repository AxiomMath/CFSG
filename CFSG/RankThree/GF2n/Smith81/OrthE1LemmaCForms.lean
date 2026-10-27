module

public import CFSG.Open.StatedDefs

public section

open scoped Matrix

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.Open

@[expose] def IsPolarOf {ι K : Type} [Field K] (f : (ι → K) → K)
    (P : (ι → K) →ₗ[K] (ι → K) →ₗ[K] K) : Prop :=
  ∀ x y, f (x + y) = f x + f y + P x y

section Generic

variable {ι K : Type} [Field K] {f : (ι → K) → K} {P : (ι → K) →ₗ[K] (ι → K) →ₗ[K] K}

theorem IsPolarOf.alt [CharP K 2] (h : IsPolarOf f P) (x : ι → K) : P x x = 0 := by
  have h0 := h 0 0
  simp only [add_zero, map_zero, LinearMap.zero_apply] at h0
  have h1 : f 0 = 0 := by
    linear_combination -h0
  have hxx : x + x = 0 := by
    ext i
    simp [CharTwo.add_self_eq_zero]
  have h2 := h x x
  rw [hxx, h1, CharTwo.add_self_eq_zero, zero_add] at h2
  exact h2.symm

theorem IsPolarOf.map_apply (h : IsPolarOf f P) (A : (ι → K) →ₗ[K] (ι → K))
    (hA : ∀ x, f (A x) = f x) (x y : ι → K) : P (A x) (A y) = P x y := by
  have h1 := h (A x) (A y)
  have h2 := h x y
  rw [← map_add, hA, hA, hA] at h1
  exact add_left_cancel (h1.symm.trans h2)

end Generic

section Isometry

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

theorem statedOmega_isometry (f : (ι → K) → K) {A : GL ι K} (hA : A ∈ StatedOmega f)
    (x : ι → K) : f ((A : Matrix ι ι K) *ᵥ x) = f x := by
  let H : Subgroup (GL ι K) :=
    { carrier := {A | ∀ v, f ((A : Matrix ι ι K) *ᵥ v) = f v}
      one_mem' := fun v => by simp
      mul_mem' := fun {a b} ha hb v => by
        change f (((a * b : GL ι K) : Matrix ι ι K) *ᵥ v) = f v
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, ha, hb]
      inv_mem' := fun {a} ha v => by
        have h := ha ((a⁻¹ : GL ι K) *ᵥ v)
        change f (((a⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) = f v
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec] at h
        exact h.symm }
  have hC : Subgroup.closure {A : GL ι K | ∀ v : ι → K, f ((A : Matrix ι ι K) *ᵥ v) = f v} ≤ H :=
    (Subgroup.closure_le H).mpr fun A hA => hA
  have hcomm : ⁅Subgroup.closure {A : GL ι K | ∀ v : ι → K, f ((A : Matrix ι ι K) *ᵥ v) = f v},
      Subgroup.closure {A : GL ι K | ∀ v : ι → K, f ((A : Matrix ι ι K) *ᵥ v) = f v}⁆ ≤ H := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem (hC ha) (hC hb)) (H.inv_mem (hC ha)))
      (H.inv_mem (hC hb))
  exact hcomm hA x

end Isometry

section Plus

variable (m : ℕ) (K : Type) [Field K]

@[expose] def plusPolar : (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K) →ₗ[K] K :=
  LinearMap.mk₂ K
    (fun x y => ∑ i : Fin m, (x (.inl i) * y (.inr i) + x (.inr i) * y (.inl i)))
    (fun x x' y => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply]; ring)
    (fun c x y => by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply]; ring)
    (fun c x y => by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]; ring)

theorem plusPolar_apply (x y : Fin m ⊕ Fin m → K) : plusPolar m K x y =
    ∑ i : Fin m, (x (.inl i) * y (.inr i) + x (.inr i) * y (.inl i)) := rfl

variable {m K}

theorem plusPolar_isPolar [CharP K 2] :
    IsPolarOf (fun v : Fin m ⊕ Fin m → K => ∑ i : Fin m, v (.inl i) * v (.inr i))
      (plusPolar m K) := by
  intro x y
  rw [plusPolar_apply, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply]; ring

theorem plusPolar_nondeg (x : Fin m ⊕ Fin m → K) (h : ∀ y, plusPolar m K x y = 0) : x = 0 := by
  ext j
  rcases j with i | i
  · have := h (Pi.single (.inr i) 1)
    simpa [plusPolar_apply, Pi.single_apply] using this
  · have := h (Pi.single (.inl i) 1)
    simpa [plusPolar_apply, Pi.single_apply] using this

end Plus

section Minus

variable (m : ℕ) (K : Type) [Field K] (b : K)

@[expose] def minusPolar :
    (Fin m ⊕ Fin m ⊕ Fin 2 → K) →ₗ[K] (Fin m ⊕ Fin m ⊕ Fin 2 → K) →ₗ[K] K :=
  LinearMap.mk₂ K
    (fun x y => ∑ i : Fin m, (x (.inl i) * y (.inr (.inl i)) + x (.inr (.inl i)) * y (.inl i)) +
      b * (x (.inr (.inr 0)) * y (.inr (.inr 1)) + x (.inr (.inr 1)) * y (.inr (.inr 0))))
    (fun x x' y => by
      simp only [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]; ring)
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [mul_add c, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by ring
      · ring)
    (fun x y y' => by
      simp only [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]; ring)
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [mul_add c, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by ring
      · ring)

theorem minusPolar_apply (x y : Fin m ⊕ Fin m ⊕ Fin 2 → K) : minusPolar m K b x y =
    ∑ i : Fin m, (x (.inl i) * y (.inr (.inl i)) + x (.inr (.inl i)) * y (.inl i)) +
      b * (x (.inr (.inr 0)) * y (.inr (.inr 1)) + x (.inr (.inr 1)) * y (.inr (.inr 0))) := rfl

variable {m K b}

theorem minusPolar_isPolar [CharP K 2] (c : K) :
    IsPolarOf (fun v : Fin m ⊕ Fin m ⊕ Fin 2 → K =>
      ∑ i : Fin m, v (.inl i) * v (.inr (.inl i)) + v (.inr (.inr 0)) ^ 2 +
        b * v (.inr (.inr 0)) * v (.inr (.inr 1)) + c * v (.inr (.inr 1)) ^ 2)
      (minusPolar m K b) := by
  intro x y
  have hsum : ∑ i : Fin m, (x (.inl i) + y (.inl i)) * (x (.inr (.inl i)) + y (.inr (.inl i))) =
      ∑ i : Fin m, x (.inl i) * x (.inr (.inl i)) + ∑ i : Fin m, y (.inl i) * y (.inr (.inl i)) +
        ∑ i : Fin m, (x (.inl i) * y (.inr (.inl i)) + x (.inr (.inl i)) * y (.inl i)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [minusPolar_apply, Pi.add_apply]
  rw [hsum]
  linear_combination (x (.inr (.inr 0)) * y (.inr (.inr 0)) +
    c * x (.inr (.inr 1)) * y (.inr (.inr 1))) * h2

theorem minusPolar_nondeg (hb : b ≠ 0) (x : Fin m ⊕ Fin m ⊕ Fin 2 → K)
    (h : ∀ y, minusPolar m K b x y = 0) : x = 0 := by
  ext j
  rcases j with i | i | i
  · have := h (Pi.single (.inr (.inl i)) 1)
    simpa [minusPolar_apply, Pi.single_apply] using this
  · have := h (Pi.single (.inl i) 1)
    simpa [minusPolar_apply, Pi.single_apply] using this
  · fin_cases i
    · have := h (Pi.single (.inr (.inr 1)) 1)
      simpa [minusPolar_apply, Pi.single_apply, hb] using this
    · have := h (Pi.single (.inr (.inr 0)) 1)
      simpa [minusPolar_apply, Pi.single_apply, hb] using this

end Minus

end CFSG.RankThree.GF2n.Smith81.Smith23E1
