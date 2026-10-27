module

public import CFSG.RankThree.PartOne.KFR4.Std

public section

namespace CFSG.RankThree.PartOne.KFR4

open QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal CFSG.LieType.Universal.Unitary

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E] {p : ℕ}

@[expose] def Uni (D : EvenNormPlane K E) : Subgroup (GL (Fin 3) E) where
  carrier := {M | conjTr D.σ.toRingEquiv (M : Matrix (Fin 3) (Fin 3) E) *
    (M : Matrix (Fin 3) (Fin 3) E) = 1}
  mul_mem' := by
    rintro A B hA hB
    have hA' : conjTr D.σ.toRingEquiv (A : Matrix (Fin 3) (Fin 3) E) *
      (A : Matrix (Fin 3) (Fin 3) E) = 1 := hA
    have hB' : conjTr D.σ.toRingEquiv (B : Matrix (Fin 3) (Fin 3) E) *
      (B : Matrix (Fin 3) (Fin 3) E) = 1 := hB
    show conjTr D.σ.toRingEquiv ((A * B : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *
      ((A * B : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) = 1
    rw [Units.val_mul, conjTr_mul]
    calc conjTr D.σ.toRingEquiv (B : Matrix (Fin 3) (Fin 3) E) *
        conjTr D.σ.toRingEquiv (A : Matrix (Fin 3) (Fin 3) E) *
        ((A : Matrix (Fin 3) (Fin 3) E) * (B : Matrix (Fin 3) (Fin 3) E))
        = conjTr D.σ.toRingEquiv (B : Matrix (Fin 3) (Fin 3) E) *
          (conjTr D.σ.toRingEquiv (A : Matrix (Fin 3) (Fin 3) E) *
            (A : Matrix (Fin 3) (Fin 3) E)) * (B : Matrix (Fin 3) (Fin 3) E) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hA', Matrix.mul_one, hB']
  one_mem' := by
    show conjTr D.σ.toRingEquiv ((1 : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *
      ((1 : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) = 1
    simp [conjTr_one]
  inv_mem' := by
    rintro A hA
    have hA' : conjTr D.σ.toRingEquiv (A : Matrix (Fin 3) (Fin 3) E) *
      (A : Matrix (Fin 3) (Fin 3) E) = 1 := hA
    have hAB : (A : Matrix (Fin 3) (Fin 3) E) * ((A⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E)
        = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    show conjTr D.σ.toRingEquiv ((A⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *
      ((A⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) = 1
    have key : conjTr D.σ.toRingEquiv ((A⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *
        (conjTr D.σ.toRingEquiv (A : Matrix (Fin 3) (Fin 3) E) *
          (A : Matrix (Fin 3) (Fin 3) E)) *
        ((A⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) =
        conjTr D.σ.toRingEquiv ((A : Matrix (Fin 3) (Fin 3) E) *
          ((A⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E)) *
        ((A : Matrix (Fin 3) (Fin 3) E) *
          ((A⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E)) := by
      rw [conjTr_mul]
      simp only [Matrix.mul_assoc]
    rw [hA', Matrix.mul_one, hAB, conjTr_one, Matrix.one_mul] at key
    exact key

@[expose] def UniBdP (D : EvenNormPlane K E) (A : AddSubgroup (Fin 3 → ZMod p))
    (M : GL (Fin 3) E) : Prop :=
  M ∈ Uni D ∧
    (∀ i, (∀ a ∈ A, a i = 0) →
      (M : Matrix (Fin 3) (Fin 3) E).mulVec (Pi.single i 1) = Pi.single i 1) ∧
    ∀ i j, (∃ a ∈ A, a i ≠ a j) → (M : Matrix (Fin 3) (Fin 3) E) j i = 0

@[expose] def coords (S : StdData K E p) (R : Subgroup (Vs K E ≃ₗ[K] Vs K E)) :
    AddSubgroup (Fin 3 → ZMod p) where
  carrier := {a | tor S a ∈ R}
  add_mem' := by
    intro a b ha hb
    show tor S (a + b) ∈ R
    rw [tor_add]
    exact mul_mem ha hb
  zero_mem' := by
    show tor S 0 ∈ R
    rw [tor_zero]
    exact one_mem R
  neg_mem' := by
    intro a ha
    show tor S (-a) ∈ R
    have : tor S (-a) = (tor S a)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← tor_add, neg_add_cancel, tor_zero]
    rw [this]
    exact inv_mem ha

theorem mem_coords {S : StdData K E p} {R : Subgroup (Vs K E ≃ₗ[K] Vs K E)}
    {a : Fin 3 → ZMod p} : a ∈ coords S R ↔ tor S a ∈ R := Iff.rfl

@[expose] def vanishes (A : AddSubgroup (Fin 3 → ZMod p)) (ρ : Root) : Prop :=
  ∀ a ∈ A, ρ.vecp p ⬝ᵥ a = 0

open _root_.Classical in
@[expose] noncomputable def fixedSet (A : AddSubgroup (Fin 3 → ZMod p)) : Finset (Fin 3) :=
  Finset.univ.filter fun i => ∀ a ∈ A, a i = 0

theorem mem_fixedSet {A : AddSubgroup (Fin 3 → ZMod p)} {i : Fin 3} :
    i ∈ fixedSet A ↔ ∀ a ∈ A, a i = 0 := by
  classical
  simp [fixedSet]

@[expose] def Coherent (A : AddSubgroup (Fin 3 → ZMod p)) : Prop :=
  ∀ i j : Fin 3, (∀ a ∈ A, a i = - a j) → ∀ a ∈ A, a i = 0

@[expose] def flipVec (k : Fin 3) (a : Fin 3 → ZMod p) : Fin 3 → ZMod p :=
  Function.update a k (-(a k))

@[expose] def Root.flip (k : Fin 3) : Root → Root
  | .s1 => .s1
  | .s2 => .s2
  | .s3 => .s3
  | .m12 => if k = 2 then .m12 else .p12
  | .p12 => if k = 2 then .p12 else .m12
  | .m13 => if k = 1 then .m13 else .p13
  | .p13 => if k = 1 then .p13 else .m13
  | .m23 => if k = 0 then .m23 else .p23
  | .p23 => if k = 0 then .p23 else .m23

theorem conjCoord_apply (D : EvenNormPlane K E) (k : Fin 3) (v : Vs K E) :
    conjCoord D k v = ((fun j => if j = k then D.σ (v.1 j) else v.1 j), v.2) := rfl

theorem conjCoord_inv (D : EvenNormPlane K E) (k : Fin 3) :
    (conjCoord D k)⁻¹ = conjCoord D k := by
  rw [inv_eq_iff_mul_eq_one]
  refine LinearEquiv.ext fun v => Prod.ext (funext fun j => ?_) rfl
  by_cases h : j = k <;> simp [conjCoord_apply, h, D.sigma_sigma]

theorem conj_tor (S : StdData K E p) (k : Fin 3) (a : Fin 3 → ZMod p) :
    conjCoord S.D k * tor S a * (conjCoord S.D k)⁻¹ = tor S (flipVec k a) := by
  rw [conjCoord_inv]
  refine LinearEquiv.ext fun v => Prod.ext (funext fun j => ?_) rfl
  by_cases h : j = k
  · subst h
    simp [conjCoord_apply, tor_apply, flipVec, S.sigma_rot, S.D.sigma_sigma]
  · simp [conjCoord_apply, tor_apply, flipVec, h]

end CFSG.RankThree.PartOne.KFR4
