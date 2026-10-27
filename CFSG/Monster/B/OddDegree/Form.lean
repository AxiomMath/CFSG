module

public import CFSG.Monster.B.Gen.MinkowskiTwo
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Data.Int.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Monster.B.OddDegree

open Matrix

section Integral

variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

@[expose] def avgForm (A : G →* GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  ∑ g, ((A g : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ)ᵀ * (A g : Matrix (Fin n) (Fin n) ℤ)

theorem avgForm_transpose (A : G →* GL (Fin n) ℤ) : (avgForm A)ᵀ = avgForm A := by
  rw [avgForm, Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

theorem avgForm_invariant (A : G →* GL (Fin n) ℤ) (h : G) :
    ((A h : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ)ᵀ * avgForm A * (A h) = avgForm A := by
  rw [avgForm, Finset.mul_sum, Finset.sum_mul]
  refine (Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g => ?_).trans rfl
  rw [Equiv.coe_mulRight, map_mul, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc,
    Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (A h : Matrix (Fin n) (Fin n) ℤ)]
  simp only [Matrix.mul_assoc]

theorem avgForm_diag_pos (A : G →* GL (Fin n) ℤ) (i : Fin n) : 0 < avgForm A i i := by
  rw [avgForm, Matrix.sum_apply]
  have hterm : ∀ g, 0 ≤ (((A g : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ)ᵀ *
      (A g : Matrix (Fin n) (Fin n) ℤ)) i i := by
    intro g
    rw [Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => by rw [Matrix.transpose_apply]; exact mul_self_nonneg _
  have h1 : (((A 1 : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ)ᵀ *
      (A 1 : Matrix (Fin n) (Fin n) ℤ)) i i = 1 := by
    rw [map_one, Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.one_apply_eq]
  calc (0 : ℤ) < 1 := one_pos
    _ = _ := h1.symm
    _ ≤ _ := Finset.single_le_sum (fun g _ => hterm g) (Finset.mem_univ 1)

theorem avgForm_ne_zero (A : G →* GL (Fin n) ℤ) (hn : 0 < n) : avgForm A ≠ 0 := by
  intro h
  have := avgForm_diag_pos A ⟨0, hn⟩
  rw [h, Matrix.zero_apply] at this
  exact lt_irrefl 0 this

theorem exists_primitive_invariant_form (A : G →* GL (Fin n) ℤ) (hn : 0 < n) :
    ∃ M' : Matrix (Fin n) (Fin n) ℤ, M'ᵀ = M' ∧
      (∀ h, ((A h : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ)ᵀ * M' * (A h) = M') ∧
      M'.map (Int.castRingHom (ZMod 2)) ≠ 0 := by
  classical
  have hex : ∃ k, ¬ DivTwoPow k (avgForm A) := by
    by_contra h
    push Not at h
    exact avgForm_ne_zero A hn (eq_zero_of_forall_divTwoPow h)
  obtain ⟨k, hk, hkmin⟩ : ∃ k, ¬ DivTwoPow k (avgForm A) ∧ ∀ j < k, DivTwoPow j (avgForm A) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => by
      by_contra h
      exact Nat.find_min hex hj h⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hk ⟨avgForm A, by rw [pow_zero, one_smul]⟩
  obtain ⟨M', hM'⟩ : DivTwoPow (k - 1) (avgForm A) := hkmin _ (by omega)
  have hinj : Function.Injective fun X : Matrix (Fin n) (Fin n) ℤ => (2 ^ (k - 1) : ℤ) • X :=
    smul_right_injective _ (pow_ne_zero _ two_ne_zero)
  refine ⟨M', ?_, fun h => ?_, fun h0 => ?_⟩
  · apply hinj
    show (2 ^ (k - 1) : ℤ) • M'ᵀ = (2 ^ (k - 1) : ℤ) • M'
    rw [← Matrix.transpose_smul, ← hM', avgForm_transpose]
  · apply hinj
    show (2 ^ (k - 1) : ℤ) • (((A h : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ)ᵀ * M' * (A h)) =
      (2 ^ (k - 1) : ℤ) • M'
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← hM', avgForm_invariant]
  ·
    apply hk
    refine ⟨Matrix.of fun i j => M' i j / 2, ?_⟩
    ext i j
    have hij := congrFun (congrFun h0 i) j
    rw [Matrix.map_apply, Matrix.zero_apply, eq_intCast,
      ZMod.intCast_zmod_eq_zero_iff_dvd] at hij
    have hdvd : (2 : ℤ) ∣ M' i j := by exact_mod_cast hij
    obtain ⟨c, hc⟩ := hdvd
    have hij' : avgForm A i j = (2 ^ (k - 1) : ℤ) * M' i j := by
      rw [hM', Matrix.smul_apply, smul_eq_mul]
    rw [hij', Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, hc,
      Int.mul_ediv_cancel_left c two_ne_zero, ← mul_assoc, ← pow_succ,
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hk0)]

end Integral

@[expose] def skewLift {n : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => if i < j then ((B i j).val : ℤ) else if j < i then -((B j i).val : ℤ) else 0

theorem skewLift_transpose {n : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2)) :
    (skewLift B)ᵀ = -skewLift B := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [skewLift, h, not_lt.2 h.le]
  · simp [skewLift]
  · simp [skewLift, h, not_lt.2 h.le]

theorem map_skewLift {n : ℕ} {B : Matrix (Fin n) (Fin n) (ZMod 2)} (hB : Bᵀ = B)
    (hdiag : ∀ i, B i i = 0) : (skewLift B).map (Int.castRingHom (ZMod 2)) = B := by
  ext i j
  have hsym : B j i = B i j := by rw [← Matrix.transpose_apply B i j, hB]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [skewLift, h]
  · simp [skewLift, hdiag]
  · simp [skewLift, h, not_lt.2 h.le, hsym]

theorem det_eq_zero_of_alternating {n : ℕ} (hn : Odd n) {B : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hB : Bᵀ = B) (hdiag : ∀ i, B i i = 0) : B.det = 0 := by
  have hS : (skewLift B).det = 0 := by
    have h := congrArg Matrix.det (skewLift_transpose B)
    rw [Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin, hn.neg_one_pow, neg_one_mul] at h
    omega
  have h := RingHom.map_det (Int.castRingHom (ZMod 2)) (skewLift B)
  rw [hS, map_zero] at h
  rw [← map_skewLift hB hdiag]
  exact h.symm

section Reducible

variable {G : Type*} [Group G] {n : ℕ}

@[expose] def quadForm (B : Matrix (Fin n) (Fin n) (ZMod 2)) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun v := ∑ i, B i i * v i
  map_add' u v := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem zmod_two_sq (c : ZMod 2) : c * c = c := by fin_cases c <;> rfl

theorem zmod_two_add_self' (c : ZMod 2) : c + c = 0 := by fin_cases c <;> rfl

theorem dotProduct_mulVec_add {B : Matrix (Fin n) (Fin n) (ZMod 2)} (hB : Bᵀ = B)
    (u v : Fin n → ZMod 2) :
    (u + v) ⬝ᵥ (B *ᵥ (u + v)) = u ⬝ᵥ (B *ᵥ u) + v ⬝ᵥ (B *ᵥ v) := by
  have hcross : v ⬝ᵥ (B *ᵥ u) = u ⬝ᵥ (B *ᵥ v) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hB, dotProduct_comm]
  rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hcross]
  have h2 : u ⬝ᵥ (B *ᵥ v) + u ⬝ᵥ (B *ᵥ v) = 0 := zmod_two_add_self' _
  linear_combination h2

theorem dotProduct_mulVec_self {B : Matrix (Fin n) (Fin n) (ZMod 2)} (hB : Bᵀ = B)
    (v : Fin n → ZMod 2) : v ⬝ᵥ (B *ᵥ v) = quadForm B v := by
  let F : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun v => v ⬝ᵥ (B *ᵥ v)
      map_add' := dotProduct_mulVec_add hB
      map_smul' := fun c v => by
        simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
          RingHom.id_apply, ← mul_assoc, zmod_two_sq] }
  have hF : F = quadForm B := by
    refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
    simp only [F, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      LinearMap.coe_single, quadForm]
    rw [Matrix.mulVec_single_one, single_dotProduct, one_mul,
      Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
        (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, mul_one]
    rfl
  exact congrFun (congrArg DFunLike.coe hF) v

theorem dotProduct_mulVec_conj (P B : Matrix (Fin n) (Fin n) (ZMod 2)) (v : Fin n → ZMod 2) :
    (P *ᵥ v) ⬝ᵥ (B *ᵥ (P *ᵥ v)) = v ⬝ᵥ ((Pᵀ * B * P) *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem exists_invariant_of_form (σ : G →* GL (Fin n) (ZMod 2)) (hn : Odd n) (hn2 : 2 ≤ n)
    (B : Matrix (Fin n) (Fin n) (ZMod 2)) (hB : Bᵀ = B) (hB0 : B ≠ 0)
    (hinv : ∀ g, ((σ g : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ * B * (σ g) = B) :
    ∃ X : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ g, ∀ v ∈ X, ((σ g : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v ∈ X) ∧
      X ≠ ⊥ ∧ X ≠ ⊤ := by
  classical
  by_cases hdiag : ∀ i, B i i = 0
  ·
    refine ⟨LinearMap.ker (Matrix.mulVecLin B), fun g v hv => ?_, ?_, ?_⟩
    · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
      have h := hinv g
      have hg : B * (σ g : Matrix (Fin n) (Fin n) (ZMod 2)) =
          ((σ g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ * B := by
        calc B * (σ g : Matrix (Fin n) (Fin n) (ZMod 2))
            = ((σ g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *
                ((σ g : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ * B *
                  (σ g) := by
              rw [← Matrix.transpose_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
                Units.val_one, Matrix.transpose_one, Matrix.one_mul]
          _ = _ := by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ B, h]
      rw [Matrix.mulVec_mulVec, hg, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
    · obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 (det_eq_zero_of_alternating hn hB hdiag)
      intro hbot
      apply hv0
      have : v ∈ LinearMap.ker (Matrix.mulVecLin B) := by
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hv
      rw [hbot] at this
      exact (Submodule.mem_bot _).1 this
    · intro htop
      apply hB0
      ext i j
      have : (Pi.single j 1 : Fin n → ZMod 2) ∈ LinearMap.ker (Matrix.mulVecLin B) := by
        rw [htop]; exact Submodule.mem_top
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at this
      exact congrFun this i
  ·
    push Not at hdiag
    obtain ⟨i, hi⟩ := hdiag
    refine ⟨LinearMap.ker (quadForm B), fun g v hv => ?_, ?_, ?_⟩
    · rw [LinearMap.mem_ker] at hv ⊢
      rw [← dotProduct_mulVec_self hB, dotProduct_mulVec_conj, hinv g, dotProduct_mulVec_self hB,
        hv]
    ·
      intro hbot
      have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := fun h => by
        simpa using congrArg Fin.val h
      set e0 : Fin n → ZMod 2 := Pi.single ⟨0, by omega⟩ 1
      set e1 : Fin n → ZMod 2 := Pi.single ⟨1, by omega⟩ 1
      have hne : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
      have hmem : ∀ w, quadForm B w = 0 → w = 0 := fun w hw => by
        have : w ∈ LinearMap.ker (quadForm B) := hw
        rw [hbot] at this
        exact (Submodule.mem_bot _).1 this
      by_cases h0 : quadForm B e0 = 0
      · have := congrFun (hmem e0 h0) ⟨0, by omega⟩
        simp [e0] at this
      · by_cases h1 : quadForm B e1 = 0
        · have := congrFun (hmem e1 h1) ⟨1, by omega⟩
          simp [e1] at this
        · have hsum : quadForm B (e0 + e1) = 0 := by
            rw [map_add, hne _ h0, hne _ h1]
            rfl
          have := congrFun (hmem _ hsum) ⟨0, by omega⟩
          simp [e0, e1, h01] at this
    · intro htop
      have : (Pi.single i 1 : Fin n → ZMod 2) ∈ LinearMap.ker (quadForm B) := by
        rw [htop]; exact Submodule.mem_top
      rw [LinearMap.mem_ker] at this
      apply hi
      rw [← this]
      change B i i = ∑ j, B j j * (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) j
      rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
        (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, mul_one]

end Reducible

end CFSG.Monster.B.OddDegree
