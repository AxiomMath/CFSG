module

public import Certificates.Certificate733012
public import CFSG.Quasithin.Recognition.St84.G24Vertex1Frame
public import CFSG.Quasithin.Recognition.St84.G24Vertex2Frame

public section

namespace CFSG.Quasithin.F112R.St84.G24M

open Certificates.A5GL42 (aN bN aO bO)
open CFSG.Quasithin.H.Q13 (om)
open CFSG.GroupTheory (quadMapOfCoeffs)
open scoped Matrix

theorem matV1_zero : CFSG.Quasithin.St84.G24MF.matV1 0 = v1Diag aO := by decide

theorem matV1_one : CFSG.Quasithin.St84.G24MF.matV1 1 = v1Diag bO := by decide

theorem matV1_two : CFSG.Quasithin.St84.G24MF.matV1 2 = v1Omega := by decide

theorem matZ1_zero : CFSG.Quasithin.St84.G24MF.matZ1 0 = 1 := by decide

theorem matZ1_one : CFSG.Quasithin.St84.G24MF.matZ1 1 = 1 := by decide

theorem matZ1_two : CFSG.Quasithin.St84.G24MF.matZ1 2 = om := by decide

theorem matV2_zero : CFSG.Quasithin.St84.G24MF.matV2 0 =
    v2Block 1 (CFSG.Quasithin.St84.G24LE.nonsplitX 0) aN := by decide

theorem matV2_one : CFSG.Quasithin.St84.G24MF.matV2 1 =
    v2Block 1 (CFSG.Quasithin.St84.G24LE.nonsplitX 1) bN := by decide

theorem matV2_two : CFSG.Quasithin.St84.G24MF.matV2 2 =
    v2Block om (CFSG.Quasithin.St84.G24LE.nonsplitX 2) CFSG.Quasithin.St84.G24LE.omegaN := by
  decide

theorem matZ2_zero : CFSG.Quasithin.St84.G24MF.matZ2 0 = aN := by decide

theorem matZ2_one : CFSG.Quasithin.St84.G24MF.matZ2 1 = bN := by decide

theorem matZ2_two : CFSG.Quasithin.St84.G24MF.matZ2 2 = 1 := by decide

theorem om_pow_three : om ^ 3 = 1 := by decide

theorem omegaN_pow_three : CFSG.Quasithin.St84.G24LE.omegaN ^ 3 = 1 := by decide

private theorem shiftX_mul_left (A : Matrix (Fin 2) (Fin 2) (ZMod 2))
    (m : Matrix (Fin 2) (Fin 4) (ZMod 2)) (t : Fin 3) (hA : A * om = om * A) :
    CFSG.Quasithin.St84.G24LE.shiftX (A * m) t =
      A * CFSG.Quasithin.St84.G24LE.shiftX m t := by
  fin_cases t
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.Quasithin.St84.G24LE.shiftX, Matrix.mul_add, Matrix.mul_assoc]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.Quasithin.St84.G24LE.shiftX, Matrix.mul_add, Matrix.mul_assoc]
  · change (A * m) * CFSG.Quasithin.St84.G24LE.omegaN + om * (A * m) =
      A * (m * CFSG.Quasithin.St84.G24LE.omegaN + om * m)
    rw [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc A om m, hA]

theorem ext2_normalize (r : ℕ) (m : Matrix (Fin 2) (Fin 4) (ZMod 2)) (t : Fin 3) :
    om ^ (2 * r) * (CFSG.Quasithin.St84.G24LE.shiftX m t +
        om ^ r * CFSG.Quasithin.St84.G24LE.nonsplitX t) +
      CFSG.Quasithin.St84.G24LE.shiftX (om ^ (2 * r) * m) t =
    CFSG.Quasithin.St84.G24LE.nonsplitX t := by
  have hcomm : om ^ (2 * r) * om = om * om ^ (2 * r) := by
    rw [← pow_succ, ← pow_succ']
  rw [shiftX_mul_left (om ^ (2 * r)) m t hcomm]
  have hAB : om ^ (2 * r) * om ^ r = 1 := by
    rw [← pow_add, show 2 * r + r = 3 * r by omega, pow_mul, om_pow_three, one_pow]
  have hself : om ^ (2 * r) * CFSG.Quasithin.St84.G24LE.shiftX m t +
      om ^ (2 * r) * CFSG.Quasithin.St84.G24LE.shiftX m t = 0 := by
    ext i j
    exact CharTwo.add_self_eq_zero (R := ZMod 2) _
  rw [Matrix.mul_add, ← Matrix.mul_assoc, hAB]
  simp
  rw [add_assoc,
    add_comm (CFSG.Quasithin.St84.G24LE.nonsplitX t)
      (om ^ (2 * r) * CFSG.Quasithin.St84.G24LE.shiftX m t),
    ← add_assoc, hself, zero_add]

private theorem quad1Check_of_certificate
    (h : CFSG.Quasithin.St84.G24LE.linEqCheck () = true) :
    CFSG.Quasithin.St84.G24LE.quad1Check () = true := by
  unfold CFSG.Quasithin.St84.G24LE.linEqCheck at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

private theorem quad2Check_of_certificate
    (h : CFSG.Quasithin.St84.G24LE.linEqCheck () = true) :
    CFSG.Quasithin.St84.G24LE.quad2Check () = true := by
  unfold CFSG.Quasithin.St84.G24LE.linEqCheck at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

private theorem commCheck_of_certificate
    (h : CFSG.Quasithin.St84.G24LE.linEqCheck () = true) :
    CFSG.Quasithin.St84.G24LE.commCheck () = true := by
  unfold CFSG.Quasithin.St84.G24LE.linEqCheck at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

private theorem ext2Check_of_certificate
    (h : CFSG.Quasithin.St84.G24LE.linEqCheck () = true) :
    CFSG.Quasithin.St84.G24LE.ext2Check () = true := by
  unfold CFSG.Quasithin.St84.G24LE.linEqCheck at h
  simp only [Bool.and_eq_true] at h
  exact h.2

private theorem spanOK_spec {R C K : Type*} [Fintype R] [DecidableEq R] [Fintype C]
    [DecidableEq C] [Fintype K] [DecidableEq K]
    {m t : Matrix R C (ZMod 2)} {k : Matrix C K (ZMod 2)}
    {p : Matrix K C (ZMod 2)} {y : Matrix C R (ZMod 2)}
    (h : CFSG.Quasithin.St84.G24LE.spanOK m t k p y = true) (x : C → ZMod 2)
    (hx : m *ᵥ x = 0) : x = k *ᵥ (p *ᵥ x) := by
  unfold CFSG.Quasithin.St84.G24LE.spanOK at h
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  obtain ⟨ht, hkp⟩ := h
  rw [ht] at hkp
  have h1 : (k * p + y * m) *ᵥ x = x := by
    rw [hkp, Matrix.one_mulVec]
  rw [Matrix.add_mulVec] at h1
  rw [← Matrix.mulVec_mulVec (M := k) (N := p)] at h1
  rw [← Matrix.mulVec_mulVec (M := y) (N := m)] at h1
  rw [hx, Matrix.mulVec_zero, add_zero] at h1
  exact h1.symm

private def quadDefectLinear {n d : ℕ} (R : Fin 3 → Matrix (Fin n) (Fin n) (ZMod 2))
    (S : Fin 3 → Matrix (Fin d) (Fin d) (ZMod 2)) :
    (CFSG.Quasithin.St84.G24LE.Mono n × Fin d → ZMod 2) →ₗ[ZMod 2]
      (Fin 3 × CFSG.Quasithin.St84.G24LE.Mono n × Fin d → ZMod 2) where
  toFun x r := CFSG.Quasithin.St84.G24LE.quadDefect R S x r
  map_add' x y := by
    funext r
    have hsq : CFSG.Quasithin.St84.G24LE.sqOf (x + y) =
        CFSG.Quasithin.St84.G24LE.sqOf x + CFSG.Quasithin.St84.G24LE.sqOf y := rfl
    have hcm : CFSG.Quasithin.St84.G24LE.cmOf (x + y) =
        CFSG.Quasithin.St84.G24LE.cmOf x + CFSG.Quasithin.St84.G24LE.cmOf y := by
      funext i j t
      by_cases h : i < j <;> simp [CFSG.Quasithin.St84.G24LE.cmOf, h]
    change (quadMapOfCoeffs (CFSG.Quasithin.St84.G24LE.sqOf (x + y))
        (CFSG.Quasithin.St84.G24LE.cmOf (x + y))
          (R r.1 *ᵥ CFSG.Quasithin.St84.G24LE.testVec r.2.1) +
      S r.1 *ᵥ quadMapOfCoeffs (CFSG.Quasithin.St84.G24LE.sqOf (x + y))
        (CFSG.Quasithin.St84.G24LE.cmOf (x + y)) (CFSG.Quasithin.St84.G24LE.testVec r.2.1)) r.2.2 =
      (quadMapOfCoeffs (CFSG.Quasithin.St84.G24LE.sqOf x) (CFSG.Quasithin.St84.G24LE.cmOf x)
          (R r.1 *ᵥ CFSG.Quasithin.St84.G24LE.testVec r.2.1) +
        S r.1 *ᵥ quadMapOfCoeffs (CFSG.Quasithin.St84.G24LE.sqOf x)
          (CFSG.Quasithin.St84.G24LE.cmOf x) (CFSG.Quasithin.St84.G24LE.testVec r.2.1)) r.2.2 +
      (quadMapOfCoeffs (CFSG.Quasithin.St84.G24LE.sqOf y) (CFSG.Quasithin.St84.G24LE.cmOf y)
          (R r.1 *ᵥ CFSG.Quasithin.St84.G24LE.testVec r.2.1) +
        S r.1 *ᵥ quadMapOfCoeffs (CFSG.Quasithin.St84.G24LE.sqOf y)
          (CFSG.Quasithin.St84.G24LE.cmOf y) (CFSG.Quasithin.St84.G24LE.testVec r.2.1)) r.2.2
    rw [hsq, hcm]
    simp only [CFSG.GroupTheory.quadMapOfCoeffs_add, Matrix.mulVec_add, Pi.add_apply]
    abel
  map_smul' a x := by
    funext r
    have hsq : CFSG.Quasithin.St84.G24LE.sqOf (a • x) =
        a • CFSG.Quasithin.St84.G24LE.sqOf x := rfl
    have hcm : CFSG.Quasithin.St84.G24LE.cmOf (a • x) =
        a • CFSG.Quasithin.St84.G24LE.cmOf x := by
      funext i j t
      by_cases h : i < j <;> simp [CFSG.Quasithin.St84.G24LE.cmOf, h]
    change (quadMapOfCoeffs (CFSG.Quasithin.St84.G24LE.sqOf (a • x))
        (CFSG.Quasithin.St84.G24LE.cmOf (a • x))
          (R r.1 *ᵥ CFSG.Quasithin.St84.G24LE.testVec r.2.1) +
      S r.1 *ᵥ quadMapOfCoeffs (CFSG.Quasithin.St84.G24LE.sqOf (a • x))
        (CFSG.Quasithin.St84.G24LE.cmOf (a • x)) (CFSG.Quasithin.St84.G24LE.testVec r.2.1)) r.2.2 =
      (a • (quadMapOfCoeffs (CFSG.Quasithin.St84.G24LE.sqOf x)
          (CFSG.Quasithin.St84.G24LE.cmOf x) (R r.1 *ᵥ CFSG.Quasithin.St84.G24LE.testVec r.2.1) +
        S r.1 *ᵥ quadMapOfCoeffs (CFSG.Quasithin.St84.G24LE.sqOf x)
          (CFSG.Quasithin.St84.G24LE.cmOf x) (CFSG.Quasithin.St84.G24LE.testVec r.2.1))) r.2.2
    rw [hsq, hcm]
    simp only [CFSG.GroupTheory.quadMapOfCoeffs_smul, Matrix.mulVec_smul,
      Pi.smul_apply, smul_add]
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc,
      mul_left_comm, mul_comm]
    rw [mul_add, Finset.mul_sum]

private theorem quadM_mulVec {n d : ℕ} (R : Fin 3 → Matrix (Fin n) (Fin n) (ZMod 2))
    (S : Fin 3 → Matrix (Fin d) (Fin d) (ZMod 2))
    (x : CFSG.Quasithin.St84.G24LE.Mono n × Fin d → ZMod 2) :
    CFSG.Quasithin.St84.G24LE.quadM R S *ᵥ x = fun r =>
      CFSG.Quasithin.St84.G24LE.quadDefect R S x r := by
  have hmat : LinearMap.toMatrix' (quadDefectLinear R S) =
      CFSG.Quasithin.St84.G24LE.quadM R S := by
    ext r u
    rw [LinearMap.toMatrix'_apply]
    exact (CFSG.Quasithin.St84.G24LE.quadM_apply R S r u).symm
  rw [← hmat, LinearMap.toMatrix'_mulVec]
  rfl

private theorem quadK_mulVec_inl {n d : ℕ} {sq : Fin n → Fin d → ZMod 2}
    {cm : Fin n → Fin n → Fin d → ZMod 2} {W : Matrix (Fin d) (Fin d) (ZMod 2)}
    (c : Fin 2 → ZMod 2) (i : Fin n) (t : Fin d) :
    (CFSG.Quasithin.St84.G24LE.quadK sq cm W *ᵥ c) (Sum.inl i, t) =
      c 0 * sq i t + c 1 * (W *ᵥ sq i) t := by
  simp [CFSG.Quasithin.St84.G24LE.quadK, CFSG.Quasithin.St84.G24LE.coeffVec,
    Matrix.mulVec, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc]

private theorem quadK_mulVec_inr {n d : ℕ} {sq : Fin n → Fin d → ZMod 2}
    {cm : Fin n → Fin n → Fin d → ZMod 2} {W : Matrix (Fin d) (Fin d) (ZMod 2)}
    (c : Fin 2 → ZMod 2) (i j : Fin n) (hij : i < j) (t : Fin d) :
    (CFSG.Quasithin.St84.G24LE.quadK sq cm W *ᵥ c) (Sum.inr ⟨(i, j), hij⟩, t) =
      c 0 * cm i j t + c 1 * (W *ᵥ cm i j) t := by
  simp [CFSG.Quasithin.St84.G24LE.quadK, CFSG.Quasithin.St84.G24LE.coeffVec,
    Matrix.mulVec, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc]

private theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

private def commA : Fin 2 → Matrix (Fin 4) (Fin 4) (ZMod 2) := ![aN, bN]

private theorem commM_mulVec (X : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    CFSG.Quasithin.St84.G24LE.commM *ᵥ (fun u : Fin 4 × Fin 4 => X u.1 u.2) =
      fun r : Fin 2 × Fin 4 × Fin 4 => (X * commA r.1 + commA r.1 * X) r.2.1 r.2.2 := by
  ext r
  rw [Matrix.mulVec, dotProduct, ← Finset.univ_product_univ, Finset.sum_product]
  have hentry : ∀ p q : Fin 4, CFSG.Quasithin.St84.G24LE.commM r (p, q) =
      (if p = r.2.1 then commA r.1 q r.2.2 else 0) +
        (if q = r.2.2 then commA r.1 r.2.1 p else 0) := by
    intro p q
    by_cases hp : p = r.2.1
    · subst hp
      by_cases hq : q = r.2.2
      · subst hq
        simp [CFSG.Quasithin.St84.G24LE.commM, commA, Matrix.single,
          Matrix.mul_apply, Finset.sum_ite_eq]
      · simp [CFSG.Quasithin.St84.G24LE.commM, commA, Matrix.single,
          Matrix.mul_apply, hq, Finset.sum_ite_eq]
    · by_cases hq : q = r.2.2
      · subst hq
        simp [CFSG.Quasithin.St84.G24LE.commM, commA, Matrix.single,
          Matrix.mul_apply, hp, Finset.sum_ite_eq]
      · simp [CFSG.Quasithin.St84.G24LE.commM, commA, Matrix.single,
          Matrix.mul_apply, hp, hq]
  simp only [hentry, add_mul, Finset.sum_add_distrib]
  have h1 : (∑ p, ∑ q, (if p = r.2.1 then commA r.1 q r.2.2 else 0) * X p q) =
      ∑ q, commA r.1 q r.2.2 * X r.2.1 q := by
    rw [Finset.sum_eq_single r.2.1]
    · simp
    · intro p _ hp
      simp [hp]
    · simp
  have h2 : (∑ p, ∑ q, (if q = r.2.2 then commA r.1 r.2.1 p else 0) * X p q) =
      ∑ p, commA r.1 r.2.1 p * X p r.2.2 := by
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_eq_single r.2.2]
    · simp
    · intro q _ hq
      simp [hq]
    · simp
  rw [h1, h2, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  rw [mul_comm]

private theorem commK_mulVec (c : Fin 2 → ZMod 2) (i j : Fin 4) :
    (CFSG.Quasithin.St84.G24LE.commK *ᵥ c) (i, j) =
      c 0 * (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) i j +
        c 1 * CFSG.Quasithin.St84.G24LE.omegaN i j := by
  simp [CFSG.Quasithin.St84.G24LE.commK, Matrix.mulVec, Fin.sum_univ_two,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

private theorem omegaN_sq : CFSG.Quasithin.St84.G24LE.omegaN ^ 2 =
    (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) + CFSG.Quasithin.St84.G24LE.omegaN := by
  decide

theorem lin_eq_check : CFSG.Quasithin.St84.G24LE.linEqCheck () = true :=
  Certificates.certificate733012

section


theorem quad1_proportional {sq : Fin 8 → Fin 2 → ZMod 2}
    {cm : Fin 8 → Fin 8 → Fin 2 → ZMod 2}
    (ha : ∀ v, quadMapOfCoeffs sq cm (v1Diag aO *ᵥ v) = quadMapOfCoeffs sq cm v)
    (hb : ∀ v, quadMapOfCoeffs sq cm (v1Diag bO *ᵥ v) = quadMapOfCoeffs sq cm v)
    (hk : ∀ v, quadMapOfCoeffs sq cm (v1Omega *ᵥ v) = om *ᵥ quadMapOfCoeffs sq cm v)
    (hne : ∃ i j, i < j ∧ cm i j ≠ 0) :
    ∃ s < 3, ∀ v, quadMapOfCoeffs sq cm v = om ^ s *ᵥ
      quadMapOfCoeffs CFSG.Quasithin.St84.G24MF.sqV1 CFSG.Quasithin.St84.G24MF.cmV1 v := by
  let x : CFSG.Quasithin.St84.G24LE.Mono 8 × Fin 2 → ZMod 2 :=
    CFSG.Quasithin.St84.G24LE.coeffVec sq cm
  have hsq : CFSG.Quasithin.St84.G24LE.sqOf x = sq := rfl
  have hcm : ∀ i j, i < j → CFSG.Quasithin.St84.G24LE.cmOf x i j = cm i j := by
    intro i j h
    funext t
    simp [x, CFSG.Quasithin.St84.G24LE.coeffVec,
      CFSG.Quasithin.St84.G24LE.cmOf, h]
  have hcmq : quadMapOfCoeffs sq (CFSG.Quasithin.St84.G24LE.cmOf x) =
      quadMapOfCoeffs sq cm := by
    funext v
    exact CFSG.GroupTheory.quadMapOfCoeffs_congr hcm v
  have hM : CFSG.Quasithin.St84.G24LE.quadM CFSG.Quasithin.St84.G24MF.matV1
      CFSG.Quasithin.St84.G24MF.matZ1 *ᵥ x = 0 := by
    rw [quadM_mulVec]
    funext r
    obtain ⟨g, μ, t⟩ := r
    fin_cases g
    · simp only [Fin.reduceFinMk, Pi.zero_apply, CFSG.Quasithin.St84.G24LE.quadDefect]
      rw [hsq, hcmq, matV1_zero, matZ1_zero, ha, Matrix.one_mulVec, Pi.add_apply]
      exact CharTwo.add_self_eq_zero (R := ZMod 2) _
    · simp only [Fin.reduceFinMk, Pi.zero_apply, CFSG.Quasithin.St84.G24LE.quadDefect]
      rw [hsq, hcmq, matV1_one, matZ1_one, hb, Matrix.one_mulVec, Pi.add_apply]
      exact CharTwo.add_self_eq_zero (R := ZMod 2) _
    · simp only [Fin.reduceFinMk, Pi.zero_apply, CFSG.Quasithin.St84.G24LE.quadDefect]
      rw [hsq, hcmq, matV1_two, matZ1_two, hk, Pi.add_apply]
      exact CharTwo.add_self_eq_zero (R := ZMod 2) _
  let P : Matrix (Fin 2) (CFSG.Quasithin.St84.G24LE.Mono 8 × Fin 2) (ZMod 2) :=
    CFSG.Quasithin.St84.G24LE.ent (CFSG.Quasithin.St84.G24LE.ofBits
      CFSG.Quasithin.St84.G24LE.pQuad1) (fun i : Fin 2 => i.val)
      (fun u => CFSG.Quasithin.St84.G24LE.quadColKey u)
  let Y : Matrix (CFSG.Quasithin.St84.G24LE.Mono 8 × Fin 2)
      (Fin 3 × CFSG.Quasithin.St84.G24LE.Mono 8 × Fin 2) (ZMod 2) :=
    CFSG.Quasithin.St84.G24LE.ent (CFSG.Quasithin.St84.G24LE.ofBits
      CFSG.Quasithin.St84.G24LE.yQuad1)
      (fun u => CFSG.Quasithin.St84.G24LE.quadColKey u)
      (fun r => CFSG.Quasithin.St84.G24LE.quadRowKey r)
  let T : Matrix (Fin 3 × CFSG.Quasithin.St84.G24LE.Mono 8 × Fin 2)
      (CFSG.Quasithin.St84.G24LE.Mono 8 × Fin 2) (ZMod 2) :=
    CFSG.Quasithin.St84.G24LE.ent
      (CFSG.Quasithin.St84.G24LE.tab (CFSG.Quasithin.St84.G24LE.quadRows 8 2)
        (CFSG.Quasithin.St84.G24LE.quadCols 8 2)
        (fun r u => CFSG.Quasithin.St84.G24LE.quadM CFSG.Quasithin.St84.G24MF.matV1
          CFSG.Quasithin.St84.G24MF.matZ1 r u))
      (fun r => CFSG.Quasithin.St84.G24LE.quadRowKey r)
      (fun u => CFSG.Quasithin.St84.G24LE.quadColKey u)
  have hspan : CFSG.Quasithin.St84.G24LE.spanOK
      (CFSG.Quasithin.St84.G24LE.quadM CFSG.Quasithin.St84.G24MF.matV1
        CFSG.Quasithin.St84.G24MF.matZ1) T
      (CFSG.Quasithin.St84.G24LE.quadK CFSG.Quasithin.St84.G24MF.sqV1
        CFSG.Quasithin.St84.G24MF.cmV1 om) P Y = true := by
    simpa [CFSG.Quasithin.St84.G24LE.quad1Check, P, Y, T] using
      quad1Check_of_certificate lin_eq_check
  have hx : x = CFSG.Quasithin.St84.G24LE.quadK CFSG.Quasithin.St84.G24MF.sqV1
      CFSG.Quasithin.St84.G24MF.cmV1 om *ᵥ (P *ᵥ x) :=
    spanOK_spec hspan x hM
  let c : Fin 2 → ZMod 2 := P *ᵥ x
  have hxc : x = CFSG.Quasithin.St84.G24LE.quadK CFSG.Quasithin.St84.G24MF.sqV1
      CFSG.Quasithin.St84.G24MF.cmV1 om *ᵥ c := hx
  have hsqc : sq = (c 0 • CFSG.Quasithin.St84.G24MF.sqV1) +
      (c 1 • (fun i => om *ᵥ CFSG.Quasithin.St84.G24MF.sqV1 i)) := by
    funext i t
    have h := congrFun hxc (Sum.inl i, t)
    rw [quadK_mulVec_inl] at h
    simpa only [x, CFSG.Quasithin.St84.G24LE.coeffVec,
      CFSG.Quasithin.St84.G24LE.sqOf, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] using h
  have hcmc : ∀ i j, i < j → cm i j =
      ((c 0 • CFSG.Quasithin.St84.G24MF.cmV1) +
        (c 1 • (fun i j => om *ᵥ CFSG.Quasithin.St84.G24MF.cmV1 i j))) i j := by
    intro i j hij
    funext t
    have h := congrFun hxc (Sum.inr ⟨(i, j), hij⟩, t)
    rw [quadK_mulVec_inr] at h
    simpa only [x, CFSG.Quasithin.St84.G24LE.coeffVec,
      CFSG.Quasithin.St84.G24LE.cmOf, hij, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] using h
  have hquad : ∀ v, quadMapOfCoeffs sq cm v =
      (c 0 • (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) + c 1 • om) *ᵥ
        quadMapOfCoeffs CFSG.Quasithin.St84.G24MF.sqV1 CFSG.Quasithin.St84.G24MF.cmV1 v := by
    intro v
    rw [hsqc]
    rw [CFSG.GroupTheory.quadMapOfCoeffs_congr hcmc v]
    rw [CFSG.GroupTheory.quadMapOfCoeffs_add,
      CFSG.GroupTheory.quadMapOfCoeffs_smul,
      CFSG.GroupTheory.quadMapOfCoeffs_smul,
      CFSG.GroupTheory.quadMapOfCoeffs_mulVec_coeffs]
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  rcases zmod_two_cases (c 0) with h0 | h0 <;>
    rcases zmod_two_cases (c 1) with h1 | h1
  · exfalso
    have hc : c = 0 := by
      funext k
      fin_cases k <;> simp [h0, h1]
    have hx0 : x = 0 := by rw [hxc, hc, Matrix.mulVec_zero]
    obtain ⟨i, j, hij, hneij⟩ := hne
    have hz : cm i j = 0 := by
      funext t
      have h := congrFun hx0 (Sum.inr ⟨(i, j), hij⟩, t)
      simpa [x, CFSG.Quasithin.St84.G24LE.coeffVec] using h
    exact hneij hz
  · refine ⟨1, by norm_num, fun v => ?_⟩
    have hv := hquad v
    rw [h0, h1] at hv
    simp only [one_smul, zero_smul, add_zero, zero_add, Matrix.one_mulVec,
      Matrix.zero_mulVec] at hv
    simpa [pow_one] using hv
  · refine ⟨0, by norm_num, fun v => ?_⟩
    have hv := hquad v
    rw [h0, h1] at hv
    simp only [one_smul, zero_smul, add_zero, zero_add, Matrix.one_mulVec,
      Matrix.zero_mulVec] at hv
    simpa using hv
  · refine ⟨2, by norm_num, fun v => ?_⟩
    have h2 : om ^ 2 = (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) + om := by decide
    have hv := hquad v
    rw [h0, h1] at hv
    simp only [one_smul, zero_smul, add_zero, zero_add, Matrix.one_mulVec,
      Matrix.zero_mulVec] at hv
    rw [← h2] at hv
    simpa using hv

theorem quad2_proportional {sq : Fin 6 → Fin 4 → ZMod 2}
    {cm : Fin 6 → Fin 6 → Fin 4 → ZMod 2}
    (ha : ∀ v, quadMapOfCoeffs sq cm
      (v2Block 1 (CFSG.Quasithin.St84.G24LE.nonsplitX 0) aN *ᵥ v) =
        aN *ᵥ quadMapOfCoeffs sq cm v)
    (hb : ∀ v, quadMapOfCoeffs sq cm
      (v2Block 1 (CFSG.Quasithin.St84.G24LE.nonsplitX 1) bN *ᵥ v) =
        bN *ᵥ quadMapOfCoeffs sq cm v)
    (hk : ∀ v, quadMapOfCoeffs sq cm (v2Block om
      (CFSG.Quasithin.St84.G24LE.nonsplitX 2)
        CFSG.Quasithin.St84.G24LE.omegaN *ᵥ v) = quadMapOfCoeffs sq cm v)
    (hne : ∃ i j, i < j ∧ cm i j ≠ 0) :
    ∃ s < 3, ∀ v, quadMapOfCoeffs sq cm v = CFSG.Quasithin.St84.G24LE.omegaN ^ s *ᵥ
      quadMapOfCoeffs CFSG.Quasithin.St84.G24MF.sqV2 CFSG.Quasithin.St84.G24MF.cmV2 v := by
  let x : CFSG.Quasithin.St84.G24LE.Mono 6 × Fin 4 → ZMod 2 :=
    CFSG.Quasithin.St84.G24LE.coeffVec sq cm
  have hsq : CFSG.Quasithin.St84.G24LE.sqOf x = sq := rfl
  have hcm : ∀ i j, i < j → CFSG.Quasithin.St84.G24LE.cmOf x i j = cm i j := by
    intro i j h
    funext t
    simp [x, CFSG.Quasithin.St84.G24LE.coeffVec,
      CFSG.Quasithin.St84.G24LE.cmOf, h]
  have hcmq : quadMapOfCoeffs sq (CFSG.Quasithin.St84.G24LE.cmOf x) =
      quadMapOfCoeffs sq cm := by
    funext v
    exact CFSG.GroupTheory.quadMapOfCoeffs_congr hcm v
  have hM : CFSG.Quasithin.St84.G24LE.quadM CFSG.Quasithin.St84.G24MF.matV2
      CFSG.Quasithin.St84.G24MF.matZ2 *ᵥ x = 0 := by
    rw [quadM_mulVec]
    funext r
    obtain ⟨g, μ, t⟩ := r
    fin_cases g
    · simp only [Fin.reduceFinMk, Pi.zero_apply, CFSG.Quasithin.St84.G24LE.quadDefect]
      rw [hsq, hcmq, matV2_zero, matZ2_zero, ha, Pi.add_apply]
      exact CharTwo.add_self_eq_zero (R := ZMod 2) _
    · simp only [Fin.reduceFinMk, Pi.zero_apply, CFSG.Quasithin.St84.G24LE.quadDefect]
      rw [hsq, hcmq, matV2_one, matZ2_one, hb, Pi.add_apply]
      exact CharTwo.add_self_eq_zero (R := ZMod 2) _
    · simp only [Fin.reduceFinMk, Pi.zero_apply, CFSG.Quasithin.St84.G24LE.quadDefect]
      rw [hsq, hcmq, matV2_two, matZ2_two, hk, Matrix.one_mulVec, Pi.add_apply]
      exact CharTwo.add_self_eq_zero (R := ZMod 2) _
  let P : Matrix (Fin 2) (CFSG.Quasithin.St84.G24LE.Mono 6 × Fin 4) (ZMod 2) :=
    CFSG.Quasithin.St84.G24LE.ent (CFSG.Quasithin.St84.G24LE.ofBits
      CFSG.Quasithin.St84.G24LE.pQuad2) (fun i : Fin 2 => i.val)
      (fun u => CFSG.Quasithin.St84.G24LE.quadColKey u)
  let Y : Matrix (CFSG.Quasithin.St84.G24LE.Mono 6 × Fin 4)
      (Fin 3 × CFSG.Quasithin.St84.G24LE.Mono 6 × Fin 4) (ZMod 2) :=
    CFSG.Quasithin.St84.G24LE.ent (CFSG.Quasithin.St84.G24LE.ofBits
      CFSG.Quasithin.St84.G24LE.yQuad2)
      (fun u => CFSG.Quasithin.St84.G24LE.quadColKey u)
      (fun r => CFSG.Quasithin.St84.G24LE.quadRowKey r)
  let T : Matrix (Fin 3 × CFSG.Quasithin.St84.G24LE.Mono 6 × Fin 4)
      (CFSG.Quasithin.St84.G24LE.Mono 6 × Fin 4) (ZMod 2) :=
    CFSG.Quasithin.St84.G24LE.ent
      (CFSG.Quasithin.St84.G24LE.tab (CFSG.Quasithin.St84.G24LE.quadRows 6 4)
        (CFSG.Quasithin.St84.G24LE.quadCols 6 4)
        (fun r u => CFSG.Quasithin.St84.G24LE.quadM CFSG.Quasithin.St84.G24MF.matV2
          CFSG.Quasithin.St84.G24MF.matZ2 r u))
      (fun r => CFSG.Quasithin.St84.G24LE.quadRowKey r)
      (fun u => CFSG.Quasithin.St84.G24LE.quadColKey u)
  have hspan : CFSG.Quasithin.St84.G24LE.spanOK
      (CFSG.Quasithin.St84.G24LE.quadM CFSG.Quasithin.St84.G24MF.matV2
        CFSG.Quasithin.St84.G24MF.matZ2) T
      (CFSG.Quasithin.St84.G24LE.quadK CFSG.Quasithin.St84.G24MF.sqV2
        CFSG.Quasithin.St84.G24MF.cmV2 CFSG.Quasithin.St84.G24LE.omegaN) P Y = true := by
    simpa [CFSG.Quasithin.St84.G24LE.quad2Check, P, Y, T] using
      quad2Check_of_certificate lin_eq_check
  have hx : x = CFSG.Quasithin.St84.G24LE.quadK CFSG.Quasithin.St84.G24MF.sqV2
      CFSG.Quasithin.St84.G24MF.cmV2 CFSG.Quasithin.St84.G24LE.omegaN *ᵥ (P *ᵥ x) :=
    spanOK_spec hspan x hM
  let c : Fin 2 → ZMod 2 := P *ᵥ x
  have hxc : x = CFSG.Quasithin.St84.G24LE.quadK CFSG.Quasithin.St84.G24MF.sqV2
      CFSG.Quasithin.St84.G24MF.cmV2 CFSG.Quasithin.St84.G24LE.omegaN *ᵥ c := hx
  have hsqc : sq = (c 0 • CFSG.Quasithin.St84.G24MF.sqV2) +
      (c 1 • (fun i => CFSG.Quasithin.St84.G24LE.omegaN *ᵥ CFSG.Quasithin.St84.G24MF.sqV2 i)) := by
    funext i t
    have h := congrFun hxc (Sum.inl i, t)
    rw [quadK_mulVec_inl] at h
    simpa only [x, CFSG.Quasithin.St84.G24LE.coeffVec,
      CFSG.Quasithin.St84.G24LE.sqOf, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] using h
  have hcmc : ∀ i j, i < j → cm i j =
      ((c 0 • CFSG.Quasithin.St84.G24MF.cmV2) +
        (c 1 • (fun i j => CFSG.Quasithin.St84.G24LE.omegaN *ᵥ
          CFSG.Quasithin.St84.G24MF.cmV2 i j))) i j := by
    intro i j hij
    funext t
    have h := congrFun hxc (Sum.inr ⟨(i, j), hij⟩, t)
    rw [quadK_mulVec_inr] at h
    simpa only [x, CFSG.Quasithin.St84.G24LE.coeffVec,
      CFSG.Quasithin.St84.G24LE.cmOf, hij, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] using h
  have hquad : ∀ v, quadMapOfCoeffs sq cm v =
      (c 0 • (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) +
        c 1 • CFSG.Quasithin.St84.G24LE.omegaN) *ᵥ
        quadMapOfCoeffs CFSG.Quasithin.St84.G24MF.sqV2 CFSG.Quasithin.St84.G24MF.cmV2 v := by
    intro v
    rw [hsqc]
    rw [CFSG.GroupTheory.quadMapOfCoeffs_congr hcmc v]
    rw [CFSG.GroupTheory.quadMapOfCoeffs_add,
      CFSG.GroupTheory.quadMapOfCoeffs_smul,
      CFSG.GroupTheory.quadMapOfCoeffs_smul,
      CFSG.GroupTheory.quadMapOfCoeffs_mulVec_coeffs]
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  rcases zmod_two_cases (c 0) with h0 | h0 <;>
    rcases zmod_two_cases (c 1) with h1 | h1
  · exfalso
    have hc : c = 0 := by
      funext k
      fin_cases k <;> simp [h0, h1]
    have hx0 : x = 0 := by rw [hxc, hc, Matrix.mulVec_zero]
    obtain ⟨i, j, hij, hneij⟩ := hne
    have hz : cm i j = 0 := by
      funext t
      have h := congrFun hx0 (Sum.inr ⟨(i, j), hij⟩, t)
      simpa [x, CFSG.Quasithin.St84.G24LE.coeffVec] using h
    exact hneij hz
  · refine ⟨1, by norm_num, fun v => ?_⟩
    have hv := hquad v
    rw [h0, h1] at hv
    simp only [one_smul, zero_smul, add_zero, zero_add, Matrix.one_mulVec,
      Matrix.zero_mulVec] at hv
    simpa [pow_one] using hv
  · refine ⟨0, by norm_num, fun v => ?_⟩
    have hv := hquad v
    rw [h0, h1] at hv
    simp only [one_smul, zero_smul, add_zero, zero_add, Matrix.one_mulVec,
      Matrix.zero_mulVec] at hv
    simpa using hv
  · refine ⟨2, by norm_num, fun v => ?_⟩
    have h2 : CFSG.Quasithin.St84.G24LE.omegaN ^ 2 =
        (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) + CFSG.Quasithin.St84.G24LE.omegaN := by decide
    have hv := hquad v
    rw [h0, h1] at hv
    simp only [one_smul, zero_smul, add_zero, zero_add, Matrix.one_mulVec,
      Matrix.zero_mulVec] at hv
    rw [← h2] at hv
    simpa using hv

theorem eq_zero_or_one_or_omegaN {M : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (ha : M * aN = aN * M) (hb : M * bN = bN * M) :
    M = 0 ∨ M = 1 ∨ M = CFSG.Quasithin.St84.G24LE.omegaN ∨
      M = CFSG.Quasithin.St84.G24LE.omegaN ^ 2 := by
  let v : Fin 4 × Fin 4 → ZMod 2 := fun u => M u.1 u.2
  have hM : CFSG.Quasithin.St84.G24LE.commM *ᵥ v = 0 := by
    rw [commM_mulVec]
    funext r
    rcases r with ⟨s, i, j⟩
    dsimp only
    fin_cases s
    · change (M * aN + aN * M) i j = 0
      rw [ha, Matrix.add_apply]
      exact CharTwo.add_self_eq_zero (R := ZMod 2) _
    · change (M * bN + bN * M) i j = 0
      rw [hb, Matrix.add_apply]
      exact CharTwo.add_self_eq_zero (R := ZMod 2) _
  let P : Matrix (Fin 2) (Fin 4 × Fin 4) (ZMod 2) :=
    CFSG.Quasithin.St84.G24LE.ent (CFSG.Quasithin.St84.G24LE.ofBits
      CFSG.Quasithin.St84.G24LE.pComm) (fun i : Fin 2 => i.val)
      (fun u => CFSG.Quasithin.St84.G24LE.commColKey u)
  let Y : Matrix (Fin 4 × Fin 4) (Fin 2 × Fin 4 × Fin 4) (ZMod 2) :=
    CFSG.Quasithin.St84.G24LE.ent (CFSG.Quasithin.St84.G24LE.ofBits
      CFSG.Quasithin.St84.G24LE.yComm)
      (fun u => CFSG.Quasithin.St84.G24LE.commColKey u)
      (fun r => CFSG.Quasithin.St84.G24LE.commRowKey r)
  let T : Matrix (Fin 2 × Fin 4 × Fin 4) (Fin 4 × Fin 4) (ZMod 2) :=
    CFSG.Quasithin.St84.G24LE.ent
      (CFSG.Quasithin.St84.G24LE.tab CFSG.Quasithin.St84.G24LE.commRows
        CFSG.Quasithin.St84.G24LE.commCols
        (fun r u => CFSG.Quasithin.St84.G24LE.commM r u))
      (fun r => CFSG.Quasithin.St84.G24LE.commRowKey r)
      (fun u => CFSG.Quasithin.St84.G24LE.commColKey u)
  have hspan : CFSG.Quasithin.St84.G24LE.spanOK CFSG.Quasithin.St84.G24LE.commM T
      CFSG.Quasithin.St84.G24LE.commK P Y = true := by
    simpa [CFSG.Quasithin.St84.G24LE.commCheck, P, Y, T] using
      commCheck_of_certificate lin_eq_check
  let c : Fin 2 → ZMod 2 := P *ᵥ v
  have hxc : v = CFSG.Quasithin.St84.G24LE.commK *ᵥ c :=
    spanOK_spec hspan v hM
  have hMvec : M = c 0 • (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) +
      c 1 • CFSG.Quasithin.St84.G24LE.omegaN := by
    ext i j
    have h := congrFun hxc (i, j)
    simpa [v, commK_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h
  rcases zmod_two_cases (c 0) with h0 | h0 <;>
    rcases zmod_two_cases (c 1) with h1 | h1
  · left
    rw [hMvec, h0, h1]
    simp
  · right; right; left
    rw [hMvec, h0, h1]
    simp
  · right; left
    rw [hMvec, h0, h1]
    simp
  · right; right; right
    rw [hMvec, h0, h1]
    simp only [one_smul]
    rw [← omegaN_sq]

private theorem v2Block_mul (U1 : Matrix (Fin 2) (Fin 2) (ZMod 2))
    (X1 : Matrix (Fin 2) (Fin 4) (ZMod 2)) (N1 : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (U2 : Matrix (Fin 2) (Fin 2) (ZMod 2)) (X2 : Matrix (Fin 2) (Fin 4) (ZMod 2))
    (N2 : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    v2Block U1 X1 N1 * v2Block U2 X2 N2 =
      v2Block (U1 * U2) (U1 * X2 + X1 * N2) (N1 * N2) := by
  ext i j
  refine Fin.addCases (m := 2) (n := 4) (fun a => ?_) (fun c => ?_) i
  · refine Fin.addCases (m := 2) (n := 4) (fun b => ?_) (fun d => ?_) j
    · rw [v2Block_castAdd_castAdd, Matrix.mul_apply, Fin.sum_univ_add (a := 2) (b := 4),
        Matrix.mul_apply]
      simp only [v2Block_castAdd_castAdd, v2Block_castAdd_natAdd, v2Block_natAdd_castAdd,
        mul_zero, Finset.sum_const_zero, add_zero]
    · rw [v2Block_castAdd_natAdd, Matrix.mul_apply, Fin.sum_univ_add (a := 2) (b := 4),
        Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
      simp only [v2Block_castAdd_castAdd, v2Block_castAdd_natAdd, v2Block_natAdd_castAdd,
        v2Block_natAdd_natAdd, mul_zero, Finset.sum_const_zero, add_zero]
  · refine Fin.addCases (m := 2) (n := 4) (fun b => ?_) (fun d => ?_) j
    · rw [v2Block_natAdd_castAdd, Matrix.mul_apply, Fin.sum_univ_add (a := 2) (b := 4)]
      simp only [v2Block_castAdd_castAdd, v2Block_castAdd_natAdd, v2Block_natAdd_castAdd,
        v2Block_natAdd_natAdd, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    · rw [v2Block_natAdd_natAdd, Matrix.mul_apply, Fin.sum_univ_add (a := 2) (b := 4),
        Matrix.mul_apply]
      simp only [v2Block_castAdd_castAdd, v2Block_castAdd_natAdd, v2Block_natAdd_castAdd,
        v2Block_natAdd_natAdd, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
      ring

private theorem v2Block_mul_upper_apply
    (U1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) (X1 : Matrix (Fin 2) (Fin 4) (ZMod 2))
    (N1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) (U2 : Matrix (Fin 2) (Fin 2) (ZMod 2))
    (X2 : Matrix (Fin 2) (Fin 4) (ZMod 2)) (N2 : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (i : Fin 2) (j : Fin 4) :
    (v2Block U1 X1 N1 * v2Block U2 X2 N2) (Fin.castAdd 4 i) (Fin.natAdd 2 j) =
      (U1 * X2 + X1 * N2) i j := by
  rw [v2Block_mul, v2Block_castAdd_natAdd]

private theorem v2Block_cube_upper_apply
    (U : Matrix (Fin 2) (Fin 2) (ZMod 2)) (X : Matrix (Fin 2) (Fin 4) (ZMod 2))
    (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) (i : Fin 2) (j : Fin 4) :
    (v2Block U X N ^ 3) (Fin.castAdd 4 i) (Fin.natAdd 2 j) =
      (U * (U * X) + (U * (X * N) + X * (N * N))) i j := by
  rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two, v2Block_mul,
    v2Block_mul_upper_apply]
  simp only [Matrix.mul_assoc, Matrix.add_mul]

private theorem v2Block_one_zero_one :
    v2Block 1 (0 : Matrix (Fin 2) (Fin 4) (ZMod 2))
      (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 := by
  decide

private theorem v2Block_one_upper_entry (i : Fin 2) (j : Fin 4) :
    (1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Fin.castAdd 4 i) (Fin.natAdd 2 j) = 0 := by
  have hne : (Fin.castAdd 4 i : Fin 6) ≠ Fin.natAdd 2 j := by
    intro hEq
    have hv := congrArg Fin.val hEq
    simp [Fin.castAdd, Fin.natAdd] at hv
    omega
  simp [Matrix.one_apply, hne]

private theorem sum_fin_three (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    (∑ k : Fin 3, N ^ (k : ℕ)) = 1 + N + N ^ 2 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [pow_two, add_assoc]

private theorem v2Block_pow_unit (Y : Matrix (Fin 2) (Fin 4) (ZMod 2))
    (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) (m : ℕ) :
    v2Block 1 Y N ^ m = v2Block 1 (Y * ∑ k : Fin m, N ^ (k : ℕ)) (N ^ m) := by
  induction m with
  | zero => simp [v2Block_one_zero_one]
  | succ m ih =>
    rw [pow_succ, ih, v2Block_mul]
    have hsum : (∑ k : Fin (m + 1), N ^ (k : ℕ)) = 1 + (∑ k : Fin m, N ^ (k : ℕ)) * N := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, Fin.val_succ]
      simp_rw [pow_succ]
      rw [← Finset.sum_mul]
    have hX : Y * (∑ k : Fin (m + 1), N ^ (k : ℕ)) =
        Y + (Y * (∑ k : Fin m, N ^ (k : ℕ))) * N := by
      rw [hsum, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_one]
    rw [hX]
    simp only [Matrix.one_mul, pow_succ]

private theorem v2Block_five_upper_apply (Y : Matrix (Fin 2) (Fin 4) (ZMod 2))
    (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) (i : Fin 2) (j : Fin 4) :
    (v2Block 1 Y N ^ 5) (Fin.castAdd 4 i) (Fin.natAdd 2 j) =
      (Y * ∑ k : Fin 5, N ^ (k : ℕ)) i j := by
  rw [v2Block_pow_unit, v2Block_castAdd_natAdd]

private theorem v2Block_upper_eq {U U' : Matrix (Fin 2) (Fin 2) (ZMod 2)}
    {X X' : Matrix (Fin 2) (Fin 4) (ZMod 2)}
    {N N' : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (h : v2Block U X N = v2Block U' X' N') : X = X' := by
  ext i j
  have h1 := congrFun (congrFun h (Fin.castAdd 4 i)) (Fin.natAdd 2 j)
  simpa [v2Block_castAdd_natAdd] using h1

private theorem v2Block_one_upper {X : Matrix (Fin 2) (Fin 4) (ZMod 2)}
    (h : v2Block 1 X 1 = 1) : X = 0 := by
  ext i j
  have h1 := congrFun (congrFun h (Fin.castAdd 4 i)) (Fin.natAdd 2 j)
  have hne : (Fin.castAdd 4 i : Fin 6) ≠ Fin.natAdd 2 j := by
    intro hEq
    have hv := congrArg Fin.val hEq
    simp [Fin.castAdd, Fin.natAdd] at hv
    omega
  simpa [v2Block_castAdd_natAdd, Matrix.one_apply, hne] using h1

private theorem v2Block_sq (X : Matrix (Fin 2) (Fin 4) (ZMod 2))
    (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    v2Block 1 X N * v2Block 1 X N = v2Block 1 (X + X * N) (N * N) := by
  rw [v2Block_mul]
  simp [Matrix.one_mul, Matrix.mul_one]

private theorem ext2Map_add (X Y : Fin 3 → Matrix (Fin 2) (Fin 4) (ZMod 2)) :
    CFSG.Quasithin.St84.G24LE.ext2Map (X + Y) =
      CFSG.Quasithin.St84.G24LE.ext2Map X + CFSG.Quasithin.St84.G24LE.ext2Map Y := by
  funext rho
  fin_cases rho
  · change ((X 0 + Y 0) + (X 0 + Y 0) * aN) =
      (X 0 + X 0 * aN) + (Y 0 + Y 0 * aN)
    simp only [Matrix.add_mul, Matrix.mul_add]
    try abel
  · change ((X 1 + Y 1) * (1 + bN + bN ^ 2)) =
      X 1 * (1 + bN + bN ^ 2) + Y 1 * (1 + bN + bN ^ 2)
    simp only [Matrix.add_mul, Matrix.mul_add]
    try abel
  · change (((X 1 + Y 1) + (X 0 + Y 0) * bN) *
        ∑ k : Fin 5, (aN * bN) ^ (k : ℕ)) =
      (X 1 + X 0 * bN) * (∑ k : Fin 5, (aN * bN) ^ (k : ℕ)) +
        (Y 1 + Y 0 * bN) * (∑ k : Fin 5, (aN * bN) ^ (k : ℕ))
    simp only [Matrix.add_mul, Matrix.mul_add]
    try abel
  · change (om ^ 2 * (X 2 + Y 2) + om * (X 2 + Y 2) * CFSG.Quasithin.St84.G24LE.omegaN +
        (X 2 + Y 2) * CFSG.Quasithin.St84.G24LE.omegaN ^ 2) =
      (om ^ 2 * X 2 + om * X 2 * CFSG.Quasithin.St84.G24LE.omegaN +
        X 2 * CFSG.Quasithin.St84.G24LE.omegaN ^ 2) +
      (om ^ 2 * Y 2 + om * Y 2 * CFSG.Quasithin.St84.G24LE.omegaN +
        Y 2 * CFSG.Quasithin.St84.G24LE.omegaN ^ 2)
    simp only [Matrix.add_mul, Matrix.mul_add]
    try abel
  · change ((X 2 + Y 2) + (X 0 + Y 0) * CFSG.Quasithin.St84.G24LE.omegaN +
        om * (X 0 + Y 0) + (X 2 + Y 2) * aN) =
      (X 2 + X 0 * CFSG.Quasithin.St84.G24LE.omegaN + om * X 0 + X 2 * aN) +
        (Y 2 + Y 0 * CFSG.Quasithin.St84.G24LE.omegaN + om * Y 0 + Y 2 * aN)
    simp only [Matrix.add_mul, Matrix.mul_add]
    try abel
  · change ((X 2 + Y 2) + (X 1 + Y 1) * CFSG.Quasithin.St84.G24LE.omegaN +
        om * (X 1 + Y 1) + (X 2 + Y 2) * bN) =
      (X 2 + X 1 * CFSG.Quasithin.St84.G24LE.omegaN + om * X 1 + X 2 * bN) +
        (Y 2 + Y 1 * CFSG.Quasithin.St84.G24LE.omegaN + om * Y 1 + Y 2 * bN)
    simp only [Matrix.add_mul, Matrix.mul_add]
    try abel

private theorem ext2Map_smul (a : ZMod 2)
    (X : Fin 3 → Matrix (Fin 2) (Fin 4) (ZMod 2)) :
    CFSG.Quasithin.St84.G24LE.ext2Map (a • X) =
      a • CFSG.Quasithin.St84.G24LE.ext2Map X := by
  rcases zmod_two_cases a with rfl | rfl <;> simp [CFSG.Quasithin.St84.G24LE.ext2Map]

private def matsOfVec (x : Fin 3 × Fin 2 × Fin 4 → ZMod 2) :
    Fin 3 → Matrix (Fin 2) (Fin 4) (ZMod 2) :=
  fun t => Matrix.of fun s j => x (t, s, j)

private def ext2Lin :
    (Fin 3 × Fin 2 × Fin 4 → ZMod 2) →ₗ[ZMod 2]
      (Fin 6 × Fin 2 × Fin 4 → ZMod 2) where
  toFun x r :=
    CFSG.Quasithin.St84.G24LE.ext2Map (matsOfVec x) r.1 r.2.1 r.2.2
  map_add' x y := by
    funext r
    have hX : matsOfVec (x + y) = matsOfVec x + matsOfVec y := rfl
    rw [hX, ext2Map_add]
    rfl
  map_smul' a x := by
    funext r
    have hX : matsOfVec (a • x) = a • matsOfVec x := rfl
    rw [hX, ext2Map_smul]
    rfl

private theorem ext2M_mulVec (X : Fin 3 → Matrix (Fin 2) (Fin 4) (ZMod 2)) :
    CFSG.Quasithin.St84.G24LE.ext2M *ᵥ
      (fun u : Fin 3 × Fin 2 × Fin 4 => X u.1 u.2.1 u.2.2) =
      fun r : Fin 6 × Fin 2 × Fin 4 =>
        CFSG.Quasithin.St84.G24LE.ext2Map X r.1 r.2.1 r.2.2 := by
  have hmat : LinearMap.toMatrix' ext2Lin = CFSG.Quasithin.St84.G24LE.ext2M := by
    ext r u
    rw [LinearMap.toMatrix'_apply]
    have hX : matsOfVec (Pi.single u (1 : ZMod 2)) =
        (fun t => if t = u.1 then Matrix.single u.2.1 u.2.2 1 else 0) := by
      funext t
      by_cases ht : t = u.1
      · subst ht
        ext s j
        by_cases hs : s = u.2.1
        · subst hs
          by_cases hj : j = u.2.2
          · subst hj
            simp [matsOfVec, Pi.single_apply, Matrix.single]
          · simp [matsOfVec, Pi.single_apply, Matrix.single, hj, Prod.ext_iff, eq_comm]
        · simp [matsOfVec, Pi.single_apply, Matrix.single, hs, Prod.ext_iff, eq_comm]
      · ext s j
        simp [matsOfVec, Pi.single_apply, Matrix.single, ht, Prod.ext_iff, eq_comm]
    change CFSG.Quasithin.St84.G24LE.ext2Map (matsOfVec (Pi.single u (1 : ZMod 2)))
      r.1 r.2.1 r.2.2 = CFSG.Quasithin.St84.G24LE.ext2M r u
    rw [hX]
    simp only [CFSG.Quasithin.St84.G24LE.ext2M, Matrix.of_apply]
  rw [← hmat, LinearMap.toMatrix'_mulVec]
  rfl

private theorem ext2Map_eq_zero_of_relations
    {X : Fin 3 → Matrix (Fin 2) (Fin 4) (ZMod 2)}
    (h0 : v2Block 1 (X 0) aN * v2Block 1 (X 0) aN = 1)
    (h1 : v2Block 1 (X 1) bN ^ 3 = 1)
    (h2 : (v2Block 1 (X 0) aN * v2Block 1 (X 1) bN) ^ 5 = 1)
    (h3 : v2Block om (X 2) CFSG.Quasithin.St84.G24LE.omegaN ^ 3 = 1)
    (h4 : v2Block 1 (X 0) aN * v2Block om (X 2) CFSG.Quasithin.St84.G24LE.omegaN =
      v2Block om (X 2) CFSG.Quasithin.St84.G24LE.omegaN * v2Block 1 (X 0) aN)
    (h5 : v2Block 1 (X 1) bN * v2Block om (X 2) CFSG.Quasithin.St84.G24LE.omegaN =
      v2Block om (X 2) CFSG.Quasithin.St84.G24LE.omegaN * v2Block 1 (X 1) bN) :
    CFSG.Quasithin.St84.G24LE.ext2Map X = 0 := by
  have haN : aN * aN = 1 := by decide
  have hbN : bN ^ 3 = 1 := by decide
  have hN5 : (aN * bN) ^ 5 = 1 := by decide
  have hX0 : X 0 + X 0 * aN = 0 := by
    apply v2Block_one_upper
    simpa [v2Block_mul, haN, Matrix.one_mul, Matrix.mul_one] using h0
  have hX1 : X 1 * (1 + bN + bN ^ 2) = 0 := by
    apply v2Block_one_upper
    simpa [v2Block_pow_unit, hbN, sum_fin_three, Matrix.mul_one] using h1
  have hAB : v2Block 1 (X 0) aN * v2Block 1 (X 1) bN =
      v2Block 1 (X 1 + X 0 * bN) (aN * bN) := by
    simpa [v2Block_mul, Matrix.one_mul, Matrix.mul_one]
  have h2' : (v2Block 1 (X 1 + X 0 * bN) (aN * bN)) ^ 5 = 1 := by
    simpa [hAB] using h2
  have hX2 : (X 1 + X 0 * bN) *
      (∑ k : Fin 5, (aN * bN) ^ (k : ℕ)) = 0 := by
    apply v2Block_one_upper
    simpa [v2Block_pow_unit, hN5, Matrix.mul_one] using h2'
  have hX3 : om ^ 2 * X 2 + om * X 2 * CFSG.Quasithin.St84.G24LE.omegaN +
      X 2 * CFSG.Quasithin.St84.G24LE.omegaN ^ 2 = 0 := by
    ext i j
    have h := congrFun (congrFun h3 (Fin.castAdd 4 i)) (Fin.natAdd 2 j)
    rw [v2Block_cube_upper_apply, v2Block_one_upper_entry] at h
    simpa [pow_two, Matrix.mul_assoc, add_assoc] using h
  have h4' : X 2 + X 0 * CFSG.Quasithin.St84.G24LE.omegaN =
      om * X 0 + X 2 * aN := by
    apply v2Block_upper_eq
    simpa [v2Block_mul, Matrix.one_mul, Matrix.mul_one] using h4
  have hAA : om * X 0 + om * X 0 = 0 := by
    ext i j
    rw [Matrix.add_apply]
    exact CharTwo.add_self_eq_zero (R := ZMod 2) _
  have hBB : X 2 * aN + X 2 * aN = 0 := by
    ext i j
    rw [Matrix.add_apply]
    exact CharTwo.add_self_eq_zero (R := ZMod 2) _
  have hX4 : X 2 + X 0 * CFSG.Quasithin.St84.G24LE.omegaN +
      om * X 0 + X 2 * aN = 0 := by
    rw [h4']
    calc
      om * X 0 + X 2 * aN + om * X 0 + X 2 * aN =
          (om * X 0 + om * X 0) + (X 2 * aN + X 2 * aN) := by abel
      _ = 0 := by rw [hAA, hBB, add_zero]
  have hAA1 : om * X 1 + om * X 1 = 0 := by
    ext i j
    rw [Matrix.add_apply]
    exact CharTwo.add_self_eq_zero (R := ZMod 2) _
  have hBB1 : X 2 * bN + X 2 * bN = 0 := by
    ext i j
    rw [Matrix.add_apply]
    exact CharTwo.add_self_eq_zero (R := ZMod 2) _
  have h5' : X 2 + X 1 * CFSG.Quasithin.St84.G24LE.omegaN =
      om * X 1 + X 2 * bN := by
    apply v2Block_upper_eq
    simpa [v2Block_mul, Matrix.one_mul, Matrix.mul_one] using h5
  have hX5 : X 2 + X 1 * CFSG.Quasithin.St84.G24LE.omegaN +
      om * X 1 + X 2 * bN = 0 := by
    rw [h5']
    calc
      om * X 1 + X 2 * bN + om * X 1 + X 2 * bN =
          (om * X 1 + om * X 1) + (X 2 * bN + X 2 * bN) := by abel
      _ = 0 := by rw [hAA1, hBB1, add_zero]
  funext rho
  fin_cases rho
  · simpa [CFSG.Quasithin.St84.G24LE.ext2Map] using hX0
  · simpa [CFSG.Quasithin.St84.G24LE.ext2Map] using hX1
  · simpa [CFSG.Quasithin.St84.G24LE.ext2Map] using hX2
  · simpa [CFSG.Quasithin.St84.G24LE.ext2Map] using hX3
  · simpa [CFSG.Quasithin.St84.G24LE.ext2Map] using hX4
  · simpa [CFSG.Quasithin.St84.G24LE.ext2Map] using hX5

private theorem ext2K_mulVec_apply (c : ((Fin 2 × Fin 4) ⊕ Fin 2) → ZMod 2)
    (t : Fin 3) (s : Fin 2) (j : Fin 4) :
    (CFSG.Quasithin.St84.G24LE.ext2K *ᵥ c) (t, s, j) =
      (∑ p : Fin 2 × Fin 4,
        c (Sum.inl p) * CFSG.Quasithin.St84.G24LE.shiftX
          (Matrix.single p.1 p.2 1) t s j) +
      c (Sum.inr 0) * CFSG.Quasithin.St84.G24LE.nonsplitX t s j +
      c (Sum.inr 1) * (om * CFSG.Quasithin.St84.G24LE.nonsplitX t) s j := by
  simp [CFSG.Quasithin.St84.G24LE.ext2K, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  abel

private theorem shiftX_sum (c : Fin 2 × Fin 4 → ZMod 2) (t : Fin 3) :
    CFSG.Quasithin.St84.G24LE.shiftX
      (∑ p : Fin 2 × Fin 4, c p • Matrix.single p.1 p.2 1) t =
      ∑ p : Fin 2 × Fin 4,
        c p • CFSG.Quasithin.St84.G24LE.shiftX (Matrix.single p.1 p.2 1) t := by
  have hsingle : ∀ p : Fin 2 × Fin 4,
      Matrix.single p.1 p.2 (c p) = c p • Matrix.single p.1 p.2 1 := by
    intro p
    ext i j
    by_cases h : i = p.1 ∧ j = p.2
    · rcases h with ⟨rfl, rfl⟩
      simp
    · simp [Matrix.single, h]
  fin_cases t
  · change (∑ p : Fin 2 × Fin 4, c p • Matrix.single p.1 p.2 1) * aN +
        ∑ p : Fin 2 × Fin 4, c p • Matrix.single p.1 p.2 1 =
      ∑ p : Fin 2 × Fin 4,
        c p • (Matrix.single p.1 p.2 1 * aN + Matrix.single p.1 p.2 1)
    rw [Matrix.sum_mul Finset.univ, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rw [Matrix.smul_mul, smul_add]
  · change (∑ p : Fin 2 × Fin 4, c p • Matrix.single p.1 p.2 1) * bN +
        ∑ p : Fin 2 × Fin 4, c p • Matrix.single p.1 p.2 1 =
      ∑ p : Fin 2 × Fin 4,
        c p • (Matrix.single p.1 p.2 1 * bN + Matrix.single p.1 p.2 1)
    rw [Matrix.sum_mul Finset.univ, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rw [Matrix.smul_mul, smul_add]
  · change (∑ p : Fin 2 × Fin 4, c p • Matrix.single p.1 p.2 1) *
        CFSG.Quasithin.St84.G24LE.omegaN +
      om * (∑ p : Fin 2 × Fin 4, c p • Matrix.single p.1 p.2 1) =
      ∑ p : Fin 2 × Fin 4,
        c p • (Matrix.single p.1 p.2 1 * CFSG.Quasithin.St84.G24LE.omegaN +
          om * Matrix.single p.1 p.2 1)
    rw [Matrix.sum_mul Finset.univ, Matrix.mul_sum Finset.univ, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_add]

theorem ext2_solutions {X : Fin 3 → Matrix (Fin 2) (Fin 4) (ZMod 2)}
    (h0 : v2Block 1 (X 0) aN * v2Block 1 (X 0) aN = 1)
    (h1 : v2Block 1 (X 1) bN ^ 3 = 1)
    (h2 : (v2Block 1 (X 0) aN * v2Block 1 (X 1) bN) ^ 5 = 1)
    (h3 : v2Block om (X 2) CFSG.Quasithin.St84.G24LE.omegaN ^ 3 = 1)
    (h4 : v2Block 1 (X 0) aN * v2Block om (X 2) CFSG.Quasithin.St84.G24LE.omegaN =
      v2Block om (X 2) CFSG.Quasithin.St84.G24LE.omegaN * v2Block 1 (X 0) aN)
    (h5 : v2Block 1 (X 1) bN * v2Block om (X 2) CFSG.Quasithin.St84.G24LE.omegaN =
      v2Block om (X 2) CFSG.Quasithin.St84.G24LE.omegaN * v2Block 1 (X 1) bN) :
    ∃ (m : Matrix (Fin 2) (Fin 4) (ZMod 2)) (L : Matrix (Fin 2) (Fin 2) (ZMod 2)),
      (L = 0 ∨ L = 1 ∨ L = om ∨ L = om ^ 2) ∧
        ∀ t, X t = CFSG.Quasithin.St84.G24LE.shiftX m t +
          L * CFSG.Quasithin.St84.G24LE.nonsplitX t := by
  have hmap := ext2Map_eq_zero_of_relations h0 h1 h2 h3 h4 h5
  let v : Fin 3 × Fin 2 × Fin 4 → ZMod 2 := fun u => X u.1 u.2.1 u.2.2
  have hM : CFSG.Quasithin.St84.G24LE.ext2M *ᵥ v = 0 := by
    rw [ext2M_mulVec]
    funext r
    simp [hmap]
  let P : Matrix (((Fin 2 × Fin 4) ⊕ Fin 2))
      (Fin 3 × Fin 2 × Fin 4) (ZMod 2) :=
    CFSG.Quasithin.St84.G24LE.ent (CFSG.Quasithin.St84.G24LE.ofBits
      CFSG.Quasithin.St84.G24LE.pExt2)
      (fun c => CFSG.Quasithin.St84.G24LE.ext2KKey c)
      (fun u => CFSG.Quasithin.St84.G24LE.ext2ColKey u)
  let Y : Matrix (Fin 3 × Fin 2 × Fin 4) (Fin 6 × Fin 2 × Fin 4) (ZMod 2) :=
    CFSG.Quasithin.St84.G24LE.ent (CFSG.Quasithin.St84.G24LE.ofBits
      CFSG.Quasithin.St84.G24LE.yExt2)
      (fun u => CFSG.Quasithin.St84.G24LE.ext2ColKey u)
      (fun r => CFSG.Quasithin.St84.G24LE.ext2RowKey r)
  let T : Matrix (Fin 6 × Fin 2 × Fin 4) (Fin 3 × Fin 2 × Fin 4) (ZMod 2) :=
    CFSG.Quasithin.St84.G24LE.ent
      (CFSG.Quasithin.St84.G24LE.tab CFSG.Quasithin.St84.G24LE.ext2Rows
        CFSG.Quasithin.St84.G24LE.ext2Cols
        (fun r u => CFSG.Quasithin.St84.G24LE.ext2M r u))
      (fun r => CFSG.Quasithin.St84.G24LE.ext2RowKey r)
      (fun u => CFSG.Quasithin.St84.G24LE.ext2ColKey u)
  have hspan : CFSG.Quasithin.St84.G24LE.spanOK CFSG.Quasithin.St84.G24LE.ext2M T
      CFSG.Quasithin.St84.G24LE.ext2K P Y = true := by
    simpa [CFSG.Quasithin.St84.G24LE.ext2Check, P, Y, T] using
      ext2Check_of_certificate lin_eq_check
  let c : ((Fin 2 × Fin 4) ⊕ Fin 2) → ZMod 2 := P *ᵥ v
  have hxc : v = CFSG.Quasithin.St84.G24LE.ext2K *ᵥ c :=
    spanOK_spec hspan v hM
  let m : Matrix (Fin 2) (Fin 4) (ZMod 2) :=
    ∑ p : Fin 2 × Fin 4, c (Sum.inl p) • Matrix.single p.1 p.2 1
  let L : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
    c (Sum.inr 0) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) + c (Sum.inr 1) • om
  have hL : L = 0 ∨ L = 1 ∨ L = om ∨ L = om ^ 2 := by
    rcases zmod_two_cases (c (Sum.inr 0)) with h0 | h0 <;>
      rcases zmod_two_cases (c (Sum.inr 1)) with h1 | h1
    · left
      simp [L, h0, h1]
    · right; right; left
      simp [L, h0, h1]
    · right; left
      simp [L, h0, h1]
    · right; right; right
      have h2 : om ^ 2 = (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) + om := by decide
      simp [L, h0, h1]
      rw [← h2]
  refine ⟨m, L, hL, ?_⟩
  intro t
  ext s j
  have h := congrFun hxc (t, s, j)
  rw [ext2K_mulVec_apply] at h
  calc
    X t s j = (∑ p : Fin 2 × Fin 4,
        c (Sum.inl p) * CFSG.Quasithin.St84.G24LE.shiftX
          (Matrix.single p.1 p.2 1) t s j) +
        c (Sum.inr 0) * CFSG.Quasithin.St84.G24LE.nonsplitX t s j +
        c (Sum.inr 1) * (om * CFSG.Quasithin.St84.G24LE.nonsplitX t) s j := by
      simpa [v] using h
    _ = (CFSG.Quasithin.St84.G24LE.shiftX m t +
        L * CFSG.Quasithin.St84.G24LE.nonsplitX t) s j := by
      rw [shiftX_sum (fun p => c (Sum.inl p)) t, Matrix.add_apply,
        Matrix.sum_apply]
      simp [L, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      abel

end

end CFSG.Quasithin.F112R.St84.G24M
