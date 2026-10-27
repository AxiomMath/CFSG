module

public import CFSG.RankThree.PartTwo.Census.Spin.RootOp
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessOdd

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

open TauCeti
open scoped commutatorElement

namespace RootData

variable {K : Type*} [Field K] {N : Type*} [Fintype N] [DecidableEq N]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

section Block

theorem block_zero {P Q T H X : Matrix N N K} {a b κ : ℤ} {c : Kˣ}
    (hc : ∀ k : ℤ, k ≠ 0 → -4 ≤ k → k ≤ 4 → c ^ k ≠ 1) (hab : -4 ≤ a - b - κ ∧ a - b - κ ≤ 4)
    (hPT : P * T = ((c ^ a : Kˣ) : K) • P) (hTQ : T * Q = ((c ^ b : Kˣ) : K) • Q)
    (hPH : P * H = (a : K) • P) (hHQ : H * Q = (b : K) • Q)
    (hT : T * X = ((c ^ κ : Kˣ) : K) • (X * T)) :
    P * (H * X - X * H - (κ : K) • X) * Q = 0 := by
  have h1 : P * (H * X - X * H - (κ : K) • X) * Q = ((a : K) - b - κ) • (P * X * Q) := by
    calc P * (H * X - X * H - (κ : K) • X) * Q
        = P * H * X * Q - P * X * (H * Q) - (κ : K) • (P * X * Q) := by
          simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
      _ = ((a : K) - b - κ) • (P * X * Q) := by
          rw [hPH, hHQ, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, sub_smul, sub_smul]
  have h2 : (((c ^ a : Kˣ) : K) - ((c ^ κ : Kˣ) : K) * ((c ^ b : Kˣ) : K)) • (P * X * Q) = 0 := by
    have e1 : P * (T * X) * Q = ((c ^ a : Kˣ) : K) • (P * X * Q) := by
      rw [← mul_assoc, hPT, smul_mul_assoc, smul_mul_assoc]
    have e2 : P * (((c ^ κ : Kˣ) : K) • (X * T)) * Q =
        (((c ^ κ : Kˣ) : K) * ((c ^ b : Kˣ) : K)) • (P * X * Q) := by
      rw [mul_smul_comm, smul_mul_assoc, ← mul_assoc, mul_assoc (P * X) T Q, hTQ, mul_smul_comm,
        smul_smul]
    rw [sub_smul, ← e1, ← e2, hT, sub_self]
  by_cases h0 : a - b - κ = 0
  · rw [h1]
    have : ((a : K) - b - κ) = ((a - b - κ : ℤ) : K) := by push_cast; ring
    rw [this, h0, Int.cast_zero, zero_smul]
  · have hne : ((c ^ a : Kˣ) : K) - ((c ^ κ : Kˣ) : K) * ((c ^ b : Kˣ) : K) ≠ 0 := by
      intro h
      apply hc (a - b - κ) h0 hab.1 hab.2
      have h' : c ^ a = c ^ κ * c ^ b := Units.ext (by rw [Units.val_mul]; exact sub_eq_zero.mp h)
      rw [zpow_sub, zpow_sub, h', ← zpow_add, add_comm κ b, zpow_add]
      group
    rw [h1, (smul_eq_zero.mp h2).resolve_left hne, smul_zero]

variable {E F X : Matrix N N K}

theorem lie_H_of_conj (hp : SqZeroPair E F) {κ : ℤ} (hκ : -2 ≤ κ ∧ κ ≤ 2) {c : Kˣ}
    (hc : ∀ k : ℤ, k ≠ 0 → -4 ≤ k → k ≤ 4 → c ^ k ≠ 1)
    (hT : SqZeroPair.φ E F (c : K) 0 0 ((c⁻¹ : Kˣ) : K) * X =
      ((c ^ κ : Kˣ) : K) • (X * SqZeroPair.φ E F (c : K) 0 0 ((c⁻¹ : Kˣ) : K))) :
    (E * F - F * E) * X - X * (E * F - F * E) = (κ : K) • X := by
  set A := E * F with hAdef
  set B := F * E with hBdef
  set C := 1 - A - B with hCdef
  set T := SqZeroPair.φ E F (c : K) 0 0 ((c⁻¹ : Kˣ) : K) with hTdef
  have hAA : A * A = A := by rw [hAdef, ← mul_assoc, hp.efe]
  have hBB : B * B = B := by rw [hBdef, ← mul_assoc, hp.fef]
  have hAB : A * B = 0 := by
    rw [hAdef, hBdef, mul_assoc, ← mul_assoc F, hp.ff, zero_mul, mul_zero]
  have hBA : B * A = 0 := by
    rw [hAdef, hBdef, mul_assoc, ← mul_assoc E, hp.ee, zero_mul, mul_zero]
  have hAC : A * C = 0 := by rw [hCdef, mul_sub, mul_sub, mul_one, hAA, hAB, sub_self, sub_zero]
  have hBC : B * C = 0 := by rw [hCdef, mul_sub, mul_sub, mul_one, hBA, hBB, sub_zero, sub_self]
  have hCA : C * A = 0 := by rw [hCdef, sub_mul, sub_mul, one_mul, hAA, hBA, sub_self, sub_zero]
  have hCB : C * B = 0 := by rw [hCdef, sub_mul, sub_mul, one_mul, hAB, hBB, sub_zero, sub_self]
  have hCC : C * C = C := by
    rw [show C * C = C * 1 - C * A - C * B by rw [hCdef]; noncomm_ring, hCA, hCB, mul_one,
      sub_zero, sub_zero]
  have hTe : T = (c : K) • A + ((c⁻¹ : Kˣ) : K) • B + C := by
    rw [hTdef, SqZeroPair.φ, zero_smul, zero_smul, add_zero, add_zero]
  have hsum : A + B + C = 1 := by rw [hCdef]; abel
  have z1 : ((c ^ (1 : ℤ) : Kˣ) : K) = (c : K) := by rw [zpow_one]
  have zm : ((c ^ (-1 : ℤ) : Kˣ) : K) = ((c⁻¹ : Kˣ) : K) := by rw [zpow_neg_one]
  have z0 : ((c ^ (0 : ℤ) : Kˣ) : K) = 1 := by rw [zpow_zero, Units.val_one]
  have hAT : A * T = ((c ^ (1 : ℤ) : Kˣ) : K) • A := by
    rw [z1, hTe, mul_add, mul_add, mul_smul_comm, mul_smul_comm, hAA, hAB, hAC]
    simp only [smul_zero, add_zero]
  have hBT : B * T = ((c ^ (-1 : ℤ) : Kˣ) : K) • B := by
    rw [zm, hTe, mul_add, mul_add, mul_smul_comm, mul_smul_comm, hBA, hBB, hBC]
    simp only [smul_zero, zero_add, add_zero]
  have hCT : C * T = ((c ^ (0 : ℤ) : Kˣ) : K) • C := by
    rw [z0, one_smul, hTe, mul_add, mul_add, mul_smul_comm, mul_smul_comm, hCA, hCB, hCC]
    simp only [smul_zero, zero_add]
  have hTA : T * A = ((c ^ (1 : ℤ) : Kˣ) : K) • A := by
    rw [z1, hTe, add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, hAA, hBA, hCA]
    simp only [smul_zero, add_zero]
  have hTB : T * B = ((c ^ (-1 : ℤ) : Kˣ) : K) • B := by
    rw [zm, hTe, add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, hAB, hBB, hCB]
    simp only [smul_zero, zero_add, add_zero]
  have hTC : T * C = ((c ^ (0 : ℤ) : Kˣ) : K) • C := by
    rw [z0, one_smul, hTe, add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, hAC, hBC, hCC]
    simp only [smul_zero, zero_add]
  have hAH : A * (A - B) = ((1 : ℤ) : K) • A := by
    rw [mul_sub, hAA, hAB, sub_zero, Int.cast_one, one_smul]
  have hBH : B * (A - B) = ((-1 : ℤ) : K) • B := by
    rw [mul_sub, hBA, hBB, zero_sub, Int.cast_neg, Int.cast_one, neg_one_smul]
  have hCH : C * (A - B) = ((0 : ℤ) : K) • C := by
    rw [mul_sub, hCA, hCB, sub_zero, Int.cast_zero, zero_smul]
  have hHA : (A - B) * A = ((1 : ℤ) : K) • A := by
    rw [sub_mul, hAA, hBA, sub_zero, Int.cast_one, one_smul]
  have hHB : (A - B) * B = ((-1 : ℤ) : K) • B := by
    rw [sub_mul, hAB, hBB, zero_sub, Int.cast_neg, Int.cast_one, neg_one_smul]
  have hHC : (A - B) * C = ((0 : ℤ) : K) • C := by
    rw [sub_mul, hAC, hBC, sub_zero, Int.cast_zero, zero_smul]
  have hr : ∀ a b : ℤ, (a = 1 ∨ a = -1 ∨ a = 0) → (b = 1 ∨ b = -1 ∨ b = 0) →
      -4 ≤ a - b - κ ∧ a - b - κ ≤ 4 := by
    intro a b ha hb
    constructor <;> omega
  have b1 := block_zero hc (hr 1 1 (by omega) (by omega)) hAT hTA hAH hHA hT
  have b2 := block_zero hc (hr 1 (-1) (by omega) (by omega)) hAT hTB hAH hHB hT
  have b3 := block_zero hc (hr 1 0 (by omega) (by omega)) hAT hTC hAH hHC hT
  have b4 := block_zero hc (hr (-1) 1 (by omega) (by omega)) hBT hTA hBH hHA hT
  have b5 := block_zero hc (hr (-1) (-1) (by omega) (by omega)) hBT hTB hBH hHB hT
  have b6 := block_zero hc (hr (-1) 0 (by omega) (by omega)) hBT hTC hBH hHC hT
  have b7 := block_zero hc (hr 0 1 (by omega) (by omega)) hCT hTA hCH hHA hT
  have b8 := block_zero hc (hr 0 (-1) (by omega) (by omega)) hCT hTB hCH hHB hT
  have b9 := block_zero hc (hr 0 0 (by omega) (by omega)) hCT hTC hCH hHC hT
  have hY : (A - B) * X - X * (A - B) - (κ : K) • X = 0 := by
    calc (A - B) * X - X * (A - B) - (κ : K) • X
        = (A + B + C) * ((A - B) * X - X * (A - B) - (κ : K) • X) * (A + B + C) := by
          rw [hsum, one_mul, mul_one]
      _ = 0 := by simp only [add_mul, mul_add, b1, b2, b3, b4, b5, b6, b7, b8, b9, add_zero]
  exact sub_eq_zero.mp hY

end Block

variable (R : RootData K N ι)

theorem lie_H_E {c : Kˣ} (hc : ∀ k : ℤ, k ≠ 0 → -4 ≤ k → k ≤ 4 → c ^ k ≠ 1) (i j : ι)
    (hκ : -2 ≤ R.CM j i ∧ R.CM j i ≤ 2) :
    (R.E j * R.F j - R.F j * R.E j) * R.E i - R.E i * (R.E j * R.F j - R.F j * R.E j) =
      (R.CM j i : K) • R.E i := by
  refine lie_H_of_conj (R.sqZero j) hκ hc ?_
  have h1 := congrArg R.mat (R.h_conj_x j i c 1)
  rw [mat_mul, mat_mul, mat_h, mat_x, mat_x, SqZeroPair.φ_upper, SqZeroPair.φ_upper, one_smul,
    mul_one] at h1
  have hinv : R.mat (R.h j c)⁻¹ * R.mat (R.h j c) = 1 := by
    rw [← mat_mul, inv_mul_cancel, mat_one]
  rw [mat_h] at hinv
  have h2 := congrArg (· * SqZeroPair.φ (R.E j) (R.F j) (c : K) 0 0 ((c⁻¹ : Kˣ) : K)) h1
  simp only [mul_assoc, hinv, mul_one] at h2
  rw [mul_add, mul_one, add_mul, one_mul] at h2
  rw [add_left_cancel h2, smul_mul_assoc]

theorem lie_H_F {c : Kˣ} (hc : ∀ k : ℤ, k ≠ 0 → -4 ≤ k → k ≤ 4 → c ^ k ≠ 1) (i j : ι)
    (hκ : -2 ≤ R.CM j i ∧ R.CM j i ≤ 2) :
    (R.E j * R.F j - R.F j * R.E j) * R.F i - R.F i * (R.E j * R.F j - R.F j * R.E j) =
      ((-R.CM j i : ℤ) : K) • R.F i := by
  refine lie_H_of_conj (R.sqZero j) ⟨by omega, by omega⟩ hc ?_
  have h1 := congrArg R.mat (R.h_conj_y j i c 1)
  rw [mat_mul, mat_mul, mat_h, mat_y, mat_y, SqZeroPair.φ_lower, SqZeroPair.φ_lower, one_smul,
    mul_one] at h1
  have hinv : R.mat (R.h j c)⁻¹ * R.mat (R.h j c) = 1 := by
    rw [← mat_mul, inv_mul_cancel, mat_one]
  rw [mat_h] at hinv
  have h2 := congrArg (· * SqZeroPair.φ (R.E j) (R.F j) (c : K) 0 0 ((c⁻¹ : Kˣ) : K)) h1
  simp only [mul_assoc, hinv, mul_one] at h2
  rw [mul_add, mul_one, add_mul, one_mul] at h2
  rw [add_left_cancel h2, smul_mul_assoc, zpow_neg]

variable {R}

theorem mat_x' (i : ι) (u : K) : R.mat (R.x i u) = 1 + u • R.E i := by
  rw [mat_x, SqZeroPair.φ_upper]

theorem mat_y' (i : ι) (u : K) : R.mat (R.y i u) = 1 + u • R.F i := by
  rw [mat_y, SqZeroPair.φ_lower]

theorem mat_commutator {g g' : R.G} {A B : Matrix N N K} {u : K} (hA : A * A = 0)
    (hB : B * B = 0) (hABA : A * B * A = 0) (hBAB : B * A * B = 0) (hg : R.mat g = 1 + A)
    (hg' : R.mat g' = 1 + u • B) : R.mat ⁅g, g'⁆ = 1 + u • (A * B - B * A) := by
  have hg1 : R.mat g = 1 + (1 : K) • A := by rw [hg, one_smul]
  rw [commutatorElement_def, mat_mul, mat_mul, mat_mul, mat_inv_one_add_smul R hA hg1,
    mat_inv_one_add_smul R hB hg', hg, hg', one_smul]
  exact commutator_one_add hA hB hABA hBAB u

variable (R)

theorem bracket_identities {A B F : Matrix N N K} (hA : A * A = 0) (hB : B * B = 0)
    (hs1 : A * B * A = 0) (hBFB : B * F * B = B) (hFBF : F * B * F = F)
    (hAF : A * F = F * A) (hlie : (B * F - F * B) * A - A * (B * F - F * B) = -A) :
    (A * B - B * A) * (A * B - B * A) = 0 ∧ (A * B - B * A) * F * (A * B - B * A) = 0 ∧
      F * (A * B - B * A) * F = 0 ∧ (A * B - B * A) * F - F * (A * B - B * A) = A := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : (A * B - B * A) * (A * B - B * A) =
        A * B * A * B - A * (B * B) * A - B * (A * A) * B + B * (A * B * A) := by noncomm_ring
    rw [e, hs1, hA, hB]
    simp
  · have t1 : A * B * F * A * B = 0 := by
      calc A * B * F * A * B = A * B * (F * A) * B := by noncomm_ring
        _ = A * B * A * F * B := by rw [← hAF]; noncomm_ring
        _ = 0 := by rw [hs1]; simp
    have t2 : A * B * F * B * A = 0 := by
      calc A * B * F * B * A = A * (B * F * B) * A := by noncomm_ring
        _ = 0 := by rw [hBFB, hs1]
    have t3 : B * A * F * A * B = 0 := by
      calc B * A * F * A * B = B * A * (F * A) * B := by noncomm_ring
        _ = B * (A * A) * F * B := by rw [← hAF]; noncomm_ring
        _ = 0 := by rw [hA]; simp
    have t4 : B * A * F * B * A = 0 := by
      calc B * A * F * B * A = B * (A * F) * B * A := by noncomm_ring
        _ = B * F * (A * B * A) := by rw [hAF]; noncomm_ring
        _ = 0 := by rw [hs1, mul_zero]
    calc (A * B - B * A) * F * (A * B - B * A)
        = A * B * F * A * B - A * B * F * B * A - B * A * F * A * B + B * A * F * B * A := by
          noncomm_ring
      _ = 0 := by rw [t1, t2, t3, t4]; simp
  · have s1 : F * A * B * F = A * (F * B * F) := by rw [← hAF]; noncomm_ring
    have s2 : F * B * A * F = F * B * F * A := by
      calc F * B * A * F = F * B * (A * F) := by noncomm_ring
        _ = F * B * F * A := by rw [hAF]; noncomm_ring
    calc F * (A * B - B * A) * F = F * A * B * F - F * B * A * F := by noncomm_ring
      _ = 0 := by rw [s1, s2, hFBF, hAF, sub_self]
  · have r1 : B * A * F = B * F * A := by
      calc B * A * F = B * (A * F) := by noncomm_ring
        _ = B * F * A := by rw [hAF]; noncomm_ring
    have r2 : F * A * B = A * F * B := by rw [← hAF]
    calc (A * B - B * A) * F - F * (A * B - B * A)
        = A * B * F - B * A * F - F * A * B + F * B * A := by noncomm_ring
      _ = -((B * F - F * B) * A - A * (B * F - F * B)) := by rw [r1, r2]; noncomm_ring
      _ = A := by rw [hlie, neg_neg]

theorem x_eq_commutator {c : Kˣ} (hc : ∀ k : ℤ, k ≠ 0 → -4 ≤ k → k ≤ 4 → c ^ k ≠ 1)
    {i j : ι} (hij : i ≠ j) (hji : R.CM j i = -1) (hs1 : R.E i * R.E j * R.E i = 0)
    (hs2 : R.E j * R.E i * R.E j = 0) (u : K) :
    R.x i u = ⁅⁅R.x i 1, R.x j 1⁆, R.y j u⁆ := by
  have hlie := R.lie_H_E hc i j (by omega)
  rw [hji, Int.cast_neg, Int.cast_one, neg_one_smul] at hlie
  obtain ⟨hMM, hMFM, hFMF, hMF⟩ := bracket_identities (R.sqZero i).ee (R.sqZero j).ee hs1
    (R.sqZero j).efe (R.sqZero j).fef (R.commute_EF i j hij).eq hlie
  have hg1 : R.mat (R.x i 1) = 1 + R.E i := by rw [mat_x', one_smul]
  have hm := mat_commutator (R := R) (R.sqZero i).ee (R.sqZero j).ee hs1 hs2 hg1
    (mat_x' (R := R) j 1)
  rw [one_smul] at hm
  apply R.mat_injective
  rw [mat_commutator (R := R) hMM (R.sqZero j).ff hMFM hFMF hm (mat_y' j u), hMF, mat_x']

theorem y_eq_commutator {c : Kˣ} (hc : ∀ k : ℤ, k ≠ 0 → -4 ≤ k → k ≤ 4 → c ^ k ≠ 1)
    {i j : ι} (hij : i ≠ j) (hji : R.CM j i = -1) (hs1 : R.F i * R.F j * R.F i = 0)
    (hs2 : R.F j * R.F i * R.F j = 0) (u : K) :
    R.y i u = ⁅⁅R.y i 1, R.y j 1⁆, R.x j u⁆ := by
  have hlie := R.lie_H_F hc i j (by omega)
  rw [hji, neg_neg, Int.cast_one, one_smul] at hlie
  have hlie' : (R.F j * R.E j - R.E j * R.F j) * R.F i - R.F i * (R.F j * R.E j - R.E j * R.F j)
      = -R.F i := by
    calc (R.F j * R.E j - R.E j * R.F j) * R.F i - R.F i * (R.F j * R.E j - R.E j * R.F j)
        = -((R.E j * R.F j - R.F j * R.E j) * R.F i -
            R.F i * (R.E j * R.F j - R.F j * R.E j)) := by noncomm_ring
      _ = -R.F i := by rw [hlie]
  obtain ⟨hMM, hMEM, hEME, hME⟩ := bracket_identities (R.sqZero i).ff (R.sqZero j).ff hs1
    (R.sqZero j).fef (R.sqZero j).efe (R.commute_EF j i (Ne.symm hij)).eq.symm hlie'
  have hg1 : R.mat (R.y i 1) = 1 + R.F i := by rw [mat_y', one_smul]
  have hm := mat_commutator (R := R) (R.sqZero i).ff (R.sqZero j).ff hs1 hs2 hg1
    (mat_y' (R := R) j 1)
  rw [one_smul] at hm
  apply R.mat_injective
  rw [mat_commutator (R := R) hMM (R.sqZero j).ee hMEM hEME hm (mat_x' j u), hME, mat_y']

theorem rootsInCommutator_of_neighbour {σ : K →+* K} {F : R.G →* R.G}
    (hF : R.IsFrobenius σ F) {c : Kˣ} (hc : ∀ k : ℤ, k ≠ 0 → -4 ≤ k → k ≤ 4 → c ^ k ≠ 1)
    (hnb : ∀ i, ∃ j, i ≠ j ∧ R.CM j i = -1 ∧ R.E i * R.E j * R.E i = 0 ∧
      R.E j * R.E i * R.E j = 0 ∧ R.F i * R.F j * R.F i = 0 ∧ R.F j * R.F i * R.F j = 0) :
    R.RootsInCommutator σ F := by
  intro i u hu
  obtain ⟨j, hij, hji, h1, h2, h3, h4⟩ := hnb i
  have h1F : (1 : K) ∈ fixedField σ := (fixedField σ).one_mem
  have hc1 : ∀ {g g' : R.G}, g ∈ fixedSubgroup F → g' ∈ fixedSubgroup F →
      ⁅g, g'⁆ ∈ fixedSubgroup F := fun hg hg' => by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hg')
      (Subgroup.inv_mem _ hg)) (Subgroup.inv_mem _ hg')
  constructor
  · rw [R.x_eq_commutator hc hij hji h1 h2 u]
    exact Subgroup.commutator_mem_commutator
      (hc1 (x_mem_fixed hF h1F) (x_mem_fixed hF h1F)) (y_mem_fixed hF hu)
  · rw [R.y_eq_commutator hc hij hji h3 h4 u]
    exact Subgroup.commutator_mem_commutator
      (hc1 (y_mem_fixed hF h1F) (y_mem_fixed hF h1F)) (x_mem_fixed hF hu)

section Three

variable (hchar : (2 : K) = 0)
include hchar

theorem φ_xy (i : ι) : SqZeroPair.φ (R.E i) (R.F i) 1 1 0 1 * SqZeroPair.φ (R.E i) (R.F i) 1 0 1 1 =
    SqZeroPair.φ (R.E i) (R.F i) 0 1 1 1 := by
  rw [(R.sqZero i).φ_mul]
  simp only [mul_one, mul_zero, zero_add]
  rw [one_add_one_eq_two, hchar]

theorem xy_pow_three (i : ι) : (R.x i 1 * R.y i 1) ^ 3 = 1 := by
  apply R.mat_injective
  have hp := R.sqZero i
  have e2 : SqZeroPair.φ (R.E i) (R.F i) 0 1 1 1 * SqZeroPair.φ (R.E i) (R.F i) 0 1 1 1 =
      SqZeroPair.φ (R.E i) (R.F i) 1 1 1 0 := by
    rw [hp.φ_mul]
    simp only [mul_one, mul_zero, zero_add]
    rw [one_add_one_eq_two, hchar]
  have e3 : SqZeroPair.φ (R.E i) (R.F i) 1 1 1 0 * SqZeroPair.φ (R.E i) (R.F i) 0 1 1 1 =
      SqZeroPair.φ (R.E i) (R.F i) 1 0 0 1 := by
    rw [hp.φ_mul]
    simp only [mul_one, mul_zero, add_zero, zero_add]
    rw [one_add_one_eq_two, hchar]
  rw [pow_succ, pow_two]
  simp only [mat_mul, mat_x, mat_y, mat_one]
  rw [R.φ_xy hchar, e2, e3, SqZeroPair.φ_one_zero_zero_one]

theorem xy_not_commute (i : ι) : ¬ Commute (R.x i 1 * R.y i 1) (R.x i 1) := by
  intro h
  have hp := R.sqZero i
  have hm := congrArg R.mat h.eq
  simp only [mat_mul, mat_x, mat_y] at hm
  rw [R.φ_xy hchar, hp.φ_mul, hp.φ_mul] at hm
  simp only [mul_one, mul_zero, add_zero, zero_add] at hm
  rw [one_add_one_eq_two, hchar] at hm
  exact zero_ne_one (SqZeroPair.φ_injective hp (R.E_ne_zero i) hm).1

theorem three_witness {F : R.G →* R.G} {κ : Type*} [Fintype κ] [DecidableEq κ] (J : κ → ι)
    (hJ : Function.Injective J) (horth : ∀ a b, a ≠ b → R.CM (J a) (J b) = 0)
    (hxD : ∀ a, R.x (J a) 1 ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆)
    (hyD : ∀ a, R.y (J a) 1 ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆) (t : R.G)
    (htD : t ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆) (ht2 : t ^ 2 = 1)
    (htz : ∃ g ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆, t * g ≠ g * t)
    (htx : ∀ a, Commute t (R.x (J a) 1)) (hty : ∀ a, Commute t (R.y (J a) 1)) :
    HasWitness (DerivedCentralQuotient (fixedSubgroup F)) 3 (Fintype.card κ) := by
  let g : κ → R.G := fun a => R.x (J a) 1 * R.y (J a) 1
  have hg3 : ∀ a, g a ^ 3 = 1 := fun a => R.xy_pow_three hchar (J a)
  let ϕ : ∀ _ : κ, Multiplicative (ZMod 3) →* R.G := fun a =>
    { toFun := fun k => g a ^ (Multiplicative.toAdd k).val
      map_one' := by simp
      map_mul' := fun k l => by
        simp only [toAdd_mul]
        rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ (hg3 a)] }
  have hgg : ∀ a b, a ≠ b → Commute (g a) (g b) := fun a b hab => by
    have hJab : J a ≠ J b := fun h => hab (hJ h)
    exact ((R.commute_x_x (horth a b hab) _ _).mul_right (R.commute_x_y hJab _ _)).mul_left
      (((R.commute_x_y hJab.symm _ _).symm).mul_right (R.commute_y_y (horth a b hab) _ _))
  have hcomm : Pairwise fun a b => ∀ u v, Commute (ϕ a u) (ϕ b v) := fun a b hab u v =>
    (hgg a b hab).pow_pow _ _
  have hD : ∀ a u, ϕ a u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := fun a u =>
    Subgroup.pow_mem _ (Subgroup.mul_mem _ (hxD a) (hyD a)) _
  have hp : ∀ (a : κ) (u : ZMod 3), 3 • u = 0 := fun a u => by
    rw [nsmul_eq_mul, Nat.cast_ofNat, show (3 : ZMod 3) = 0 from rfl, zero_mul]
  have hcard : Nat.card (κ → Multiplicative (ZMod 3)) = 3 ^ Fintype.card κ := by
    rw [Nat.card_fun, Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 3) ≃ ZMod 3),
      Nat.card_zmod, Nat.card_eq_fintype_card]
  have hdet : ∀ a u, Commute (ϕ a u) (R.x (J a) 1) → u = 1 := fun a u h => by
    have hv := ZMod.val_lt (Multiplicative.toAdd u)
    change Commute (g a ^ (Multiplicative.toAdd u).val) (R.x (J a) 1) at h
    rcases (show (Multiplicative.toAdd u).val = 0 ∨ (Multiplicative.toAdd u).val = 1 ∨
        (Multiplicative.toAdd u).val = 2 by omega) with h0 | h1 | h2
    · rw [ZMod.val_eq_zero] at h0
      exact Multiplicative.toAdd.injective h0
    · rw [h1, pow_one] at h
      exact absurd h (R.xy_not_commute hchar (J a))
    · rw [h2] at h
      have h4 := h.pow_left 2
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hg3 a, one_mul, pow_one] at h4
      exact absurd h4 (R.xy_not_commute hchar (J a))
  have hoff : ∀ a b, a ≠ b → ∀ u, Commute (ϕ b u) (R.x (J a) 1) := fun a b hab u => by
    have hJab : J a ≠ J b := fun h => hab (hJ h)
    exact (((R.commute_x_x (horth b a (Ne.symm hab)) _ _).mul_left
      (R.commute_x_y hJab _ _).symm)).pow_left _
  have ht : ∀ a u, Commute t (ϕ a u) := fun a u => ((htx a).mul_right (hty a)).pow_right _
  exact family_witness ϕ hcomm hD hp hcard (fun a => R.x (J a) 1) hxD hdet hoff t htD ht2 htz ht

theorem three_witness_node {F : R.G →* R.G} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (J : κ → ι) (hJ : Function.Injective J) (horth : ∀ a b, a ≠ b → R.CM (J a) (J b) = 0)
    (hxD : ∀ a, R.x (J a) 1 ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆)
    (hyD : ∀ a, R.y (J a) 1 ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆) (k : ι) (hkJ : ∀ a, k ≠ J a)
    (hkorth : ∀ a, R.CM k (J a) = 0) (hkx : R.x k 1 ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆)
    (hky : R.y k 1 ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆) :
    HasWitness (DerivedCentralQuotient (fixedSubgroup F)) 3 (Fintype.card κ) := by
  have h11 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two]; exact hchar
  refine R.three_witness hchar J hJ horth hxD hyD (R.x k 1) hkx ?_
    ⟨R.y k 1, hky, fun h => (one_ne_zero : (1 : K) ≠ 0) (R.eq_zero_of_commute_x_y h)⟩
    (fun a => R.commute_x_x (hkorth a) _ _) (fun a => R.commute_x_y (hkJ a) _ _)
  rw [pow_two, ← x_add, h11, x_zero]

end Three

end RootData

end CFSG.RankThree.PartTwo.Census.Spin
