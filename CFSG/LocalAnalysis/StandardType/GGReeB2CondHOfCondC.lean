module

public import CFSG.LocalAnalysis.StandardType.GGReeB2WeightDefs
public import Mathlib.Combinatorics.Colex
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.StandardType.ReeB2Fixed

private theorem zmod_pow_succ {N : ℕ} (a : ZMod N) (n : ℕ) : a^(n+1) = a^n * a :=
  pow_succ a n

private theorem zmod_pow_mul_pow {N : ℕ} (a : ZMod N) (m n : ℕ) : a^m * a^n = a^(m+n) :=
  (pow_add a m n).symm

private theorem two_pow_e_eq_one (m : ℕ) :
    (2 : ZMod (2 ^ (2*m+1) - 1)) ^ (2*m+1) = 1 := by
  set N : ℕ := 2 ^ (2*m+1) - 1
  have hN : ((N : ℕ) : ZMod N) = 0 := ZMod.natCast_self N
  have hone : 1 ≤ 2 ^ (2*m+1) := Nat.one_le_two_pow
  have hsub : (2 ^ (2*m+1) - 1) + 1 = 2 ^ (2*m+1) := Nat.sub_add_cancel hone
  have h : ((2 ^ (2*m+1) : ℕ) : ZMod N) = 1 := by
    conv_lhs => rw [← hsub]
    rw [Nat.cast_add, Nat.cast_one, hN, zero_add]
  simpa [N, Nat.cast_pow] using h

private theorem mul_cancel_of_mul_eq_one {R : Type*} [CommRing R] {a b : R} (hab : a * b = 1)
    {x y : R} (h : a * x = a * y) : x = y := by
  calc x = 1 * x := (one_mul x).symm
    _ = (b * a) * x := by rw [mul_comm b a, hab]
    _ = b * (a * x) := by ring
    _ = b * (a * y) := by rw [h]
    _ = (b * a) * y := by ring
    _ = 1 * y := by rw [mul_comm b a, hab]
    _ = y := one_mul y

private theorem theta_mul_r (m : ℕ) :
    (2 : ZMod (2 ^ (2*m+1) - 1)) ^ m * 2 ^ (m+1) = 1 := by
  rw [zmod_pow_mul_pow, show m + (m+1) = 2*m+1 by omega, two_pow_e_eq_one]

private theorem pow_succ_test (m : ℕ) :
    (2 : ZMod (2 ^ (2*m+1) - 1))^(m+1) * 2^(m+1) = 2 := by
  have h2e := two_pow_e_eq_one m
  have h : (2 : ZMod (2 ^ (2*m+1) - 1))^(m+1) * 2^(m+1) =
      (2 : ZMod (2 ^ (2*m+1) - 1))^(m+1+(m+1)) := by rw [zmod_pow_mul_pow]
  rw [h, show m+1+(m+1) = (2*m+1)+1 by omega]
  rw [zmod_pow_succ]
  rw [h2e]
  norm_num

private theorem one_add_theta_mul_R (m : ℕ) :
    (1 + 2^m) * (R (2*m+1) * 2^(m+1)) = 1 := by
  have hR : R (2*m+1) = 2^(m+1) - 1 := by
    unfold R
    have hdiv : (2*m+1+1)/2 = m+1 := by omega
    rw [hdiv]
  have h2e := two_pow_e_eq_one m
  have h2a : (2 : ZMod (2 ^ (2*m+1) - 1)) * 2^m = 2^(m+1) := by
    calc (2 : ZMod (2 ^ (2*m+1) - 1)) * 2^m = 2^m * 2 := mul_comm _ _
      _ = 2^(m+1) := (zmod_pow_succ _ _).symm
  have hab : (2 : ZMod (2 ^ (2*m+1) - 1))^m * 2^(m+1) = 1 := theta_mul_r m
  have hsq : (2 : ZMod (2 ^ (2*m+1) - 1))^(m+1) * 2^(m+1) = 2 := pow_succ_test m
  rw [hR]
  calc ((1 : ZMod (2 ^ (2*m+1) - 1)) + 2^m) * ((2^(m+1) - 1) * 2^(m+1))
      = (1 + 2^m) * (2^(m+1) * 2^(m+1) - 2^(m+1)) := by ring
    _ = (1 + 2^m) * (2 - 2^(m+1)) := by rw [hsq]
    _ = 2 + 2 * 2^m - 2^(m+1) - 2^m * 2^(m+1) := by ring
    _ = 2 + 2^(m+1) - 2^(m+1) - 1 := by rw [h2a, hab]
    _ = 1 := by ring

private theorem one_add_theta_cancel (m : ℕ) {x y : ZMod (2 ^ (2*m+1) - 1)}
    (h : (1 + 2^m) * x = (1 + 2^m) * y) : x = y :=
  mul_cancel_of_mul_eq_one (one_add_theta_mul_R m) h

private theorem theta_cancel (m : ℕ) {x y : ZMod (2 ^ (2*m+1) - 1)}
    (h : (2:ZMod (2 ^ (2*m+1) - 1))^m * x = 2^m * y) : x = y :=
  mul_cancel_of_mul_eq_one (theta_mul_r m) h

private theorem theta_mul_eq_zero (m : ℕ) {x : ZMod (2 ^ (2*m+1) - 1)}
    (h : (2:ZMod (2 ^ (2*m+1) - 1))^m * x = 0) : x = 0 := by
  have h' : (2:ZMod (2 ^ (2*m+1) - 1))^m * x = 2^m * 0 := by rw [h, mul_zero]
  exact theta_cancel (m := m) h'

private theorem sum_range_two_pow (e : ℕ) : ∑ i ∈ Finset.range e, 2^i = 2^e - 1 := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have : 1 ≤ 2^e := Nat.one_le_two_pow
    omega


private theorem two_pow_pos_sub_one (e : ℕ) [NeZero e] : 0 < 2^e - 1 := by
  have h2 : 2 ≤ 2^e := by
    calc 2 = 2^1 := by norm_num
      _ ≤ 2^e := Nat.pow_le_pow_right (by norm_num) (NeZero.pos e)
  omega

private theorem val_lt_two_pow (e : ℕ) [NeZero e] (x : ZMod (2^e - 1)) : x.val < 2^e := by
  haveI : NeZero (2^e - 1) := ⟨by have := two_pow_pos_sub_one e; omega⟩
  have h := ZMod.val_lt x
  have hle : 2^e - 1 ≤ 2^e := Nat.sub_le _ _
  omega

private theorem S_digits (e : ℕ) [NeZero e] (x : ZMod (2^e - 1)) :
    S e (digits e x) = x := by
  haveI : NeZero (2^e - 1) := ⟨by have := two_pow_pos_sub_one e; omega⟩
  have hfilter : (Finset.range e).filter (fun i => x.val.testBit i) = x.val.bitIndices.toFinset := by
    ext i
    rw [Finset.mem_filter, Finset.mem_range, List.mem_toFinset, Nat.mem_bitIndices]
    constructor
    · rintro ⟨_, hbit⟩; exact hbit
    · intro hbit
      refine ⟨?_, hbit⟩
      by_contra hge
      push Not at hge
      have hle : 2^e ≤ 2^i := Nat.pow_le_pow_right (by norm_num) hge
      have hx : 2^i ≤ x.val := Nat.ge_two_pow_of_testBit hbit
      have hlt := val_lt_two_pow e x
      omega
  have hsum_nat : (∑ i ∈ (Finset.range e).filter (fun i => x.val.testBit i), 2^i) = x.val := by
    rw [hfilter]
    exact Finset.sum_toFinset_bitIndices_two_pow x.val
  have hsum_zmod : (∑ i ∈ (Finset.range e).filter (fun i => x.val.testBit i),
      (2 : ZMod (2^e - 1))^i) = (x.val : ZMod (2^e - 1)) := by
    have h := congrArg (fun n : ℕ => ((n : ZMod (2^e - 1)))) hsum_nat
    simpa [Nat.cast_sum, Nat.cast_pow] using h
  have hmap : (Finset.univ.filter (fun j : Fin e => x.val.testBit (j:ℕ))).map (Fin.valEmbedding)
      = (Finset.range e).filter (fun i => x.val.testBit i) := by
    ext i
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range,
      Fin.valEmbedding_apply]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨j.isLt, hj⟩
    · rintro ⟨hi, hbit⟩; exact ⟨⟨i, hi⟩, hbit, rfl⟩
  calc S e (digits e x)
      = ∑ j ∈ Finset.univ.filter (fun j : Fin e => x.val.testBit (j:ℕ)),
          (2:ZMod (2^e - 1))^(j:ℕ) := rfl
    _ = ∑ i ∈ (Finset.univ.filter (fun j : Fin e => x.val.testBit (j:ℕ))).map (Fin.valEmbedding),
          (2:ZMod (2^e - 1))^i := by
          rw [Finset.sum_map]
          simp [Fin.valEmbedding_apply]
    _ = ∑ i ∈ (Finset.range e).filter (fun i => x.val.testBit i),
          (2:ZMod (2^e - 1))^i := by rw [hmap]
    _ = (x.val : ZMod (2^e - 1)) := hsum_zmod
    _ = x := ZMod.natCast_zmod_val x

private theorem digits_S (e : ℕ) [NeZero e] (A : Finset (Fin e))
    (hA : A ≠ Finset.univ) : digits e (S e A) = A := by
  haveI : NeZero (2^e - 1) := ⟨by have := two_pow_pos_sub_one e; omega⟩
  set n : ℕ := ∑ j ∈ A, 2^(j:ℕ) with hn
  have hS : S e A = (n : ZMod (2^e - 1)) := by
    rw [S, hn]
    push_cast
    rfl
  have hlt : n < 2^e - 1 := by
    obtain ⟨j0, hj0⟩ : ∃ j0 : Fin e, j0 ∉ A := by
      by_contra h
      push Not at h
      exact hA (Finset.eq_univ_of_forall h)
    have hsum_univ : (∑ j : Fin e, 2^(j:ℕ)) = 2^e - 1 := by
      rw [Fin.sum_univ_eq_sum_range]
      exact sum_range_two_pow e
    have h2j : 0 < 2^(j0:ℕ) := Nat.two_pow_pos _
    have hle : n + 2^(j0:ℕ) ≤ 2^e - 1 := by
      have h1 : n + 2^(j0:ℕ) = ∑ j ∈ insert j0 A, 2^(j:ℕ) := by
        rw [Finset.sum_insert hj0, hn]; omega
      rw [h1, ← hsum_univ]
      exact Finset.sum_le_sum_of_subset (Finset.insert_subset_iff.mpr ⟨Finset.mem_univ _, Finset.subset_univ A⟩)
    omega
  have hval : (S e A).val = n := by
    rw [hS]
    exact ZMod.val_natCast_of_lt hlt
  have hn_bits : n.bitIndices.toFinset = A.map (Fin.valEmbedding) := by
    have h : n = ∑ i ∈ A.map (Fin.valEmbedding), 2^i := by
      rw [hn, Finset.sum_map]
      simp [Fin.valEmbedding_apply]
    rw [h]
    exact Finset.toFinset_bitIndices_sum_two_pow _
  rw [digits, hval]
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset, Nat.mem_bitIndices,
    Finset.mem_map, Fin.valEmbedding_apply]
  constructor
  · intro hbit
    have hmem : (j:ℕ) ∈ n.bitIndices.toFinset := by simpa using hbit
    rw [hn_bits, Finset.mem_map] at hmem
    rcases hmem with ⟨k, hk, hkval⟩
    have hkj : k = j := Fin.ext hkval
    simpa [hkj] using hk
  · intro hj
    have hmem : (j:ℕ) ∈ n.bitIndices.toFinset := by
      rw [hn_bits]
      exact Finset.mem_map.mpr ⟨j, hj, rfl⟩
    simpa using hmem

private theorem digits_ne_univ (e : ℕ) [NeZero e] (x : ZMod (2^e - 1)) :
    digits e x ≠ Finset.univ := by
  haveI : NeZero (2^e - 1) := ⟨by have := two_pow_pos_sub_one e; omega⟩
  intro h
  have hbits : ∀ j : Fin e, x.val.testBit (j:ℕ) := by
    intro j
    have : j ∈ digits e x := by rw [h]; exact Finset.mem_univ j
    simpa [digits] using this
  have hsubset : Finset.range e ⊆ x.val.bitIndices.toFinset := by
    intro i hi
    rw [List.mem_toFinset, Nat.mem_bitIndices]
    exact hbits ⟨i, Finset.mem_range.mp hi⟩
  have hle : ∑ i ∈ Finset.range e, 2^i ≤ x.val := by
    rw [← Finset.sum_toFinset_bitIndices_two_pow x.val]
    exact Finset.sum_le_sum_of_subset hsubset
  rw [sum_range_two_pow e] at hle
  have hlt := ZMod.val_lt x
  omega


private theorem zero_mem_lam_univ (e : ℕ) [NeZero e] :
    (0 : ZMod (2^e - 1)) ∈ Lam e Finset.univ := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro j _; simp [units]
  · have hnat : (∑ j : Fin e, 2^(j:ℕ)) = 2^e - 1 := by
      rw [Fin.sum_univ_eq_sum_range]
      exact sum_range_two_pow e
    have hcast : (∑ j : Fin e, (2:ZMod (2^e-1))^(j:ℕ)) = 0 := by
      have h : ((∑ j : Fin e, 2^(j:ℕ) : ℕ) : ZMod (2^e-1)) = 0 := by
        rw [hnat]; exact ZMod.natCast_self _
      simpa [Nat.cast_sum, Nat.cast_pow] using h
    simpa using hcast.symm

private theorem not_good_univ (e : ℕ) [NeZero e] : ¬ Good e Finset.univ :=
  fun h => h (zero_mem_lam_univ e)

private theorem good_ne_univ {e : ℕ} [NeZero e] {A : Finset (Fin e)}
    (h : Good e A) : A ≠ Finset.univ := by
  rintro rfl
  exact not_good_univ e h

private noncomputable def rho (m : ℕ) : Equiv.Perm (Fin (2*m+1)) :=
  Equiv.addRight (⟨m % (2*m+1), Nat.mod_lt _ (by omega)⟩ : Fin (2*m+1))

private theorem rho_apply_val (m : ℕ) (p : Fin (2*m+1)) :
    ((rho m p : Fin (2*m+1)) : ℕ) = (p.val + m) % (2*m+1) := by
  unfold rho
  rw [Equiv.coe_addRight, Fin.val_add]
  simp only [Fin.val_mk]
  rw [Nat.add_mod_mod]

private theorem zmod_pow_add {N : ℕ} (a : ZMod N) (m n : ℕ) : a^(m+n) = a^m * a^n :=
  pow_add a m n

private theorem pow_rho (m : ℕ) (p : Fin (2*m+1)) :
    (2 : ZMod (2^(2*m+1)-1))^(((rho m p : Fin (2*m+1)) : ℕ)) =
      (2:ZMod (2^(2*m+1)-1))^m * (2:ZMod (2^(2*m+1)-1))^(p:ℕ) := by
  have h2e := two_pow_e_eq_one m
  have hmod := rho_apply_val m p
  have hpow : (2 : ZMod (2^(2*m+1)-1))^(((rho m p : Fin (2*m+1)) : ℕ)) =
      (2 : ZMod (2^(2*m+1)-1))^(p.val + m) := by
    rw [hmod]
    exact (pow_eq_pow_mod (a := (2 : ZMod (2^(2*m+1)-1))) (n := 2*m+1) (p.val + m) h2e).symm
  calc (2 : ZMod (2^(2*m+1)-1))^(((rho m p : Fin (2*m+1)) : ℕ))
      = (2 : ZMod (2^(2*m+1)-1))^(p.val + m) := hpow
    _ = (2 : ZMod (2^(2*m+1)-1))^p.val * (2 : ZMod (2^(2*m+1)-1))^m := by
          rw [zmod_pow_add]
    _ = (2 : ZMod (2^(2*m+1)-1))^m * (2 : ZMod (2^(2*m+1)-1))^p.val := by ring
    _ = (2 : ZMod (2^(2*m+1)-1))^m * (2 : ZMod (2^(2*m+1)-1))^(p:ℕ) := rfl

private theorem S_rho (m : ℕ) (A : Finset (Fin (2*m+1))) :
    S (2*m+1) (A.map (rho m).toEmbedding) =
      (2:ZMod (2^(2*m+1)-1))^m * S (2*m+1) A := by
  rw [S, S, Finset.mul_sum, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro p hp
  exact pow_rho m p

private theorem Lam_rho (m : ℕ) (A : Finset (Fin (2*m+1))) :
    Lam (2*m+1) (A.map (rho m).toEmbedding) =
      (fun y => (2:ZMod (2^(2*m+1)-1))^m * y) '' Lam (2*m+1) A := by
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨∑ j ∈ A, c (rho m j) * (2:ZMod (2^(2*m+1)-1))^(j:ℕ),
      ⟨fun j => c (rho m j), ?_, rfl⟩, ?_⟩
    · intro j hj
      exact hc (rho m j) (Finset.mem_map.mpr ⟨j, hj, rfl⟩)
    · show (2:ZMod (2^(2*m+1)-1))^m *
          (∑ j ∈ A, c (rho m j) * (2:ZMod (2^(2*m+1)-1))^(j:ℕ)) =
        ∑ k ∈ A.map (rho m).toEmbedding, c k * (2:ZMod (2^(2*m+1)-1))^(k:ℕ)
      rw [Finset.mul_sum, Finset.sum_map]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Equiv.coe_toEmbedding]
      rw [pow_rho m j]
      ring
  · rintro ⟨y, ⟨c, hc, rfl⟩, hxy⟩
    rw [← hxy]
    refine ⟨fun k => c ((rho m).symm k), ?_, ?_⟩
    · intro k hk
      rw [Finset.mem_map] at hk
      obtain ⟨j, hj, rfl⟩ := hk
      simpa using hc j hj
    · show (2:ZMod (2^(2*m+1)-1))^m *
          (∑ j ∈ A, c j * (2:ZMod (2^(2*m+1)-1))^(j:ℕ)) =
        ∑ k ∈ A.map (rho m).toEmbedding,
          c ((rho m).symm k) * (2:ZMod (2^(2*m+1)-1))^(k:ℕ)
      rw [Finset.mul_sum, Finset.sum_map]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
      rw [pow_rho m j]
      ring

private theorem Good_rho (m : ℕ) (A : Finset (Fin (2*m+1))) :
    Good (2*m+1) (A.map (rho m).toEmbedding) ↔ Good (2*m+1) A := by
  unfold Good
  rw [Lam_rho]
  constructor
  · intro h hy
    exact h ⟨0, hy, by simp⟩
  · rintro h ⟨y, hy, hxy⟩
    exact h (by rw [theta_mul_eq_zero m hxy] at hy; exact hy)

private theorem Disjoint_rho (m : ℕ) (A B : Finset (Fin (2*m+1))) :
    Disjoint (Lam (2*m+1) (A.map (rho m).toEmbedding))
        (Lam (2*m+1) (B.map (rho m).toEmbedding)) ↔
      Disjoint (Lam (2*m+1) A) (Lam (2*m+1) B) := by
  rw [Lam_rho, Lam_rho]
  constructor
  · intro h
    rw [Set.disjoint_left] at h ⊢
    intro x hx hy
    exact h ⟨x, hx, rfl⟩ ⟨x, hy, rfl⟩
  · intro h
    rw [Set.disjoint_left] at h ⊢
    rintro z ⟨x, hx, hzx⟩ ⟨y, hy, hzy⟩
    have hxy : x = y := theta_cancel m (hzx.trans hzy.symm)
    exact h hx (by rw [← hxy] at hy; exact hy)

private theorem Admissible_rho (m : ℕ) (A B : Finset (Fin (2*m+1))) :
    Admissible (2*m+1) (A.map (rho m).toEmbedding) (B.map (rho m).toEmbedding) ↔
      Admissible (2*m+1) A B := by
  unfold Admissible
  rw [Good_rho, Good_rho, Disjoint_rho]


theorem condH_of_condC (m : ℕ) (h : CondC (2 * m + 1)) : CondH m := by
  intro I J hIJ
  obtain ⟨κ₀, hκ₀, hnot⟩ := h I J hIJ
  refine ⟨(1 + 2^m) * κ₀, ⟨κ₀, hκ₀, rfl⟩, ?_⟩
  intro I' J' hEq hAdm
  set U : Finset (Fin (2*m+1)) := digits (2*m+1) (S (2*m+1) J - κ₀) with hU
  set V : Finset (Fin (2*m+1)) := digits (2*m+1) (S (2*m+1) J + κ₀) with hV
  have hnot' : ¬ Admissible (2*m+1) U V := by rw [hU, hV]; exact hnot
  rw [Prod.mk.injEq] at hEq
  obtain ⟨hI', hJ'⟩ := hEq
  unfold hw sa at hI' hJ'
  have hSI : S (2*m+1) I' = 2^m * (S (2*m+1) J - κ₀) := by
    apply one_add_theta_cancel m
    rw [hI']
    ring
  have hSJ : S (2*m+1) J' = 2^m * (κ₀ + S (2*m+1) J) := by
    apply one_add_theta_cancel m
    rw [hJ']
    ring
  have hSU : S (2*m+1) (U.map (rho m).toEmbedding) = S (2*m+1) I' := by
    rw [S_rho, hU, S_digits, hSI]
  have hSV : S (2*m+1) (V.map (rho m).toEmbedding) = S (2*m+1) J' := by
    rw [S_rho, hV, S_digits, hSJ]
    ring
  have hUU : U.map (rho m).toEmbedding ≠ Finset.univ := by
    intro hmap
    have hcard : U.card = Fintype.card (Fin (2*m+1)) := by
      have := congrArg Finset.card hmap
      rwa [Finset.card_map, Finset.card_univ] at this
    have hUuniv : U = Finset.univ := Finset.eq_univ_of_card U hcard
    exact digits_ne_univ (2*m+1) (S (2*m+1) J - κ₀) (by rw [← hU]; exact hUuniv)
  have hVV : V.map (rho m).toEmbedding ≠ Finset.univ := by
    intro hmap
    have hcard : V.card = Fintype.card (Fin (2*m+1)) := by
      have := congrArg Finset.card hmap
      rwa [Finset.card_map, Finset.card_univ] at this
    have hVuniv : V = Finset.univ := Finset.eq_univ_of_card V hcard
    exact digits_ne_univ (2*m+1) (S (2*m+1) J + κ₀) (by rw [← hV]; exact hVuniv)
  have hI'map : I' = U.map (rho m).toEmbedding := by
    have hIU : I' ≠ Finset.univ := good_ne_univ hAdm.1
    calc I' = digits (2*m+1) (S (2*m+1) I') := (digits_S (2*m+1) I' hIU).symm
      _ = digits (2*m+1) (S (2*m+1) (U.map (rho m).toEmbedding)) := by rw [← hSU]
      _ = U.map (rho m).toEmbedding := digits_S (2*m+1) (U.map (rho m).toEmbedding) hUU
  have hJ'map : J' = V.map (rho m).toEmbedding := by
    have hJU : J' ≠ Finset.univ := good_ne_univ hAdm.2.1
    calc J' = digits (2*m+1) (S (2*m+1) J') := (digits_S (2*m+1) J' hJU).symm
      _ = digits (2*m+1) (S (2*m+1) (V.map (rho m).toEmbedding)) := by rw [← hSV]
      _ = V.map (rho m).toEmbedding := digits_S (2*m+1) (V.map (rho m).toEmbedding) hVV
  have hAdm_rho : Admissible (2*m+1) (U.map (rho m).toEmbedding) (V.map (rho m).toEmbedding) := by
    rwa [← hI'map, ← hJ'map]
  exact hnot' ((Admissible_rho m U V).mp hAdm_rho)


end CFSG.StandardType.ReeB2Fixed
