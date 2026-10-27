module

public import CFSG.Quasithin.Background.G2UCodes

public section

namespace CFSG.Quasithin.G11.P3G2

open CFSG.Quasithin.G2U

@[expose] def B9 : ℕ := 387420489

@[expose] def ofChunks (l : List ℕ) : ℕ :=
  l.foldr (fun c acc => c + acc <<< 320) 0

@[expose] def rowDec3 (r : ℕ) : Fin 3 → F9 :=
  fun j => dec9 (r / 9 ^ (j : ℕ) % 9)

@[expose] def rowDec8 (r : ℕ) : Fin 8 → ZMod 2 :=
  fun j => bz (r.testBit j)

@[expose] def matDec3 (m : ℕ) : Matrix (Fin 3) (Fin 3) F9 :=
  Matrix.of fun i => rowDec3 (m / 729 ^ (i : ℕ) % 729)

@[expose] def matDec8 (m : ℕ) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun i => rowDec8 (m / 256 ^ (i : ℕ) % 256)

@[expose] def decK (k : ℕ) : Matrix (Fin 8) (Fin 8) (ZMod 2) × Matrix (Fin 3) (Fin 3) F9 :=
  (matDec8 (k / B9), matDec3 (k % B9))

private theorem dec9_inj : ∀ x < 9, ∀ y < 9, dec9 x = dec9 y → x = y := by
  decide

private theorem bz_inj : Function.Injective bz := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem rowDec3_injective {r r' : ℕ} (hr : r < 729) (hr' : r' < 729)
    (h : rowDec3 r = rowDec3 r') : r = r' := by
  have e0 := dec9_inj _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num))
    (congrFun h 0)
  have e1 := dec9_inj _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num))
    (congrFun h 1)
  have e2 := dec9_inj _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num))
    (congrFun h 2)
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, Nat.div_one] at e0 e1 e2
  norm_num at e2
  omega

theorem rowDec8_injective {r r' : ℕ} (hr : r < 256) (hr' : r' < 256)
    (h : rowDec8 r = rowDec8 r') : r = r' := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  by_cases hj : j < 8
  · exact bz_inj (congrFun h ⟨j, hj⟩)
  · have h2 : 2 ^ 8 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hj)
    rw [Nat.testBit_eq_false_of_lt (by omega), Nat.testBit_eq_false_of_lt (by omega)]

theorem matDec3_injective {m m' : ℕ} (hm : m < B9) (hm' : m' < B9)
    (h : matDec3 m = matDec3 m') : m = m' := by
  have hb : ∀ i : Fin 3, m / 729 ^ (i : ℕ) % 729 = m' / 729 ^ (i : ℕ) % 729 := fun i =>
    rowDec3_injective (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (congrFun h i)
  have b0 := hb 0
  have b1 := hb 1
  have b2 := hb 2
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, Nat.div_one] at b0 b1 b2
  norm_num at b2
  rw [B9] at hm hm'
  omega

theorem matDec8_injective {m m' : ℕ} (hm : m < 2 ^ 64) (hm' : m' < 2 ^ 64)
    (h : matDec8 m = matDec8 m') : m = m' := by
  have hb : ∀ i : Fin 8, m / 256 ^ (i : ℕ) % 256 = m' / 256 ^ (i : ℕ) % 256 := fun i =>
    rowDec8_injective (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (congrFun h i)
  have b0 := hb 0
  have b1 := hb 1
  have b2 := hb 2
  have b3 := hb 3
  have b4 := hb 4
  have b5 := hb 5
  have b6 := hb 6
  have b7 := hb 7
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
    Nat.div_one] at b0 b1 b2 b3 b4 b5 b6 b7
  norm_num at b2 b3 b4 b5 b6 b7 hm hm'
  omega

theorem decK_injective {k k' : ℕ} (hk : k / B9 < 2 ^ 64) (hk' : k' / B9 < 2 ^ 64)
    (h : decK k = decK k') : k = k' := by
  simp only [decK, Prod.mk.injEq] at h
  have h1 := matDec8_injective hk hk' h.1
  have h2 := matDec3_injective (Nat.mod_lt _ (by norm_num [B9])) (Nat.mod_lt _ (by norm_num [B9]))
    h.2
  rw [← Nat.div_add_mod k B9, ← Nat.div_add_mod k' B9, h1, h2]

@[expose] def look3 (T r : ℕ) : ℕ :=
  T >>> (10 * r) % 1024

@[expose] def rmul3 (T m : ℕ) : ℕ :=
  look3 T (m % 729) + 729 * look3 T (m / 729 % 729) + 531441 * look3 T (m / 531441 % 729)

@[expose] def look8 (T r : ℕ) : ℕ :=
  T >>> (8 * r) % 256

@[expose] def rmul8 (T m : ℕ) : ℕ :=
  look8 T (m % 256) + 256 * look8 T (m / 256 % 256) + 65536 * look8 T (m / 65536 % 256) +
    16777216 * look8 T (m / 16777216 % 256) + 4294967296 * look8 T (m / 4294967296 % 256) +
    1099511627776 * look8 T (m / 1099511627776 % 256) +
    281474976710656 * look8 T (m / 281474976710656 % 256) +
    72057594037927936 * look8 T (m / 72057594037927936 % 256)

theorem matDec3_rmul3 {T : ℕ} {Gm : Matrix (Fin 3) (Fin 3) F9}
    (hT : ∀ r < 729, look3 T r < 729 ∧ rowDec3 (look3 T r) = Matrix.vecMul (rowDec3 r) Gm)
    (m : ℕ) : rmul3 T m < B9 ∧ matDec3 (rmul3 T m) = matDec3 m * Gm := by
  have h0 := hT (m % 729) (Nat.mod_lt _ (by norm_num))
  have h1 := hT (m / 729 % 729) (Nat.mod_lt _ (by norm_num))
  have h2 := hT (m / 531441 % 729) (Nat.mod_lt _ (by norm_num))
  set a0 := look3 T (m % 729) with ha0
  set a1 := look3 T (m / 729 % 729) with ha1
  set a2 := look3 T (m / 531441 % 729) with ha2
  have hr : rmul3 T m = a0 + 729 * a1 + 531441 * a2 := rfl
  refine ⟨by rw [hr, B9]; omega, ?_⟩
  rw [hr]
  have key1 : ∀ i : Fin 3,
      (a0 + 729 * a1 + 531441 * a2) / 729 ^ (i : ℕ) % 729 = ![a0, a1, a2] i := by
    intro i
    fin_cases i <;> simp <;> omega
  have key2 : ∀ i : Fin 3,
      m / 729 ^ (i : ℕ) % 729 = ![m % 729, m / 729 % 729, m / 531441 % 729] i := by
    intro i
    fin_cases i <;> simp
  have hrows : ∀ i : Fin 3, rowDec3 (![a0, a1, a2] i) =
      Matrix.vecMul (rowDec3 (![m % 729, m / 729 % 729, m / 531441 % 729] i)) Gm := by
    intro i
    fin_cases i
    · exact h0.2
    · exact h1.2
    · exact h2.2
  funext i
  show rowDec3 ((a0 + 729 * a1 + 531441 * a2) / 729 ^ (i : ℕ) % 729) =
    Matrix.vecMul (rowDec3 (m / 729 ^ (i : ℕ) % 729)) Gm
  rw [key1 i, key2 i]
  exact hrows i

theorem matDec8_rmul8 {T : ℕ} {Gb : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (hT : ∀ r < 256, look8 T r < 256 ∧ rowDec8 (look8 T r) = Matrix.vecMul (rowDec8 r) Gb)
    (m : ℕ) : matDec8 (rmul8 T m) = matDec8 m * Gb := by
  have h0 := hT (m % 256) (Nat.mod_lt _ (by norm_num))
  have h1 := hT (m / 256 % 256) (Nat.mod_lt _ (by norm_num))
  have h2 := hT (m / 65536 % 256) (Nat.mod_lt _ (by norm_num))
  have h3 := hT (m / 16777216 % 256) (Nat.mod_lt _ (by norm_num))
  have h4 := hT (m / 4294967296 % 256) (Nat.mod_lt _ (by norm_num))
  have h5 := hT (m / 1099511627776 % 256) (Nat.mod_lt _ (by norm_num))
  have h6 := hT (m / 281474976710656 % 256) (Nat.mod_lt _ (by norm_num))
  have h7 := hT (m / 72057594037927936 % 256) (Nat.mod_lt _ (by norm_num))
  set a0 := look8 T (m % 256) with ha0
  set a1 := look8 T (m / 256 % 256) with ha1
  set a2 := look8 T (m / 65536 % 256) with ha2
  set a3 := look8 T (m / 16777216 % 256) with ha3
  set a4 := look8 T (m / 4294967296 % 256) with ha4
  set a5 := look8 T (m / 1099511627776 % 256) with ha5
  set a6 := look8 T (m / 281474976710656 % 256) with ha6
  set a7 := look8 T (m / 72057594037927936 % 256) with ha7
  have hr : rmul8 T m = a0 + 256 * a1 + 65536 * a2 + 16777216 * a3 + 4294967296 * a4 +
      1099511627776 * a5 + 281474976710656 * a6 + 72057594037927936 * a7 := rfl
  rw [hr]
  have key1 : ∀ i : Fin 8,
      (a0 + 256 * a1 + 65536 * a2 + 16777216 * a3 + 4294967296 * a4 + 1099511627776 * a5 +
        281474976710656 * a6 + 72057594037927936 * a7) / 256 ^ (i : ℕ) % 256 =
        ![a0, a1, a2, a3, a4, a5, a6, a7] i := by
    intro i
    fin_cases i <;> simp <;> omega
  have key2 : ∀ i : Fin 8,
      m / 256 ^ (i : ℕ) % 256 = ![m % 256, m / 256 % 256, m / 65536 % 256, m / 16777216 % 256,
        m / 4294967296 % 256, m / 1099511627776 % 256, m / 281474976710656 % 256,
        m / 72057594037927936 % 256] i := by
    intro i
    fin_cases i <;> simp
  have hrows : ∀ i : Fin 8, rowDec8 (![a0, a1, a2, a3, a4, a5, a6, a7] i) =
      Matrix.vecMul (rowDec8 (![m % 256, m / 256 % 256, m / 65536 % 256, m / 16777216 % 256,
        m / 4294967296 % 256, m / 1099511627776 % 256, m / 281474976710656 % 256,
        m / 72057594037927936 % 256] i)) Gb := by
    intro i
    fin_cases i
    · exact h0.2
    · exact h1.2
    · exact h2.2
    · exact h3.2
    · exact h4.2
    · exact h5.2
    · exact h6.2
    · exact h7.2
  funext i
  show rowDec8 ((a0 + 256 * a1 + 65536 * a2 + 16777216 * a3 + 4294967296 * a4 +
      1099511627776 * a5 + 281474976710656 * a6 + 72057594037927936 * a7) / 256 ^ (i : ℕ) % 256) =
    Matrix.vecMul (rowDec8 (m / 256 ^ (i : ℕ) % 256)) Gb
  rw [key1 i, key2 i]
  exact hrows i

@[expose] def rmulK (T3 T8 k : ℕ) : ℕ :=
  rmul3 T3 (k % B9) + B9 * rmul8 T8 (k / B9)

theorem decK_rmulK {T3 T8 : ℕ} {Gm : Matrix (Fin 3) (Fin 3) F9}
    {Gb : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (h3 : ∀ r < 729, look3 T3 r < 729 ∧ rowDec3 (look3 T3 r) = Matrix.vecMul (rowDec3 r) Gm)
    (h8 : ∀ r < 256, look8 T8 r < 256 ∧ rowDec8 (look8 T8 r) = Matrix.vecMul (rowDec8 r) Gb)
    (k : ℕ) : decK (rmulK T3 T8 k) = decK k * (Gb, Gm) := by
  obtain ⟨hlt, hmat⟩ := matDec3_rmul3 h3 (k % B9)
  have hmat8 := matDec8_rmul8 h8 (k / B9)
  have e1 : rmulK T3 T8 k / B9 = rmul8 T8 (k / B9) := by
    rw [rmulK]
    rw [B9] at hlt ⊢
    omega
  have e2 : rmulK T3 T8 k % B9 = rmul3 T3 (k % B9) := by
    rw [rmulK]
    rw [B9] at hlt ⊢
    omega
  simp only [decK, e1, e2, hmat, hmat8, Prod.mk_mul_mk]

@[expose] def id3p : ℕ := 1 + 9 ^ 4 + 9 ^ 8

@[expose] def id8p : ℕ :=
  1 + 2 * 256 + 4 * 256 ^ 2 + 8 * 256 ^ 3 + 16 * 256 ^ 4 + 32 * 256 ^ 5 + 64 * 256 ^ 6 +
    128 * 256 ^ 7

@[expose] def oneK : ℕ := id3p + B9 * id8p

theorem matDec3_id3p : matDec3 id3p = 1 := by
  decide +kernel

theorem matDec8_id8p : matDec8 id8p = 1 := by
  decide +kernel

theorem id3p_lt : id3p < B9 := by
  norm_num [id3p, B9]

theorem id8p_lt : id8p < 2 ^ 64 := by
  norm_num [id8p]

theorem decK_oneK : decK oneK = 1 := by
  have h1 : oneK / B9 = id8p := by
    have := id3p_lt
    rw [oneK]
    rw [B9] at this ⊢
    omega
  have h2 : oneK % B9 = id3p := by
    have := id3p_lt
    rw [oneK]
    rw [B9] at this ⊢
    omega
  simp only [decK, h1, h2, matDec3_id3p, matDec8_id8p, Prod.mk_one_one]

theorem matDec8_eq_one_iff {m : ℕ} (hm : m < 2 ^ 64) : matDec8 m = 1 ↔ m = id8p :=
  ⟨fun h => matDec8_injective hm id8p_lt (h.trans matDec8_id8p.symm),
    fun h => h ▸ matDec8_id8p⟩

theorem matDec3_eq_one_iff {m : ℕ} (hm : m < B9) : matDec3 m = 1 ↔ m = id3p :=
  ⟨fun h => matDec3_injective hm id3p_lt (h.trans matDec3_id3p.symm),
    fun h => h ▸ matDec3_id3p⟩

end CFSG.Quasithin.G11.P3G2
