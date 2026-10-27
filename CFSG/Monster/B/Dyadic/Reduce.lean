module

public import CFSG.Monster.B.Dyadic.Contain
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Monster.B.Dyadic

open CFSG.Monster.B.Dyadic.Native

@[expose] def z32 (x : UInt32) : ZMod 4294967296 := (x.toNat : ZMod 4294967296)

theorem z32_add (x y : UInt32) : z32 (x + y) = z32 x + z32 y := by
  unfold z32
  rw [UInt32.toNat_add, show (2 : ℕ) ^ 32 = 4294967296 by norm_num, ZMod.natCast_mod,
    Nat.cast_add]

theorem z32_mul (x y : UInt32) : z32 (x * y) = z32 x * z32 y := by
  unfold z32
  rw [UInt32.toNat_mul, show (2 : ℕ) ^ 32 = 4294967296 by norm_num, ZMod.natCast_mod,
    Nat.cast_mul]

theorem z32_toU32 (m : ℤ) : z32 (toU32 m) = (m : ZMod 4294967296) := by
  unfold z32 toU32
  have h0 : 0 ≤ m % 4294967296 := Int.emod_nonneg _ (by norm_num)
  have h1 : m % 4294967296 < 4294967296 := Int.emod_lt_of_pos _ (by norm_num)
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), ← Int.cast_natCast,
    Int.toNat_of_nonneg h0, show (4294967296 : ℤ) = ((4294967296 : ℕ) : ℤ) by norm_num,
    ZMod.intCast_mod]

theorem z32_toUInt32 (b : UInt8) : z32 b.toUInt32 = (b.toNat : ZMod 4294967296) := by
  unfold z32
  rw [UInt8.toNat_toUInt32]

@[expose] def entrySum (l : List (ℕ × UInt32)) (u : ℕ) : ZMod 4294967296 :=
  (l.map fun e => if e.1 = u then z32 e.2 else 0).sum

theorem addRow_size (b : UInt32) (l : List (ℕ × UInt32)) :
    ∀ acc : Array UInt32, (addRow acc b l).size = acc.size := by
  induction l with
  | nil => intro acc; rfl
  | cons e l ih =>
    intro acc
    obtain ⟨u, m⟩ := e
    simp only [addRow]
    rw [ih, Array.size_modify]

theorem addRow_get (b : UInt32) (l : List (ℕ × UInt32)) :
    ∀ (acc : Array UInt32) (u : ℕ), u < acc.size →
      z32 (addRow acc b l)[u]! = z32 acc[u]! + z32 b * entrySum l u := by
  induction l with
  | nil => intro acc u hu; simp [addRow, entrySum]
  | cons e l ih =>
    intro acc u hu
    obtain ⟨u', m⟩ := e
    simp only [addRow]
    rw [ih _ u (by rw [Array.size_modify]; exact hu),
      getElem!_pos (acc.modify u' (· + b * m)) u (by rw [Array.size_modify]; exact hu),
      Array.getElem_modify, getElem!_pos acc u hu]
    simp only [entrySum, List.map_cons, List.sum_cons]
    by_cases h : u' = u
    · rw [ite_eq_left h, ite_eq_left h, z32_add, z32_mul]
      ring
    · rw [ite_eq_right h, ite_eq_right h]
      ring

theorem mulGo_size (M : Array (Array (ℕ × UInt32))) (rowI : ByteArray) (n : ℕ) :
    ∀ t (acc : Array UInt32), (mulGo M rowI n t acc).size = acc.size := by
  intro t
  induction h : n - t generalizing t with
  | zero =>
    intro acc
    rw [mulGo, ite_eq_right (by omega)]
  | succ d ih =>
    intro acc
    rw [mulGo, ite_eq_left (by omega)]
    simp only
    rw [ih (t + 1) (by omega)]
    split
    · rfl
    · exact addRow_size _ _ _

theorem mulGo_get (M : Array (Array (ℕ × UInt32))) (rowI : ByteArray) (n : ℕ) :
    ∀ t (acc : Array UInt32) (u : ℕ), u < acc.size →
      z32 (mulGo M rowI n t acc)[u]! = z32 acc[u]! + ∑ s ∈ Finset.Ico t n,
        ((rowI.get! s).toNat : ZMod 4294967296) * entrySum (M[s]!).toList u := by
  intro t
  induction h : n - t generalizing t with
  | zero =>
    intro acc u _
    rw [mulGo, ite_eq_right (by omega), Finset.Ico_eq_empty (by omega), Finset.sum_empty,
      add_zero]
  | succ d ih =>
    intro acc u hu
    have ht : t < n := by omega
    rw [mulGo, ite_eq_left ht]
    simp only
    have hsz : (if rowI.get! t == 0 then acc
        else addRow acc (rowI.get! t).toUInt32 (M[t]!).toList).size = acc.size := by
      split
      · rfl
      · exact addRow_size _ _ _
    rw [ih (t + 1) (by omega) _ u (by rw [hsz]; exact hu), Finset.sum_eq_sum_Ico_succ_bot ht]
    split
    · next h0 =>
      rw [beq_iff_eq] at h0
      rw [h0]
      simp
    · rw [addRow_get _ _ _ u hu, z32_toUInt32]
      ring

theorem wRow_arith (sh : ℕ) (hsh : sh ≤ 24) (a : ℕ) (X : ℤ)
    (h : (a : ZMod 4294967296) = (X : ZMod 4294967296)) (h8 : a % 2 ^ sh = 0) :
    (2 ^ sh : ℤ) ∣ X ∧ (((a >>> sh) % 256 : ℕ) : ZMod 256) = ((X / 2 ^ sh : ℤ) : ZMod 256) := by
  have hd : ((4294967296 : ℕ) : ℤ) ∣ X - a := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, Int.cast_natCast]
    exact h
  obtain ⟨k, hk⟩ := hd
  obtain ⟨a', ha'⟩ := Nat.dvd_of_mod_eq_zero h8
  have e32 : ((4294967296 : ℕ) : ℤ) = 2 ^ sh * (256 * 2 ^ (24 - sh)) := by
    have : ((4294967296 : ℕ) : ℤ) = 2 ^ (sh + (8 + (24 - sh))) := by
      rw [show sh + (8 + (24 - sh)) = 32 by omega]
      norm_num
    rw [this, pow_add, pow_add]
    norm_num
  have hX : X = 2 ^ sh * ((a' : ℤ) + 256 * 2 ^ (24 - sh) * k) := by
    have : X = a + ((4294967296 : ℕ) : ℤ) * k := by linarith
    rw [this, e32, ha']
    push_cast
    ring
  have hpos : (2 : ℤ) ^ sh ≠ 0 := by positivity
  refine ⟨⟨_, hX⟩, ?_⟩
  rw [Nat.shiftRight_eq_div_pow, ha', Nat.mul_div_cancel_left _ (by positivity), ZMod.natCast_mod,
    hX, Int.mul_ediv_cancel_left _ hpos, ← Int.cast_natCast, ZMod.intCast_eq_intCast_iff_dvd_sub]
  exact ⟨2 ^ (24 - sh) * k, by push_cast; ring⟩

theorem wRow_spec (sh : ℕ) (hsh : sh ≤ 24) (rows : Array ByteArray)
    (M : Array (Array (ℕ × UInt32))) (i : ℕ) (num : ℕ → ℕ → ℤ)
    (hnum : ∀ s u, entrySum (M[s]!).toList u = (num s u : ZMod 4294967296))
    {w : ByteArray} (h : wRow sh rows M i = some w) :
    w.size = dim ∧ ∀ u < dim,
      (2 ^ sh : ℤ) ∣ ∑ s ∈ Finset.range dim, ((rows[i]!.get! s).toNat : ℤ) * num s u ∧
      bz 256 w u = (((∑ s ∈ Finset.range dim, ((rows[i]!.get! s).toNat : ℤ) * num s u) /
        2 ^ sh : ℤ) : ZMod 256) := by
  unfold wRow at h
  simp only at h
  split at h
  · next hc =>
    rw [Option.some.injEq] at h
    subst h
    refine ⟨by simp [ByteArray.size], fun u hu => ?_⟩
    set acc := mulGo M rows[i]! dim 0 (Array.replicate dim 0) with hacc
    have h8 := (allLt_iff.1 hc) u hu
    rw [beq_iff_eq] at h8
    have hz : ((acc[u]!.toNat : ℕ) : ZMod 4294967296) =
        ((∑ s ∈ Finset.range dim, ((rows[i]!.get! s).toNat : ℤ) * num s u : ℤ) :
          ZMod 4294967296) := by
      have := mulGo_get M rows[i]! dim 0 (Array.replicate dim 0) u (by simpa using hu)
      unfold z32 at this
      rw [← hacc] at this
      rw [this]
      rw [getElem!_pos (Array.replicate dim (0 : UInt32)) u (by simpa using hu),
        Array.getElem_replicate]
      push_cast [Int.cast_sum]
      rw [zero_add, Finset.range_eq_Ico]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hnum]
    obtain ⟨hX, hw⟩ := wRow_arith sh hsh _ _ hz h8
    refine ⟨hX, ?_⟩
    unfold bz
    rw [getBytes_ofFn _ hu]
    simp only
    rw [UInt8.toNat_ofNat', show (2 : ℕ) ^ 8 = 256 by norm_num, Nat.mod_mod]
    exact hw
  · exact absurd h (by simp)

theorem reduceRow_spec (sh : ℕ) (hsh : sh ≤ 24) (rows : Array ByteArray) (pexp : Array ℕ)
    (hup : ∀ t < dim, ∀ k < t, rows[t]!.get! k = 0) (M : Array (Array (ℕ × UInt32))) (i : ℕ)
    (num : ℕ → ℕ → ℤ) (hnum : ∀ s u, entrySum (M[s]!).toList u = (num s u : ZMod 4294967296))
    {qs : ByteArray} (h : reduceRow sh rows pexp M i = some qs) :
    qs.size = dim ∧ ∀ u < dim,
      (2 ^ sh : ℤ) ∣ ∑ s ∈ Finset.range dim, ((rows[i]!.get! s).toNat : ℤ) * num s u ∧
      (((∑ s ∈ Finset.range dim, ((rows[i]!.get! s).toNat : ℤ) * num s u) / 2 ^ sh : ℤ) :
        ZMod 256) = ∑ t ∈ Finset.range dim, bz 256 qs t * bz 256 rows[t]! u := by
  unfold reduceRow at h
  split at h
  · exact absurd h (by simp)
  · next w hw =>
    simp only at h
    split at h
    · next hz =>
      rw [Option.some.injEq] at h
      subst h
      obtain ⟨hws, hwu⟩ := wRow_spec sh hsh rows M i num hnum hw
      obtain ⟨-, h2, -, h4⟩ := elimGo_spec goodMask255 rows pexp dim hup 0 w (zeroBytes dim) hws
        (zeroBytes_size dim) (fun t _ _ => zeroBytes_get dim t)
      refine ⟨h2, fun u hu => ⟨(hwu u hu).1, ?_⟩⟩
      have := h4 u hu
      rw [allZero_spec hz hu, (hwu u hu).2, ← Finset.range_eq_Ico] at this
      exact (sub_eq_zero.1 this.symm)
    · exact absurd h (by simp)

theorem coeffs_of_mod (Y q : Fin 4371 → ℤ)
    (hY : ∀ u : Fin 4371, ((Y u : ℤ) : ZMod 256) =
      ∑ t : Fin 4371, ((q t : ℤ) : ZMod 256) * (Bz t u : ZMod 256)) :
    ∃ c : Fin 4371 → ℤ, (∀ u : Fin 4371, Y u = ∑ t : Fin 4371, c t * Bz t u) ∧
      ∀ t, (c t : ZMod 2) = (q t : ZMod 2) := by
  have hd : ∀ u, (256 : ℤ) ∣ Y u - ∑ t : Fin 4371, q t * Bz t u := by
    intro u
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub (∑ t : Fin 4371, q t * Bz t u) (Y u) 256).1
      (by push_cast [Int.cast_sum]; exact (hY u).symm)
    exact_mod_cast this
  set z : Fin 4371 → ℤ := fun u => (Y u - ∑ t : Fin 4371, q t * Bz t u) / 256 with hz
  obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 (smul128_mem_rowLat z)
  refine ⟨fun t => q t + 2 * c' t, fun u => ?_, fun t => ?_⟩
  · have hu := congrFun hc' u
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Bvec, byteVec] at hu
    have e : Y u = ∑ t : Fin 4371, q t * Bz t u + 256 * z u := by
      rw [hz]
      simp only
      rw [Int.mul_ediv_cancel' (hd u)]
      ring
    rw [e, show (256 : ℤ) * z u = 2 * (128 * z u) by ring, ← hu, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by unfold Bz; ring
  · push_cast
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, add_zero]

theorem reduce_row_of
    (sh : ℕ) (hsh : sh ≤ 24) (M : Array (Array (ℕ × UInt32)))
    (num : ℕ → ℕ → ℤ) (hnum : ∀ s u, entrySum (M[s]!).toList u = (num s u : ZMod 4294967296))
    {i : ℕ} {qs : ByteArray} (hqs : reduceRow sh basisRowsK diagExpK M i = some qs) :
    (∀ u : Fin 4371, (2 ^ sh : ℤ) ∣ ∑ t : Fin 4371, Bz i t * num t u) ∧
      ∃ c : Fin 4371 → ℤ,
        (∀ u : Fin 4371,
          (∑ t : Fin 4371, Bz i t * num t u) / 2 ^ sh = ∑ t : Fin 4371, c t * Bz t u) ∧
        ∀ t : Fin 4371, (c t : ZMod 2) = ((qs.get! t).toNat : ZMod 2) := by
  obtain ⟨-, hspec⟩ := reduceRow_spec sh hsh basisRowsK diagExpK basis_facts.lower M i num hnum hqs
  simp only [dim_eq] at hspec
  have hsum : ∀ u : ℕ, ∑ t : Fin 4371, Bz i t * num t u =
      ∑ s ∈ Finset.range 4371, ((basisRowsK[i]!.get! s).toNat : ℤ) * num s u := fun u =>
    Fin.sum_univ_eq_sum_range (fun s => Bz i s * num s u) 4371
  refine ⟨fun u => by rw [hsum u]; exact (hspec u u.2).1, ?_⟩
  obtain ⟨c, hc1, hc2⟩ := coeffs_of_mod (fun u => (∑ t : Fin 4371, Bz i t * num t u) / 2 ^ sh)
    (fun t => ((qs.get! t).toNat : ℤ)) (fun u => by
      rw [hsum u, (hspec u u.2).2, ← Fin.sum_univ_eq_sum_range
        (fun t => bz 256 qs t * bz 256 basisRowsK[t]! u) 4371]
      refine Finset.sum_congr rfl fun t _ => ?_
      unfold bz Bz
      push_cast
      rfl)
  exact ⟨c, hc1, fun t => by rw [hc2 t]; push_cast; rfl⟩

theorem foldl_numer (u : ℕ) : ∀ (l : List (ℕ × ℤ)) (a : ℤ),
    l.foldl (fun s e => if e.1 = u then s + e.2 else s) a =
      a + (l.map fun e => if e.1 = u then e.2 else 0).sum
  | [], a => by simp
  | e :: l, a => by
    rw [List.foldl_cons, foldl_numer u l, List.map_cons, List.sum_cons]
    split <;> ring

theorem numer_eq (g t u : ℕ) : numer g t u =
    (((CFSG.Monster.B.Native.packetRows[selIdx g]!)[t]!).toList.map
      fun e => if e.1 = u then e.2 else 0).sum := by
  unfold numer
  rw [← Array.foldl_toList, foldl_numer, zero_add]

theorem entrySum_map (l : List (ℕ × ℤ)) (u : ℕ) :
    entrySum (l.map fun e => (e.1, toU32 e.2)) u =
      (((l.map fun e => if e.1 = u then e.2 else 0).sum : ℤ) : ZMod 4294967296) := by
  induction l with
  | nil => simp [entrySum]
  | cons e l ih =>
    simp only [entrySum, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    push_cast
    split
    · rw [z32_toU32]
    · rfl

theorem entrySum_genRows (g s u : ℕ) :
    entrySum ((genRows g)[s]!).toList u = (numer g s u : ZMod 4294967296) := by
  rw [numer_eq]
  unfold genRows
  set P := CFSG.Monster.B.Native.packetRows[selIdx g]!
  by_cases hs : s < P.size
  · rw [getElem!_pos (P.map _) s (by simpa using hs), Array.getElem_map,
      getElem!_pos P s hs, Array.toList_map, entrySum_map]
  · rw [getElem!_neg (P.map _) s (by simpa using hs), getElem!_neg P s hs]
    rfl

@[expose] def numerAt (j t u : ℕ) : ℤ :=
  ((CFSG.Monster.B.Native.packetRows[j]!)[t]!).foldl (fun s e => if e.1 = u then s + e.2 else s) 0

@[expose] def packetMat (j : ℕ) : Array (Array (ℕ × UInt32)) :=
  (CFSG.Monster.B.Native.packetRows[j]!).map fun row => row.map fun e => (e.1, toU32 e.2)

theorem numer_eq_numerAt (g t u : ℕ) : numer g t u = numerAt (selIdx g) t u := rfl

theorem genRows_eq_packetMat (g : ℕ) : genRows g = packetMat (selIdx g) := rfl

theorem entrySum_packetMat (j s u : ℕ) :
    entrySum ((packetMat j)[s]!).toList u = (numerAt j s u : ZMod 4294967296) := by
  have e : numerAt j s u = (((CFSG.Monster.B.Native.packetRows[j]!)[s]!).toList.map
      fun e => if e.1 = u then e.2 else 0).sum := by
    unfold numerAt
    rw [← Array.foldl_toList, foldl_numer, zero_add]
  rw [e]
  unfold packetMat
  set P := CFSG.Monster.B.Native.packetRows[j]!
  by_cases hs : s < P.size
  · rw [getElem!_pos (P.map _) s (by simpa using hs), Array.getElem_map,
      getElem!_pos P s hs, Array.toList_map, entrySum_map]
  · rw [getElem!_neg (P.map _) s (by simpa using hs), getElem!_neg P s hs]
    rfl

theorem packBits_lt : ∀ l : List Bool, packBits l < 2 ^ l.length
  | [] => by simp [packBits]
  | b :: l => by
    have := packBits_lt l
    simp only [packBits, List.length_cons, pow_succ]
    split <;> omega

theorem packBits_bit : ∀ (l : List Bool) (j : ℕ),
    (packBits l >>> j) % 2 = if l.getD j false then 1 else 0
  | [], j => by simp [packBits]
  | b :: l, 0 => by
    simp only [packBits, Nat.shiftRight_zero, List.getD_cons_zero]
    split <;> omega
  | b :: l, j + 1 => by
    have h1 : packBits (b :: l) >>> 1 = packBits l := by
      simp only [packBits, Nat.shiftRight_eq_div_pow, pow_one]
      split <;> omega
    rw [List.getD_cons_succ, show j + 1 = 1 + j by omega, Nat.shiftRight_add, h1,
      packBits_bit l j]

theorem packByte_toNat (bit : ℕ → Bool) :
    (packByte bit).toNat = packBits ((List.range 8).map bit) := by
  unfold packByte
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt]
  have := packBits_lt ((List.range 8).map bit)
  simpa using this

theorem ite_beq_one (x : Bool) : ((if x = true then 1 else 0 : ℕ) == 1) = x := by
  cases x <;> rfl

theorem rowBit_packed (F : Fin 552 → ℕ → Bool) (t : ℕ) (ht : t < 4416) :
    Binary.Native.rowBit (ByteArray.mk (Array.ofFn fun b => packByte (F b))) t =
      F ⟨t / 8, by omega⟩ (t % 8) := by
  unfold Binary.Native.rowBit
  rw [getBytes_ofFn _ (show t / 8 < 552 by omega), packByte_toNat, packBits_bit,
    List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (Nat.mod_lt _ (by norm_num))]
  simp only [Option.map_some, Option.getD_some]
  exact ite_beq_one _

theorem and_one_eq_one (x : UInt8) : (x &&& 1 == 1) = true ↔ x.toNat % 2 = 1 := by
  rw [beq_iff_eq]
  have h1 : (1 : UInt8).toNat = 1 := rfl
  constructor
  · intro h
    have := congrArg UInt8.toNat h
    rw [UInt8.toNat_and, h1, Nat.and_one_is_mod] at this
    exact this
  · intro h
    apply UInt8.toNat_inj.1
    rw [UInt8.toNat_and, h1, Nat.and_one_is_mod]
    exact h

theorem bit_zmod2 (b : Bool) (x : ℕ) (h : b = true ↔ x % 2 = 1) :
    (if b then 1 else 0 : ZMod 2) = (x : ZMod 2) := by
  rw [← ZMod.natCast_mod x 2]
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx
  · rw [hx, ite_eq_right (by rw [h, hx]; omega)]
    rfl
  · rw [hx, ite_eq_left (h.2 hx)]
    rfl

theorem rowBit_binRow_of (sh : ℕ) (rows : Array ByteArray) (pexp : Array ℕ)
    (M : Array (Array (ℕ × UInt32))) {i : ℕ} {qs : ByteArray}
    (h : reduceRow sh rows pexp M i = some qs) {t : ℕ} (ht : t < 4371) :
    (if Binary.Native.rowBit (binRow sh rows pexp M i) t then 1 else 0 : ZMod 2) =
      ((qs.get! t).toNat : ZMod 2) := by
  unfold binRow
  rw [h]
  simp only
  rw [rowBit_packed _ t (by omega)]
  simp only
  rw [Nat.div_add_mod t 8]
  apply bit_zmod2
  rw [Bool.and_eq_true, decide_eq_true_eq, and_one_eq_one]
  exact ⟨fun h => h.2, fun h => ⟨ht, h⟩⟩

theorem rowBit_binRow (sh : ℕ) (M : Array (Array (ℕ × UInt32))) {i : ℕ} {qs : ByteArray}
    (h : reduceRow sh basisRowsK diagExpK M i = some qs) {t : ℕ} (ht : t < 4371) :
    (if Binary.Native.rowBit (binRow sh basisRowsK diagExpK M i) t then 1 else 0 : ZMod 2) =
      ((qs.get! t).toNat : ZMod 2) :=
  rowBit_binRow_of sh basisRowsK diagExpK M h ht

theorem binRows_get (g chunks : ℕ) (hc : 0 < chunks) {k : ℕ} (hk : k < 4371) :
    (binRows g chunks)[k]! = binRow 3 basisRows diagExp (genRows g) k := by
  unfold binRows assembleRows binParts
  set sz := dim / chunks + 1 with hsz
  have hsz0 : 0 < sz := Nat.succ_pos _
  have hj : k / sz < chunks := by
    rw [Nat.div_lt_iff_lt_mul hsz0]
    have h1 := Nat.div_add_mod dim chunks
    have h2 := Nat.mod_lt dim hc
    have : chunks * sz = chunks * (dim / chunks) + chunks := by rw [hsz]; ring
    have hk' : k < dim := hk
    rw [this]
    generalize chunks * (dim / chunks) = A at h1 ⊢
    omega
  rw [getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn]
  simp only
  rw [getElem!_pos _ (k / sz) (by simpa using hj), Array.getElem_ofFn]
  change (Array.ofFn (n := sz) fun j => if k / sz * sz + j.val < dim then
      binRow 3 basisRows diagExp (genRows g) (k / sz * sz + j.val) else zeroBytes 552)[k % sz]! = _
  rw [getElem!_pos _ (k % sz) (by simpa using Nat.mod_lt k hsz0), Array.getElem_ofFn]
  simp only
  rw [Nat.div_add_mod' k sz, ite_eq_left (show k < dim from hk)]

end CFSG.Monster.B.Dyadic
