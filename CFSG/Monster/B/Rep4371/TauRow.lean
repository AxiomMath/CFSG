module

public import CFSG.Monster.B.Rep4371.OctTau
public import CFSG.Monster.B.Rep4371.Tau

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Rep4371

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess Matrix

@[expose] noncomputable def rowVec (row : Array (ℕ × ℤ)) : SpaceB :=
  (row.toList.map fun e => ((e.2 : ℚ) / 8) • Rraw e.1).sum

theorem testBit_oddCodes_eq (k : ℕ) :
    (Model.wordN Model.oddCodes[k]!).testBit 0 = (Model.wordN Model.oddCodes[k]!).testBit 1 := by
  rcases getElem!_mem_or (A := Model.oddCodes) k with h | h
  · have h' := h
    simp only [Model.oddCodes, Model.oddCodesOf, List.mem_toArray, List.mem_filter,
      beq_iff_eq] at h'
    exact h'.2
  · rw [h]
    rfl

theorem oddC_bit_eq (k : ℕ) :
    ((oddC k : C) : Fin 24 → ZMod 2) 0 = ((oddC k : C) : Fin 24 → ZMod 2) 1 := by
  rw [coe_oddC, coe_toC_apply, coe_toC_apply]
  exact congrArg boolZ (testBit_oddCodes_eq k)

theorem sgn_oddC_zero (k : ℕ) : sgn (((oddC k : C) : Fin 24 → ZMod 2) 0) =
    ((Model.sgnI ((Model.wordN Model.oddCodes[k]!).testBit 0) : ℤ) : ℚ) := by
  rw [coe_oddC, coe_toC_apply, sgn_boolZ]
  rfl

theorem sgn_P_oddC (k : ℕ) : sgn (P ((oddC k : C) : Fin 24 → ZMod 2)) =
    ((Model.sgnI (Model.pN Model.oddCodes[k]!) : ℤ) : ℚ) := by
  rw [coe_oddC, P_toC, sgn_boolZ]

theorem rowVec_one (j : ℕ) (m : ℤ) : rowVec #[(j, m)] = ((m : ℚ) / 8) • Rraw j := by
  simp [rowVec]

theorem rowVec_two (j j' : ℕ) (m m' : ℤ) :
    rowVec #[(j, m), (j', m')] = ((m : ℚ) / 8) • Rraw j + ((m' : ℚ) / 8) • Rraw j' := by
  simp [rowVec]

theorem rowVec_three (j j' j'' : ℕ) (m m' m'' : ℤ) :
    rowVec #[(j, m), (j', m'), (j'', m'')] =
      ((m : ℚ) / 8) • Rraw j + ((m' : ℚ) / 8) • Rraw j' + ((m'' : ℚ) / 8) • Rraw j'' := by
  simp [rowVec, add_assoc]

theorem sum_map_range_eq (g : ℕ → SpaceB) :
    ∀ n, ((List.range n).map g).sum = ∑ j : Fin n, g j
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_map_range_eq g n,
      Fin.sum_univ_castSucc]
    simp

theorem rowVec_range16 (f : ℕ → ℕ × ℤ) :
    rowVec ((Array.range 16).map f) = ∑ j : Fin 16, (((f j).2 : ℚ) / 8) • Rraw (f j).1 := by
  rw [rowVec, Array.toList_map, Array.toList_range, List.map_map]
  exact sum_map_range_eq (fun j => (((f j).2 : ℚ) / 8) • Rraw (f j).1) 16

theorem cast_mul_eight_div (x : ℤ) : ((x * 8 : ℤ) : ℚ) / 8 = (x : ℚ) := by
  push_cast
  ring

theorem Rraw_A_eq {k : ℕ} (h1 : 1 ≤ k) (h22 : k ≤ 22) : Rraw k = rawA (fin24 (k + 1)) := by
  rw [Rraw, ite_eq_right (by omega : k ≠ 0), ite_eq_left h22]

theorem Rraw_D_eq {k : ℕ} (h23 : 23 ≤ k) (h66 : k ≤ 66) (hp : (k - 23) % 2 = 0) :
    Rraw k = rawD (fin24 ((k - 23) / 2 + 2)) := by
  rw [Rraw, ite_eq_right (by omega : k ≠ 0), ite_eq_right (by omega : ¬ k ≤ 22), ite_eq_left h66,
    ite_eq_left hp]

theorem Rraw_P_eq {k : ℕ} (h23 : 23 ≤ k) (h66 : k ≤ 66) (hp : ¬ (k - 23) % 2 = 0) :
    Rraw k = rawP (fin24 ((k - 23) / 2 + 2)) := by
  rw [Rraw, ite_eq_right (by omega : k ≠ 0), ite_eq_right (by omega : ¬ k ≤ 22), ite_eq_left h66,
    ite_eq_right hp]

theorem Rraw_odd_eq {k : ℕ} (h67 : 67 ≤ k) (h1090 : k ≤ 1090) : Rraw k = rawOdd (oddC (k - 67)) := by
  rw [Rraw, ite_eq_right (by omega : k ≠ 0), ite_eq_right (by omega : ¬ k ≤ 22),
    ite_eq_right (by omega : ¬ k ≤ 66), ite_eq_left h1090]

theorem Rraw_oct_eq {k : ℕ} (h1091 : 1091 ≤ k) (h2322 : k ≤ 2322) :
    Rraw k = octVec ((k - 1091) / 16) ((k - 1091) % 16) := by
  rw [Rraw, ite_eq_right (by omega : k ≠ 0), ite_eq_right (by omega : ¬ k ≤ 22),
    ite_eq_right (by omega : ¬ k ≤ 66), ite_eq_right (by omega : ¬ k ≤ 1090), ite_eq_left h2322]

theorem Rraw_spin_eq {k : ℕ} (h2323 : 2323 ≤ k) :
    Rraw k = rawSpin (if 3347 ≤ k then 1 else 0) (oddC ((k - 2323) % 1024)) := by
  rw [Rraw, ite_eq_right (by omega : k ≠ 0), ite_eq_right (by omega : ¬ k ≤ 22),
    ite_eq_right (by omega : ¬ k ≤ 66), ite_eq_right (by omega : ¬ k ≤ 1090),
    ite_eq_right (by omega : ¬ k ≤ 2322)]

theorem fin24_pos {j : ℕ} (h2 : 2 ≤ j) (h24 : j < 24) :
    (0 : Fin 24) < fin24 j ∧ (1 : Fin 24) < fin24 j := by
  have : (fin24 j : ℕ) = j := Nat.mod_eq_of_lt h24
  constructor <;> exact Fin.lt_def.2 (by rw [this]; simp; omega)

theorem tauB_Rraw (hoct : Model.octDataOK = true) (hsign : Model.octSignOK = true) {k : ℕ}
    (hk : k < 4371) : tauB (Rraw k) = rowVec (Model.tauRow k) := by
  unfold Model.tauRow
  by_cases h0 : k = 0
  · subst h0
    rw [ite_eq_left rfl, rowVec_one, Rraw, ite_eq_left rfl, tauB_rawDiag]
    norm_num
  rw [ite_eq_right h0]
  by_cases h22 : k ≤ 22
  · rw [ite_eq_left h22, rowVec_two, Rraw_A_eq (by omega) h22,
      Rraw_D_eq (by omega) (by omega) (by omega), Rraw_P_eq (by omega) (by omega) (by omega)]
    have e1 : (23 + 2 * (k - 1) - 23) / 2 + 2 = k + 1 := by omega
    have e2 : (24 + 2 * (k - 1) - 23) / 2 + 2 = k + 1 := by omega
    obtain ⟨hp0, hp1⟩ := fin24_pos (j := k + 1) (by omega) (by omega)
    rw [e1, e2, tauB_rawA hp0 hp1]
    norm_num
    module
  rw [ite_eq_right h22]
  by_cases h66 : k ≤ 66
  · rw [ite_eq_left h66]
    obtain ⟨hp0, hp1⟩ := fin24_pos (j := (k - 23) / 2 + 2) (by omega) (by omega)
    by_cases hp : (k - 23) % 2 = 0
    · rw [ite_eq_left hp, rowVec_three, Rraw_D_eq (by omega) h66 hp, tauB_rawD hp0 hp1,
        Rraw_A_eq (k := (k - 23) / 2 + 1) (by omega) (by omega),
        Rraw_P_eq (k := k + 1) (by omega) (by omega) (by omega)]
      have e1 : (k - 23) / 2 + 1 + 1 = (k - 23) / 2 + 2 := by omega
      have e2 : (k + 1 - 23) / 2 + 2 = (k - 23) / 2 + 2 := by omega
      rw [e1, e2]
      push_cast
      module
    · rw [ite_eq_right hp, rowVec_three, Rraw_P_eq (by omega) h66 hp, tauB_rawP hp0 hp1,
        Rraw_A_eq (k := (k - 23) / 2 + 1) (by omega) (by omega),
        Rraw_D_eq (k := k - 1) (by omega) (by omega) (by omega)]
      have e1 : (k - 23) / 2 + 1 + 1 = (k - 23) / 2 + 2 := by omega
      have e2 : (k - 1 - 23) / 2 + 2 = (k - 23) / 2 + 2 := by omega
      rw [e1, e2]
      push_cast
      module
  rw [ite_eq_right h66]
  by_cases h1090 : k ≤ 1090
  · rw [ite_eq_left h1090, rowVec_one, Rraw_odd_eq (by omega) h1090, tauB_rawOdd (oddC_bit_eq _),
      Rraw_spin_eq (by omega), ite_eq_left (by omega : 3347 ≤ 3347 + (k - 67))]
    have e : (3347 + (k - 67) - 2323) % 1024 = k - 67 := by omega
    rw [e, sgn_oddC_zero, cast_mul_eight_div]
  rw [ite_eq_right h1090]
  by_cases h2322 : k ≤ 2322
  · rw [ite_eq_left h2322, rowVec_range16, Rraw_oct_eq (by omega) h2322,
      tauB_octVec hoct (by omega : (k - 1091) / 16 < 77) hsign (Nat.mod_lt _ (by norm_num))]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only
    have hj := j.2
    have e0 : 1091 + 16 * ((k - 1091) / 16) + (j : ℕ) - 1091 = 16 * ((k - 1091) / 16) + j := by
      omega
    have e1 : (16 * ((k - 1091) / 16) + (j : ℕ)) / 16 = (k - 1091) / 16 := by omega
    have e2 : (16 * ((k - 1091) / 16) + (j : ℕ)) % 16 = j := by omega
    rw [Rraw_oct_eq (by omega) (by omega), e0, e1, e2]
    have hc : (((2 * Model.Mentry ((k - 1091) % 16) j : ℤ) : ℚ) / 8) =
        ((Model.Mentry ((k - 1091) % 16) j : ℚ) / 4) := by
      push_cast
      ring
    rw [hc]
  rw [ite_eq_right h2322]
  by_cases h3346 : k ≤ 3346
  · rw [ite_eq_left h3346, rowVec_one, Rraw_spin_eq (by omega), ite_eq_right (by omega),
      tauB_rawSpin_zero, Rraw_odd_eq (by omega) (by omega)]
    have e : (k - 2323) % 1024 = k - 2323 := Nat.mod_eq_of_lt (by omega)
    have e' : 67 + (k - 2323) - 67 = k - 2323 := by omega
    rw [e, e', sgn_P_oddC, cast_mul_eight_div]
  · rw [ite_eq_right h3346, rowVec_one, Rraw_spin_eq (by omega), ite_eq_left (by omega),
      tauB_rawSpin_one (oddC_bit_eq _), Rraw_spin_eq (by omega), ite_eq_right (by omega)]
    have e : (k - 2323) % 1024 = k - 3347 := by
      rw [show k - 2323 = 1024 + (k - 3347) by omega, Nat.add_mod_left]
      exact Nat.mod_eq_of_lt (by omega)
    have e' : (2323 + (k - 3347) - 2323) % 1024 = k - 3347 := by
      rw [show 2323 + (k - 3347) - 2323 = k - 3347 by omega]
      exact Nat.mod_eq_of_lt (by omega)
    rw [e, e', sgn_add, sgn_oddC_zero, sgn_P_oddC, cast_mul_eight_div, sgnI_xor]

end CFSG.Monster.B.Rep4371
