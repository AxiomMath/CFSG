module

public import CFSG.Monster.Schur.FoxData
public import CFSG.Monster.VisCert.FrameData

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Schur

open CFSG.Monster.VisCert

@[expose] def bitZ (x i : ℕ) : ZMod 2 := if x.testBit i then 1 else 0

theorem bitZ_xor (x y i : ℕ) : bitZ (x ^^^ y) i = bitZ x i + bitZ y i := by
  unfold bitZ
  rw [Nat.testBit_xor]
  cases x.testBit i <;> cases y.testBit i <;> decide

theorem bitZ_zero (i : ℕ) : bitZ 0 i = 0 := by simp [bitZ]

theorem bitZ_pow (s i : ℕ) : bitZ (1 <<< s) i = if i = s then 1 else 0 := by
  unfold bitZ
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : s = i <;> simp [h, eq_comm]

theorem bitZ_succ (x t : ℕ) : bitZ x (t + 1) = bitZ (x / 2) t := by
  simp [bitZ, Nat.testBit_succ]

theorem bitZ_zero_right (x : ℕ) : bitZ x 0 = if x % 2 = 1 then 1 else 0 := by
  simp [bitZ, Nat.testBit_zero]

@[expose] def maskDot (N : ℕ) (A : ℕ → ZMod 2) (x : ℕ) : ZMod 2 :=
  ∑ s ∈ Finset.range N, A s * bitZ x s

theorem maskDot_xor (N : ℕ) (A : ℕ → ZMod 2) (x y : ℕ) :
    maskDot N A (x ^^^ y) = maskDot N A x + maskDot N A y := by
  simp only [maskDot, bitZ_xor, mul_add, Finset.sum_add_distrib]

theorem maskDot_zero (N : ℕ) (A : ℕ → ZMod 2) : maskDot N A 0 = 0 := by
  simp [maskDot, bitZ_zero]

theorem maskDot_pow {N s : ℕ} (hs : s < N) (A : ℕ → ZMod 2) : maskDot N A (1 <<< s) = A s := by
  simp [maskDot, bitZ_pow, hs]

@[expose] def xorSelL : List ℕ → ℕ → ℕ
  | [], _ => 0
  | r :: rs, sel => (if sel % 2 = 1 then r else 0) ^^^ xorSelL rs (sel / 2)

@[expose] def selSum : List (ZMod 2) → ℕ → ZMod 2
  | [], _ => 0
  | v :: vs, sel => (if sel % 2 = 1 then v else 0) + selSum vs (sel / 2)

theorem maskDot_xorSelL (N : ℕ) (A : ℕ → ZMod 2) :
    ∀ (rows : List ℕ) (sel : ℕ),
      maskDot N A (xorSelL rows sel) = selSum (rows.map (maskDot N A)) sel
  | [], sel => by simp [xorSelL, selSum, maskDot_zero]
  | r :: rs, sel => by
    rw [xorSelL, maskDot_xor, List.map_cons, selSum, maskDot_xorSelL N A rs]
    split_ifs <;> simp [maskDot_zero]

theorem selSum_eq_zero {vals : List (ZMod 2)} (h : ∀ v ∈ vals, v = 0) :
    ∀ sel : ℕ, selSum vals sel = 0 := by
  induction vals with
  | nil => intro sel; rfl
  | cons v vs ih =>
    intro sel
    rw [selSum, h v List.mem_cons_self, ih (fun w hw => h w (List.mem_cons_of_mem _ hw))]
    simp

theorem selSum_eq : ∀ (vals : List (ZMod 2)) (sel : ℕ),
    selSum vals sel = ∑ t ∈ Finset.range vals.length, bitZ sel t * vals.getD t 0
  | [], sel => by simp [selSum]
  | v :: vs, sel => by
    rw [selSum, selSum_eq vs, List.length_cons, Finset.sum_range_succ', bitZ_zero_right]
    simp only [bitZ_succ, List.getD_cons_succ, List.getD_cons_zero]
    split_ifs <;> simp [add_comm]

@[expose] def foxMask : List ℕ → ℕ → ℕ
  | [], _ => 0
  | g :: w, v => (v <<< (24 * (g - 1))) ^^^ foxMask w (actRows frameMatrices[g]! v)

@[expose] def foxEqs : List ℕ :=
  foxSel.map fun p => foxMask (foxRelators.getD p.1 []) (1 <<< p.2)

@[expose] def lamRow (g i : ℕ) : ℕ := (frameMatrices[g]!)[i]! ^^^ (1 <<< i)

@[expose] def foxRelOK : Bool :=
  foxRelators.all fun r => r.all (fun g => decide (1 ≤ g ∧ g ≤ 14)) &&
    (List.range 24).all fun i => actWord frameMatrices r (1 <<< i) == 1 <<< i

@[expose] def foxCertOK : Bool :=
  (List.range 336).all fun s =>
    xorSelL foxB (lamRow (s / 24 + 1) (s % 24)) ^^^ xorSelL foxEqs (foxM.getD s 0) == 1 <<< s

@[expose] def foxSelOK : Bool :=
  foxSel.all fun p => decide (p.1 < foxRelators.length ∧ p.2 < 24)

theorem foxRelOK_eq_true : foxRelOK = true := by decide +kernel

theorem foxCertOK_eq_true : foxCertOK = true := by decide +kernel

theorem foxSelOK_eq_true : foxSelOK = true := by decide +kernel

theorem length_foxB : foxB.length = 24 := by decide +kernel

theorem foxRelators_letters {r : List ℕ} (hr : r ∈ foxRelators) {g : ℕ} (hg : g ∈ r) :
    1 ≤ g ∧ g ≤ 14 := by
  have h := foxRelOK_eq_true
  simp only [foxRelOK, List.all_eq_true, Bool.and_eq_true] at h
  simpa using (h r hr).1 g hg

theorem foxRelators_actWord {r : List ℕ} (hr : r ∈ foxRelators) {i : ℕ} (hi : i < 24) :
    actWord frameMatrices r (1 <<< i) = 1 <<< i := by
  have h := foxRelOK_eq_true
  simp only [foxRelOK, List.all_eq_true, Bool.and_eq_true] at h
  have h2 := (h r hr).2 i (List.mem_range.2 hi)
  simpa using h2

theorem foxSel_valid {p : ℕ × ℕ} (hp : p ∈ foxSel) : p.1 < foxRelators.length ∧ p.2 < 24 := by
  have h := foxSelOK_eq_true
  simp only [foxSelOK, List.all_eq_true, decide_eq_true_eq] at h
  exact h p hp

theorem foxCert_row {s : ℕ} (hs : s < 336) :
    xorSelL foxB (lamRow (s / 24 + 1) (s % 24)) ^^^ xorSelL foxEqs (foxM.getD s 0) = 1 <<< s := by
  have h := foxCertOK_eq_true
  simp only [foxCertOK, List.all_eq_true, beq_iff_eq] at h
  exact h s (List.mem_range.2 hs)

theorem fox_principal (A : ℕ → ZMod 2) (hA : ∀ t ∈ foxEqs, maskDot 336 A t = 0) {g i : ℕ}
    (hg1 : 1 ≤ g) (hg : g ≤ 14) (hi : i < 24) :
    A (24 * (g - 1) + i) =
      ∑ c ∈ Finset.range 24, bitZ (lamRow g i) c * maskDot 336 A (foxB.getD c 0) := by
  have hs : 24 * (g - 1) + i < 336 := by omega
  have hdiv : (24 * (g - 1) + i) / 24 + 1 = g := by omega
  have hmod : (24 * (g - 1) + i) % 24 = i := by omega
  have h1 := congrArg (maskDot 336 A) (foxCert_row hs)
  rw [hdiv, hmod, maskDot_xor, maskDot_xorSelL, maskDot_xorSelL,
    maskDot_pow hs, selSum_eq_zero (fun v hv => ?_) (foxM.getD _ 0), add_zero] at h1
  · rw [← h1, selSum_eq, List.length_map, length_foxB]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hc' : c < foxB.length := by rw [length_foxB]; exact Finset.mem_range.1 hc
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hc']
    simp
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hv
    exact hA t ht

end CFSG.Monster.Schur
