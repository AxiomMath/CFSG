module

public import CFSG.Sporadic.Co2Smith.Frame

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem pow_eq_one_of_powRows {u : K} {R : Array ℕ} (hu : u.val.val = rowsMatrix 22 R) {n : ℕ}
    (h : powRows 22 R n = idRows 22) : u ^ n = 1 :=
  eq_of_val_eq (by rw [pow_val, hu, ← rowsMatrix_powRows, h, rowsMatrix_idRows]; rfl)

theorem conj_of_conjTo {p u v : K} {P X Y : Array ℕ} (hp : p.val.val = rowsMatrix 22 P)
    (hu : u.val.val = rowsMatrix 22 X) (hv : v.val.val = rowsMatrix 22 Y)
    (h : Native.conjTo P X Y = true) : p * u = v * p :=
  eq_of_val_eq (by
    rw [val_val_mul, val_val_mul, hp, hu, hv, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows,
      beq_iff_eq.mp h])

@[expose] noncomputable def frS
    (i : ℕ) : S0 := if h : i < 10 then ⟨frE i, frE_mem_S0 h⟩ else 1

theorem frS_val
    {i : ℕ} (hi : i < 10) : (frS i : K) = frE i := by
  simp [frS, hi]

theorem frS_ext {u v : S0} (h : (u : K) = v) : u = v := Subtype.ext h

theorem frS_val_val
    {i : ℕ} (hi : i < 10) :
    (frS i : K).val.val = rowsMatrix 22 (Native.fRows seedRowsArr)[i]! := by
  rw [frS_val hi, frE_val hi]

theorem frS_y_pow
    {i : ℕ} (hi : i < 3) : frS (2 * i) ^ 3 = 1 :=
  frS_ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact pow_eq_one_of_powRows (frS_val_val (by omega)) (frame_spec.2.1 i hi).1)

theorem frS_s_sq
    {i : ℕ} (hi : i < 3) : frS (2 * i + 1) * frS (2 * i + 1) = 1 := by
  apply frS_ext
  apply eq_of_val_eq
  rw [Subgroup.coe_mul, Subgroup.coe_one, val_val_mul, val_val_one, frS_val_val (by omega),
    ← rowsMatrix_mulRows, (frame_spec.2.1 i hi).2.1, rowsMatrix_idRows]

theorem frS_s_y
    {i : ℕ} (hi : i < 3) :
    frS (2 * i + 1) * frS (2 * i) * frS (2 * i + 1) = frS (2 * i) * frS (2 * i) := by
  apply frS_ext
  apply eq_of_val_eq
  simp only [Subgroup.coe_mul, val_val_mul]
  rw [frS_val_val (by omega : 2 * i + 1 < 10), frS_val_val (by omega : 2 * i < 10),
    ← rowsMatrix_mulRows, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows, (frame_spec.2.1 i hi).2.2]

theorem frS_comm
    {i j : ℕ} (hi : i < 3) (hj : j < 3) (hij : i ≠ j) {e e' : ℕ} (he : e < 2)
    (he' : e' < 2) :
    frS (2 * i + e) * frS (2 * j + e') = frS (2 * j + e') * frS (2 * i + e) := by
  apply frS_ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  have h := frame_spec.2.2.1 i hi j hj
  rcases h with h | h
  · exact absurd h hij
  · exact comm_of_commRows (frS_val_val (by omega)) (frS_val_val (by omega)) (h e he e' he')

@[expose] def sw12 (k : ℕ) : ℕ :=
  (2 * if k / 2 = 0 then 1 else if k / 2 = 1 then 0 else k / 2) + k % 2

@[expose] def sw23 (k : ℕ) : ℕ :=
  (2 * if k / 2 = 1 then 2 else if k / 2 = 2 then 1 else k / 2) + k % 2

theorem sw12_lt {k : ℕ} (hk : k < 6) : sw12 k < 10 := by
  unfold sw12
  split_ifs <;> omega

theorem sw23_lt {k : ℕ} (hk : k < 6) : sw23 k < 10 := by
  unfold sw23
  split_ifs <;> omega

theorem frS_p12
    {k : ℕ} (hk : k < 6) : frS 6 * frS k = frS (sw12 k) * frS 6 := by
  apply frS_ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact conj_of_conjTo (frS_val_val (by norm_num)) (frS_val_val (by omega))
    (frS_val_val (sw12_lt hk)) (frame_spec.2.2.2.1 k hk).1

theorem frS_p23
    {k : ℕ} (hk : k < 6) : frS 7 * frS k = frS (sw23 k) * frS 7 := by
  apply frS_ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact conj_of_conjTo (frS_val_val (by norm_num)) (frS_val_val (by omega))
    (frS_val_val (sw23_lt hk)) (frame_spec.2.2.2.1 k hk).2

theorem frS_x_pow :
    frS 8 ^ 5 = 1 :=
  frS_ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, frS_val (by norm_num)]; exact frE_x_pow)

theorem frS_x_y1 :
    frS 8 * frS 0 = frS 0 * frS 8 := by
  apply frS_ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact comm_of_commRows (frS_val_val (by norm_num)) (frS_val_val (by norm_num))
    frame_spec.2.2.2.2.2.1

theorem frS_x_s1 :
    frS 8 * frS 1 = frS 1 * frS 8 := by
  apply frS_ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact comm_of_commRows (frS_val_val (by norm_num)) (frS_val_val (by norm_num))
    frame_spec.2.2.2.2.2.2.1

@[expose] noncomputable def frLetters :
    Letters where
  elt := frE
  rows := Native.fRows seedRowsArr
  val_eq k hk := frE_val (by rw [frame_spec.1] at hk; exact hk)

@[expose] noncomputable def frWordS :
    List ℕ → S0
  | [] => 1
  | k :: w => frS k * frWordS w

theorem frWordS_val :

    ∀ w : List ℕ, (∀ k ∈ w, k < 10) → (frWordS w : K) = lWord frLetters w
  | [], _ => rfl
  | k :: w, hw => by
    rw [frWordS, Subgroup.coe_mul, frWordS_val w fun j hj => hw j (List.mem_cons_of_mem _ hj),
      frS_val (hw k List.mem_cons_self), lWord]
    rfl

theorem frWordS_val_val
    {w : List ℕ} (hw : ∀ k ∈ w, k < 10) :
    (frWordS w : K).val.val = rowsMatrix 22 (Native.wRows (Native.fRows seedRowsArr) w) := by
  rw [frWordS_val w hw, lWord_val frLetters w fun k hk => by
    show k < (Native.fRows seedRowsArr).size
    rw [frame_spec.1]
    exact hw k hk]
  rfl

theorem pinRels_lt : ∀ r ∈ Native.pinRels, ∀ k ∈ r.1, k < 10 := by decide

theorem frS_pin
    {r : List ℕ × ℕ} (hr : r ∈ Native.pinRels) :
    (frS 8 * frWordS r.1) ^ r.2 = 1 := by
  apply frS_ext
  rw [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one]
  refine pow_eq_one_of_powRows ?_ (frame_spec.2.2.2.2.2.2.2.2.2.1 r hr)
  rw [val_val_mul, frS_val_val (by norm_num), frWordS_val_val (pinRels_lt r hr),
    rowsMatrix_mulRows]

theorem genAWord_lt : ∀ k ∈ Native.genAWord, k < 10 := by decide

theorem genBWord_lt : ∀ k ∈ Native.genBWord, k < 10 := by decide

theorem aE_mem_S0 :
    aE ∈ S0 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem bE_mem_S0 :
    bE ∈ S0 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem frWordS_genA :
    frWordS Native.genAWord = ⟨aE, aE_mem_S0⟩ := by
  apply frS_ext
  apply eq_of_val_eq
  rw [frWordS_val_val genAWord_lt, (frame_spec.2.2.2.2.2.2.2.2.2.2).1]
  exact aE_val'.symm

theorem frWordS_genB :
    frWordS Native.genBWord = ⟨bE, bE_mem_S0⟩ := by
  apply frS_ext
  apply eq_of_val_eq
  rw [frWordS_val_val genBWord_lt, (frame_spec.2.2.2.2.2.2.2.2.2.2).2]
  exact bE_val'.symm

end CFSG.Sporadic.Co2Smith
