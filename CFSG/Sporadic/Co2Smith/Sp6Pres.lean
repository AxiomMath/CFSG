module

public import CFSG.Sporadic.Co2Smith.FrameRel
public import CFSG.Sporadic.Co2Smith.Sp6PresCheck

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem sp6Check_parts :
    ((List.range 8).all fun i =>
        Native.wRows (Native.sp6LetterRows seedRowsArr) [2 * i, 2 * i + 1] == idRows 22) = true ∧
      (Native.sp6Rels.all fun r =>
        Native.wRows (Native.sp6LetterRows seedRowsArr) (r.map Native.sCode) ==
          idRows 22) = true ∧
      ((List.finRange 8).all fun i =>
        Native.wRows (Native.sp6LetterRows seedRowsArr)
            ((Native.commWordsN (Native.sp6Pairs i)).map Native.sCode) ==
          Native.wRows (Native.sp6LetterRows seedRowsArr) [2 * i.val]) = true ∧
      (Native.wRows (Native.sp6LetterRows seedRowsArr) (Native.sp6Wa.map Native.sCode) ==
        Native.mRows seedRowsArr [2]) = true ∧
      (Native.wRows (Native.sp6LetterRows seedRowsArr) (Native.sp6Wb.map Native.sCode) ==
        Native.mRows seedRowsArr [3]) = true := by
  have h := sp6Check_ok
  simp only [Native.sp6Check, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem sp6LetterMix_mem : ∀ k < 16, ∀ l ∈ Native.sp6LetterMix k, l = 2 ∨ l = 3 := by
  decide +kernel

theorem sp6LetterRows_size : (Native.sp6LetterRows seedRowsArr).size = 16 := by
  simp [Native.sp6LetterRows]

theorem sp6LetterRows_get {k : ℕ} (hk : k < 16) :
    (Native.sp6LetterRows seedRowsArr)[k]! =
      Native.mRows seedRowsArr (Native.sp6LetterMix k) := by
  simp [Native.sp6LetterRows, hk]

@[expose] noncomputable def sp6Letters : Letters where
  elt k := mWord (Native.sp6LetterMix k)
  rows := Native.sp6LetterRows seedRowsArr
  val_eq k hk := by
    have hk' : k < 16 := sp6LetterRows_size ▸ hk
    rw [sp6LetterRows_get hk']
    exact mWord_val _ fun l hl => by
      rcases sp6LetterMix_mem k hk' l hl with rfl | rfl <;> norm_num

theorem sp6Letters_mem
    {k : ℕ} (hk : k < 16) : sp6Letters.elt k ∈ S0 :=
  mWord_mem_S0 _ (sp6LetterMix_mem k hk)

theorem sp6Letters_size :
    sp6Letters.rows.size = 16 := sp6LetterRows_size

theorem lWord_sp6_eq
    {w w' : List ℕ} (hw : ∀ k ∈ w, k < 16) (hw' : ∀ k ∈ w', k < 16)
    (h : (Native.wRows (Native.sp6LetterRows seedRowsArr) w ==
      Native.wRows (Native.sp6LetterRows seedRowsArr) w') = true) :
    lWord sp6Letters w = lWord sp6Letters w' := by
  apply eq_of_val_eq
  rw [lWord_val sp6Letters w (fun k hk => sp6Letters_size ▸ hw k hk),
    lWord_val sp6Letters w' (fun k hk => sp6Letters_size ▸ hw' k hk)]
  exact congrArg (rowsMatrix 22) (beq_iff_eq.mp h)

theorem sCode_lt (l : Fin 8 × Bool) : Native.sCode l < 16 := by
  obtain ⟨i, b⟩ := l
  have := i.isLt
  cases b <;> simp [Native.sCode] <;> omega

theorem sCode_mem_lt (w : List (Fin 8 × Bool)) : ∀ k ∈ w.map Native.sCode, k < 16 := by
  intro k hk
  obtain ⟨l, -, rfl⟩ := List.mem_map.mp hk
  exact sCode_lt l

theorem sp6Letters_inv
    (i : ℕ) (hi : i < 8) :
    sp6Letters.elt (2 * i + 1) = (sp6Letters.elt (2 * i))⁻¹ := by
  have h := List.all_eq_true.mp sp6Check_parts.1 i (List.mem_range.mpr hi)
  have e := lWord_sp6_eq (w := [2 * i, 2 * i + 1]) (w' := [])
    (by intro k hk; simp at hk; omega) (by simp) h
  simp only [lWord, mul_one] at e
  exact eq_inv_of_mul_eq_one_right e

@[expose] noncomputable def sp6Gen (i : Fin 8) : S0 :=
  ⟨sp6Letters.elt (2 * i.val), sp6Letters_mem (by omega)⟩

theorem sp6Gen_val
    (i : Fin 8) : (sp6Gen i : K) = sp6Letters.elt (2 * i.val) := rfl

theorem lift_sp6Gen_mk
    (w : List (Fin 8 × Bool)) :
    ((FreeGroup.lift sp6Gen (FreeGroup.mk w) : S0) : K) =
      lWord sp6Letters (w.map Native.sCode) := by
  rw [FreeGroup.lift_mk]
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons, Subgroup.coe_mul, ih, List.map_cons, lWord]
    congr 1
    obtain ⟨i, b⟩ := l
    cases b
    · show ((sp6Gen i)⁻¹ : S0).val = sp6Letters.elt (2 * i.val + 1)
      rw [Subgroup.coe_inv, sp6Gen_val, sp6Letters_inv i.val i.isLt]
    · rfl

theorem lift_sp6Gen_rel
    {r : List (Fin 8 × Bool)} (hr : r ∈ Native.sp6Rels) :
    FreeGroup.lift sp6Gen (FreeGroup.mk r) = 1 := by
  apply Subtype.ext
  rw [lift_sp6Gen_mk, Subgroup.coe_one]
  have h := List.all_eq_true.mp sp6Check_parts.2.1 r hr
  exact lWord_sp6_eq (w' := []) (sCode_mem_lt r) (by simp) h

theorem lift_sp6Gen_comm
    (i : Fin 8) :
    FreeGroup.lift sp6Gen (FreeGroup.mk (Native.commWordsN (Native.sp6Pairs i))) = sp6Gen i := by
  apply Subtype.ext
  rw [lift_sp6Gen_mk, sp6Gen_val]
  have h := List.all_eq_true.mp sp6Check_parts.2.2.1 i (List.mem_finRange i)
  rw [lWord_sp6_eq (sCode_mem_lt _) (by intro k hk; simp at hk; omega) h]
  simp only [lWord, mul_one]

theorem lift_sp6Gen_mix
    {w : List (Fin 8 × Bool)} {l : ℕ} (hl : l = 2 ∨ l = 3)
    (h : (Native.wRows (Native.sp6LetterRows seedRowsArr) (w.map Native.sCode) ==
      Native.mRows seedRowsArr [l]) = true) :
    ((FreeGroup.lift sp6Gen (FreeGroup.mk w) : S0) : K) = mWord [l] := by
  rw [lift_sp6Gen_mk]
  apply eq_of_val_eq
  rw [lWord_val sp6Letters _ (fun k hk => sp6Letters_size ▸ sCode_mem_lt w k hk),
    mWord_val [l] (by rcases hl with rfl | rfl <;> simp)]
  exact congrArg (rowsMatrix 22) (beq_iff_eq.mp h)

theorem closure_sp6Gen :
    Subgroup.closure (Set.range sp6Gen) = ⊤ := by
  set C := Subgroup.closure (Set.range sp6Gen)
  have hrange : ∀ f : FreeGroup (Fin 8), FreeGroup.lift sp6Gen f ∈ C := by
    intro f
    have h : FreeGroup.lift sp6Gen f ∈ (FreeGroup.lift sp6Gen).range := ⟨f, rfl⟩
    rwa [FreeGroup.range_lift_eq_closure] at h
  have ha : (⟨aE, aE_mem_S0⟩ : S0) ∈ C := by
    have e : FreeGroup.lift sp6Gen (FreeGroup.mk Native.sp6Wa) = ⟨aE, aE_mem_S0⟩ :=
      Subtype.ext ((lift_sp6Gen_mix (Or.inl rfl) sp6Check_parts.2.2.2.1).trans mWord_two)
    rw [← e]
    exact hrange _
  have hb : (⟨bE, bE_mem_S0⟩ : S0) ∈ C := by
    have e : FreeGroup.lift sp6Gen (FreeGroup.mk Native.sp6Wb) = ⟨bE, bE_mem_S0⟩ :=
      Subtype.ext ((lift_sp6Gen_mix (Or.inr rfl) sp6Check_parts.2.2.2.2).trans mWord_three)
    rw [← e]
    exact hrange _
  have hle : S0 ≤ C.map S0.subtype := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨_, ha, rfl⟩
    · exact ⟨_, hb, rfl⟩
  rw [eq_top_iff]
  intro g _
  obtain ⟨g', hg', he⟩ := hle g.2
  have : g' = g := Subtype.ext he
  rw [← this]
  exact hg'

end CFSG.Sporadic.Co2Smith
