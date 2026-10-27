module

public import CFSG.Sporadic.Co2Smith.RigidFrame

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Certificates.ExtraspecialNF CFSG.Sporadic.SmallF2
open CFSG.Sporadic.SmallF2.Native

universe u

@[expose] def codeA (A : Fin 4 → Fin 4 → ZMod 2) : ℕ :=
  ofBits 16 fun k => if h : k < 16 then decide (A ⟨k % 4, by omega⟩ ⟨k / 4, by omega⟩ = 1)
    else false

theorem codeA_testBit (A : Fin 4 → Fin 4 → ZMod 2) (b b' : Fin 4) :
    (codeA A).testBit (4 * b.val + b'.val) = decide (A b' b = 1) := by
  rw [codeA, ofBits_testBit]
  have h16 : 4 * b.val + b'.val < 16 := by omega
  rw [dite_eq_left h16]
  have e1 : (⟨(4 * b.val + b'.val) % 4, by omega⟩ : Fin 4) = b' :=
    Fin.ext (show (4 * b.val + b'.val) % 4 = b'.val by omega)
  have e2 : (⟨(4 * b.val + b'.val) / 4, by omega⟩ : Fin 4) = b :=
    Fin.ext (show (4 * b.val + b'.val) / 4 = b.val by omega)
  simp only [h16, decide_true, Bool.true_and, e1, e2]

theorem codeA_lt (A : Fin 4 → Fin 4 → ZMod 2) : codeA A < 65536 := ofBits_lt 16 _

@[expose] def XmA (A : Fin 4 → Fin 4 → ZMod 2) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  fun i j => if i.val % 2 = j.val % 2 then A ⟨i.val / 2, by omega⟩ ⟨j.val / 2, by omega⟩ else 0

theorem xRows_spec (cn : ℕ) (i j : Fin 8) :
    rowsMatrix 8 (Native.xRows cn) i j =
      if j.val % 2 = i.val % 2 ∧ cn.testBit (4 * (j.val / 2) + i.val / 2) = true then 1 else 0 := by
  rw [rowsMatrix_apply, Native.xRows, Array.getElem?_ofFn, dite_eq_left i.2, Option.getD_some,
    toVecD_ofBits]
  simp only [Bool.and_eq_true, beq_iff_eq]

theorem zmod2_ite (z : ZMod 2) : (if z = 1 then (1 : ZMod 2) else 0) = z := by
  rcases zmod_two_cases z with rfl | rfl <;> decide

theorem xRows_codeA (A : Fin 4 → Fin 4 → ZMod 2) :
    rowsMatrix 8 (Native.xRows (codeA A)) = XmA A := by
  ext i j
  rw [xRows_spec, XmA]
  have h := codeA_testBit A ⟨j.val / 2, by omega⟩ ⟨i.val / 2, by omega⟩
  simp only at h
  rw [h]
  by_cases hij : i.val % 2 = j.val % 2
  · rw [ite_eq_left hij]
    simp only [hij.symm, true_and, decide_eq_true_eq]
    exact zmod2_ite _
  · rw [ite_eq_right hij]
    have hji : ¬ j.val % 2 = i.val % 2 := fun h' => hij h'.symm
    simp only [hji, false_and, ite_false]

@[expose] def xMat : Matrix (Fin 8) (Fin 8) (ZMod 2) := rowsMatrix 8 (Native.xRows 24505)

@[expose] def frameMat (k : ℕ) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  if k < 8 then stdMat k else xMat

theorem colAct8_lt (R : Array ℕ) (v : ℕ) : Native.colAct8 R v < 2 ^ 8 := by
  rw [Native.colAct8, vecMulN]
  have key : ∀ (L : List ℕ) (acc : ℕ), acc < 2 ^ 8 →
      L.foldl (fun acc j => if v.testBit j then acc ^^^ ((transposeRows 8 R)[j]?.getD 0) else acc)
        acc < 2 ^ 8 := by
    intro L
    induction L with
    | nil => intro acc h; exact h
    | cons j L ih =>
      intro acc h
      apply ih
      dsimp only
      split_ifs
      · refine Nat.xor_lt_two_pow h ?_
        cases hj : (transposeRows 8 R)[j]? with
        | none => simp
        | some x =>
          rw [Option.getD_some]
          rw [transposeRows, Array.getElem?_ofFn] at hj
          split_ifs at hj with hlt
          · simp only [Option.some.injEq] at hj
            rw [← hj]
            exact ofBits_lt 8 _
      · exact h
  exact key _ 0 (by norm_num)

theorem fixesAll8_of_eq_one {R : Array ℕ} (h : rowsMatrix 8 R = 1) : Native.fixesAll8 R = true := by
  simp only [Native.fixesAll8, List.all_eq_true, List.mem_range, beq_iff_eq]
  intro a ha
  have hv := rowsMatrix_mulVec 8 R (1 <<< a)
  rw [h, Matrix.one_mulVec] at hv
  have hlt : 1 <<< a < 2 ^ 8 := by
    rw [Nat.one_shiftLeft]
    exact Nat.pow_lt_pow_right (by norm_num) ha
  exact (toVecD_injective (colAct8_lt R _) hlt hv.symm)

theorem pinUnique_spec
    {cn : ℕ} (hc : cn < 65536) (h : Native.pinOK cn = true) : cn = 24505 := by
  have hu := pinUnique_check
  simp only [Native.pinUniqueOK, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq] at hu
  rcases hu cn hc with h' | h'
  · rw [h] at h'
    exact absurd h' (by decide)
  · exact h'

theorem wRows8_lt : ∀ r ∈ Native.pinRels, ∀ k ∈ r.1, k < 8 := by decide

namespace LocalConfig

variable (c : LocalConfig.{u})

@[expose] def evenV (u : Fin 8 → ZMod 2) : Prop := ∀ b : Fin 8, b.val.testBit 0 = true → u b = 0

theorem C1_even
    {x : c.M} (hx : x ∈ c.C1) : ∃ u, evenV u ∧ x = c.β u := by
  have hmul : ∀ {x y : c.M}, (∃ u, evenV u ∧ x = c.β u) → (∃ u, evenV u ∧ y = c.β u) →
      ∃ u, evenV u ∧ x * y = c.β u := by
    rintro x y ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
    exact ⟨u + u', fun b hb => by rw [Pi.add_apply, hu b hb, hu' b hb, add_zero],
      (c.β_add u u').symm⟩
  have hs : ∀ {s : c.M}, s ∈ c.C123 → ∀ e1 e2 : Bool,
      ∃ u, evenV u ∧ c.yb 2 e1 (c.yb 4 e2 s) = c.β u := by
    intro s hs e1 e2
    rcases c.eq_w_of_mem hs with rfl | rfl
    · exact ⟨0, fun _ _ => rfl, by rw [yb_one, yb_one, c.β_zero]⟩
    · refine ⟨sv (vcode false e1 e2), fun b hb => ?_, ?_⟩
      · simp only [sv, Pi.single_apply]
        split_ifs with hbv
        · subst hbv
          cases e1 <;> cases e2 <;> simp [vcode] at hb
        · rfl
      · rw [c.β_sv, c.v_vcode]
        rfl
  obtain ⟨t, ht, t', ht', rfl⟩ := c.decomp2.2 x hx
  obtain ⟨s1, hs1, s2, hs2, rfl⟩ := c.decomp3.2 t ht
  obtain ⟨s3, hs3, s4, hs4, rfl⟩ := c.decomp3.2 t' ht'
  simp only [map_mul]
  exact hmul (hmul (hs hs1 false false) (hs hs2 false true))
    (hmul (hs hs3 true false) (hs hs4 true true))

theorem x_C1
    (e1 e2 : Bool) : c.mA (frS 8) (c.vv false e1 e2) ∈ c.C1 := by
  rw [mem_C1, ← c.mA_comm_of frS_x_s1, c.s1_vv]
  rfl

@[expose] noncomputable def colX
    (e1 e2 : Bool) : Fin 8 → ZMod 2 :=
  (c.C1_even (c.x_C1 e1 e2)).choose

theorem colX_even
    (e1 e2 : Bool) : evenV (c.colX e1 e2) :=
  (c.C1_even (c.x_C1 e1 e2)).choose_spec.1

theorem x_vv0
    (e1 e2 : Bool) : c.mA (frS 8) (c.vv false e1 e2) = c.β (c.colX e1 e2) :=
  (c.C1_even (c.x_C1 e1 e2)).choose_spec.2

@[expose] noncomputable def Ax
    (b' b : Fin 4) : ZMod 2 :=
  c.colX (b.val.testBit 0) (b.val.testBit 1) ⟨2 * b'.val, by omega⟩

theorem y1_β_even
    {u : Fin 8 → ZMod 2} (hu : evenV u) :
    c.mA (frS 0) (c.β u) = c.β fun i => if i.val.testBit 0 then u ⟨i.val - 1, by omega⟩ else 0 := by
  have h1 := hu 1 rfl
  have h3 := hu 3 rfl
  have h5 := hu 5 rfl
  have h7 := hu 7 rfl
  simp only [β, Fin.prod_univ_eight, map_mul, map_pow]
  simp only [h1, h3, h5, h7, ZMod.val_zero, pow_zero, mul_one]
  have e : ∀ a : Fin 8, c.v a = c.vv (a.val.testBit 0) (a.val.testBit 1) (a.val.testBit 2) :=
    fun a => rfl
  simp only [e, c.y1_vv]
  norm_num
  rfl

theorem colX_eq_XmA
    (e1 e2 : Bool) (i : Fin 8) :
    c.colX e1 e2 i = XmA c.Ax i (vcode false e1 e2) := by
  have hv0 : (vcode false e1 e2).val % 2 = 0 := by cases e1 <;> cases e2 <;> rfl
  have hv1 : ((vcode false e1 e2).val / 2).testBit 0 = e1 := by cases e1 <;> cases e2 <;> rfl
  have hv2 : ((vcode false e1 e2).val / 2).testBit 1 = e2 := by cases e1 <;> cases e2 <;> rfl
  rw [XmA]
  split_ifs with h
  · rw [Ax]
    simp only [hv1, hv2]
    congr 1
    exact Fin.ext (by simp only; omega)
  · exact c.colX_even e1 e2 i (by rw [Nat.testBit_zero]; simp only [decide_eq_true_eq]; omega)

theorem shift_eq_XmA
    (e1 e2 : Bool) (i : Fin 8) :
    (if i.val.testBit 0 then c.colX e1 e2 ⟨i.val - 1, by omega⟩ else 0) =
      XmA c.Ax i (vcode true e1 e2) := by
  have hv0 : (vcode true e1 e2).val % 2 = 1 := by cases e1 <;> cases e2 <;> rfl
  have hv1 : ((vcode true e1 e2).val / 2).testBit 0 = e1 := by cases e1 <;> cases e2 <;> rfl
  have hv2 : ((vcode true e1 e2).val / 2).testBit 1 = e2 := by cases e1 <;> cases e2 <;> rfl
  rw [XmA, Nat.testBit_zero]
  by_cases h : i.val % 2 = 1
  · rw [ite_eq_left (by simp [h]), ite_eq_left (by omega), Ax]
    simp only [hv1, hv2]
    congr 1
    exact Fin.ext (by simp only; omega)
  · rw [ite_eq_right (by simp [h]), ite_eq_right (by omega)]

theorem rep_x :
    c.Rep (c.mA (frS 8)) (XmA c.Ax) := by
  refine c.rep_of_cols _ _ fun a => ?_
  rw [← vcode_bits a, c.v_vcode]
  cases a.val.testBit 0
  · rw [c.x_vv0]
    congr 1
    funext i
    exact c.colX_eq_XmA _ _ i
  · show c.mA (frS 8) (c.mA (frS 0) (c.vv false _ _)) = _
    rw [c.mA_comm_of frS_x_y1, c.x_vv0, c.y1_β_even (c.colX_even _ _)]
    congr 1
    funext i
    exact c.shift_eq_XmA _ _ i

theorem rep_one :
    c.Rep (c.mA 1) 1 := c.rep_congr c.rep_id fun m => c.mA_one m

theorem rep_mul
    {g h : S0} {A B : Matrix (Fin 8) (Fin 8) (ZMod 2)} (hg : c.Rep (c.mA g) A)
    (hh : c.Rep (c.mA h) B) : c.Rep (c.mA (g * h)) (A * B) :=
  c.rep_congr (Rep.comp c hg hh) fun m => c.mA_mul g h m

theorem rep_pow
    {g : S0} {A : Matrix (Fin 8) (Fin 8) (ZMod 2)} (hg : c.Rep (c.mA g) A) :
    ∀ n : ℕ, c.Rep (c.mA (g ^ n)) (A ^ n)
  | 0 => by rw [pow_zero, pow_zero]; exact c.rep_one
  | n + 1 => by rw [pow_succ, pow_succ]; exact c.rep_mul (rep_pow hg n) hg
theorem rep_wRows8 :
    ∀ w : List ℕ, (∀ k ∈ w, k < 8) →
    c.Rep (c.mA (frWordS w)) (rowsMatrix 8 (Native.wRows8 w))
  | [], _ => by rw [frWordS, Native.wRows8, rowsMatrix_idRows]; exact c.rep_one
  | k :: w, hw => by
    rw [frWordS, Native.wRows8, rowsMatrix_mulRows]
    exact c.rep_mul (c.rep_std k (hw k List.mem_cons_self))
      (rep_wRows8 w fun j hj => hw j (List.mem_cons_of_mem _ hj))

theorem codeA_Ax :
    codeA c.Ax = 24505 := by
  refine pinUnique_spec (codeA_lt _) ?_
  simp only [Native.pinOK, List.all_eq_true]
  intro r hr
  apply fixesAll8_of_eq_one
  rw [rowsMatrix_powRows, rowsMatrix_mulRows, xRows_codeA]
  have hrep := c.rep_pow (c.rep_mul c.rep_x (c.rep_wRows8 r.1 (wRows8_lt r hr))) r.2
  refine Rep.eq_one c hrep fun m => ?_
  rw [frS_pin hr, c.mA_one]

theorem rep_x_std :
    c.Rep (c.mA (frS 8)) xMat := by
  have h := c.rep_x
  rwa [← xRows_codeA, c.codeA_Ax] at h

theorem rep_frame
    (k : ℕ) (hk : k < 9) : c.Rep (c.mA (frS k)) (frameMat k) := by
  rw [frameMat]
  split_ifs with h
  · exact c.rep_std k h
  · rw [show k = 8 by omega]
    exact c.rep_x_std

end LocalConfig

end CFSG.Sporadic.Co2Smith
