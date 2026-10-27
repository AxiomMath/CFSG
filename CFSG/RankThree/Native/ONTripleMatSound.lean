module

public import CFSG.RankThree.Native.ONTripleSigCheckInputs
public import CFSG.Certificates.Kernel.Misc.F7MatSound
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

set_option maxRecDepth 100000

public section

namespace CFSG.RankThree.Native.ONTriple

open CFSG.KC.Misc.F7 CFSG.KC.Loop

abbrev Mat45 := Matrix (Fin 45) (Fin 45) (ZMod 7)

@[expose] def MRep (c : ℕ) (g : Mat45ˣ) : Prop := c = enc (g : Mat45)

theorem mrep_mmul {a b : ℕ} {g h : Mat45ˣ} (ha : MRep a g) (hb : MRep b h) :
    MRep (mmul a b) (g * h) := by
  unfold MRep at *
  rw [ha, hb, mmul_enc, Units.val_mul]

theorem mrep_idM : MRep idM 1 := by
  unfold MRep
  rw [Units.val_one, idM_eq]

theorem mrep_powM {a : ℕ} {g : Mat45ˣ} (ha : MRep a g) (e : ℕ) : MRep (powM a e) (g ^ e) := by
  unfold MRep at *
  rw [ha, powM_enc, Units.val_pow_eq_pow_val]

theorem mrep_eq {a b : ℕ} {g h : Mat45ˣ} (ha : MRep a g) (hb : MRep b h)
    (hab : Nat.beq a b = true) : g = h :=
  Units.ext (enc_inj (ha.symm.trans ((Nat.eq_of_beq_eq_true hab).trans hb)))

theorem mrep_beq {a b : ℕ} {g h : Mat45ˣ} (ha : MRep a g) (hb : MRep b h) :
    Nat.beq a b = true ↔ g = h := by
  refine ⟨mrep_eq ha hb, fun e => ?_⟩
  unfold MRep at ha hb
  rw [ha, hb, e]
  exact Nat.beq_refl _

theorem mrep_ne {a b : ℕ} {g h : Mat45ˣ} (ha : MRep a g) (hb : MRep b h)
    (hab : notB (Nat.beq a b) = true) : g ≠ h := by
  intro e
  rw [bNot_eq, (mrep_beq ha hb).2 e] at hab
  exact Bool.noConfusion hab

theorem mrep_inv {a b : ℕ} {g : Mat45ˣ} {B : Mat45} (ha : MRep a g) (hb : b = enc B)
    (h : Nat.beq (mmul a b) idM = true) : MRep b g⁻¹ := by
  unfold MRep at ha ⊢
  have e : (g : Mat45) * B = 1 := enc_inj (by
    rw [← mmul_enc, ← ha, ← hb, ← idM_eq]
    exact Nat.eq_of_beq_eq_true h)
  have hB : B = ((g⁻¹ : Mat45ˣ) : Mat45) := by
    calc B = ((g⁻¹ : Mat45ˣ) : Mat45) * ((g : Mat45) * B) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [e, mul_one]
  rw [hb, hB]

theorem mrep_wordC {F FI : ℕ → ℕ} {R : Array Mat45ˣ} (w : List (ℕ × Bool))
    (h : ∀ l ∈ w, MRep (F l.1) (R.getD l.1 1) ∧ MRep (FI l.1) (R.getD l.1 1)⁻¹) :
    MRep (wordC F FI w) (wordG R w) := by
  induction w with
  | nil => exact mrep_idM
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    have hl := h (i, b) List.mem_cons_self
    have hw := ih fun l hl => h l (List.mem_cons_of_mem _ hl)
    unfold wordG at hw ⊢
    rw [List.map_cons, List.prod_cons]
    cases b with
    | true => exact mrep_mmul hl.1 hw
    | false => exact mrep_mmul hl.2 hw

theorem nthN_eq (l : List ℕ) (i : ℕ) : nthN l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons x l ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem nthOp_eq (l : List SOp) (i : ℕ) : nthOp l i = l.getD i (.pow 0 0) := by
  induction l generalizing i with
  | nil => rfl
  | cons x l ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

@[expose, irreducible] noncomputable def genMat (k : ℕ) : Mat45 := decC 45 (nthN genC k)
@[expose, irreducible] noncomputable def genIMat (k : ℕ) : Mat45 := decC 45 (nthN genIC k)

theorem genM_eq (k : ℕ) : genM k = enc (genMat k) := by
  unfold genM genMat
  exact widen_eq _
theorem genIM_eq (k : ℕ) : genIM k = enc (genIMat k) := by
  unfold genIM genIMat
  exact widen_eq _

@[expose, irreducible] noncomputable def gM (k : Fin 8) : Mat45ˣ :=
  if h : genMat k * genIMat k = 1 then ⟨genMat k, genIMat k, h, _root_.mul_eq_one_comm.1 h⟩
  else 1

@[expose, irreducible] noncomputable def gMArr : Array Mat45ˣ := Array.ofFn gM

theorem gMArr_getD (k : Fin 8) : gMArr.getD k.val 1 = gM k := by
  rw [gMArr, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [k.isLt, dite_true, Option.getD_some]

theorem size_gMArr : gMArr.size = 8 := by rw [gMArr, Array.size_ofFn]

theorem chkGensM_at (h : chkGensM = true) (k : ℕ) (hk : k < 8) :
    (MRep (genM k) (gM ⟨k, hk⟩) ∧ MRep (genIM k) (gM ⟨k, hk⟩)⁻¹) ∧
      nthN regC k = nthN genC k ∧ nthN regIC k = nthN genIC k := by
  rw [chkGensM] at h
  have h1 := (allN_iff 8 _).1 h k hk
  rw [bAnd_eq, bAnd_eq] at h1
  obtain ⟨hp, hr, hri⟩ := h1
  have e : genMat k * genIMat k = 1 := enc_inj (by
    rw [← mmul_enc, ← genM_eq, ← genIM_eq, ← idM_eq]
    exact Nat.eq_of_beq_eq_true hp)
  have hg : gM ⟨k, hk⟩ = ⟨genMat k, genIMat k, e, _root_.mul_eq_one_comm.1 e⟩ := by
    unfold gM
    exact dite_eq_left e
  have hr' := Nat.eq_of_beq_eq_true hr
  have hri' := Nat.eq_of_beq_eq_true hri
  refine ⟨⟨?_, ?_⟩, hr', hri'⟩
  · rw [MRep, hg, genM_eq, Units.val_mk]
  · rw [MRep, hg, genIM_eq, Units.inv_mk, Units.val_mk]

theorem chkGensM_spec (h : chkGensM = true) (k : Fin 8) :
    (MRep (genM k) (gM k) ∧ MRep (genIM k) (gM k)⁻¹) ∧ nthN regC k = nthN genC k ∧
      nthN regIC k = nthN genIC k :=
  chkGensM_at h k.val k.isLt

theorem relWord_eq (w : List (Fin 8 × Bool)) : relWord w = w.map fun l => (l.1.val, l.2) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    change (i.val, b) :: relWord w = _
    rw [ih, List.map_cons]

theorem lift_gM_mk (w : List (Fin 8 × Bool)) :
    FreeGroup.lift gM (FreeGroup.mk w) = wordG gMArr (relWord w) := by
  induction w with
  | nil =>
    change FreeGroup.lift gM 1 = 1
    exact map_one _
  | cons x w ih =>
    have e : FreeGroup.mk (x :: w) = FreeGroup.mk [x] * FreeGroup.mk w := rfl
    obtain ⟨i, b⟩ := x
    have hx : FreeGroup.lift gM (FreeGroup.mk [(i, b)]) =
        if b then gMArr.getD i.val 1 else (gMArr.getD i.val 1)⁻¹ := by
      rw [gMArr_getD]
      cases b with
      | true =>
        have e1 : FreeGroup.mk [(i, true)] = FreeGroup.of i := rfl
        rw [e1, FreeGroup.lift_apply_of, ite_eq_left rfl]
      | false =>
        have e1 : FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ := rfl
        rw [e1, map_inv, FreeGroup.lift_apply_of, ite_eq_right Bool.false_ne_true]
    rw [e, map_mul, ih, hx, relWord_eq, relWord_eq]
    unfold wordG
    rw [List.map_cons, List.map_cons, List.prod_cons]

theorem relOKM_spec (hg : chkGensM = true) {r : List (Fin 8 × Bool)} (h : relOKM r = true) :
    FreeGroup.lift gM (FreeGroup.mk r) = 1 := by
  rw [lift_gM_mk]
  refine mrep_eq (mrep_wordC (R := gMArr) _ fun l hl => ?_) mrep_idM h
  rw [relWord_eq, List.mem_map] at hl
  obtain ⟨⟨i, b⟩, -, rfl⟩ := hl
  dsimp only
  rw [gMArr_getD]
  exact (chkGensM_spec hg i).1

theorem chkNontrivM_spec (hg : chkGensM = true) (h : chkNontrivM = true) :
    gM 0 * gM 1 ≠ gM 1 * gM 0 ∧ gM 7 ≠ 1 := by
  rw [chkNontrivM, bAnd_eq] at h
  have v0 : ((0 : Fin 8) : ℕ) = 0 := rfl
  have v1 : ((1 : Fin 8) : ℕ) = 1 := rfl
  have v7 : ((7 : Fin 8) : ℕ) = 7 := rfl
  have g0 := (chkGensM_spec hg 0).1.1
  have g1 := (chkGensM_spec hg 1).1.1
  have g7 := (chkGensM_spec hg 7).1.1
  rw [v0] at g0
  rw [v1] at g1
  rw [v7] at g7
  have n01 := mrep_ne (mrep_mmul g0 g1) (mrep_mmul g1 g0) h.1
  have n7 := mrep_ne g7 mrep_idM h.2
  exact ⟨n01, n7⟩

section Program

variable {X : Type*} [Group X]

@[expose] def opG (R : Array X) : SOp → X
  | .word w => wordG R w
  | .pow e i => R.getD i 1 ^ e

@[expose] def opIdxLt (n : ℕ) : SOp → Bool
  | .word w => w.all fun l => l.1 < n
  | .pow _ i => i < n

theorem stepG_eq (R : Array X) (o : SOp) : stepG R o = R.push (opG R o) := by
  cases o <;> rfl

theorem getD_push_lt (R : Array X) (y : X) {k : ℕ} (hk : k < R.size) :
    (R.push y).getD k 1 = R.getD k 1 := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, Nat.ne_of_lt hk]

theorem getD_push_size (R : Array X) (y : X) : (R.push y).getD R.size 1 = y := by
  simp [Array.getD_eq_getD_getElem?]

theorem runG_getD_lt : ∀ (prog : List SOp) (R : Array X) {k : ℕ}, k < R.size →
    (runG R prog).getD k 1 = R.getD k 1
  | [], _, _, _ => rfl
  | o :: prog, R, k, hk => by
    change (runG (stepG R o) prog).getD k 1 = _
    rw [runG_getD_lt prog _ (by rw [size_stepG]; omega), stepG_eq]
    exact getD_push_lt _ _ hk

theorem runG_getD_add : ∀ (prog : List SOp) (R : Array X) (t : ℕ), t < prog.length →
    (runG R prog).getD (R.size + t) 1 = opG (runG R (prog.take t)) (prog.getD t (.pow 0 0))
  | [], _, _, ht => absurd ht (by simp)
  | o :: prog, R, 0, _ => by
    change (runG (stepG R o) prog).getD (R.size + 0) 1 = opG R o
    rw [runG_getD_lt prog _ (by rw [size_stepG]; omega), stepG_eq, Nat.add_zero, getD_push_size]
  | o :: prog, R, t + 1, ht => by
    change (runG (stepG R o) prog).getD (R.size + (t + 1)) 1 =
      opG (runG (stepG R o) (prog.take t)) (prog.getD t (.pow 0 0))
    have e : R.size + (t + 1) = (stepG R o).size + t := by
      rw [size_stepG]
      omega
    rw [e]
    exact runG_getD_add prog (stepG R o) t (by simp at ht; omega)

theorem runG_take_getD (prog : List SOp) (R : Array X) (t : ℕ) {k : ℕ}
    (hk : k < R.size + min t prog.length) :
    (runG R (prog.take t)).getD k 1 = (runG R prog).getD k 1 := by
  have e : runG R prog = runG (runG R (prog.take t)) (prog.drop t) := by
    rw [runG, runG, runG, ← List.foldl_append, List.take_append_drop]
  rw [e, runG_getD_lt (prog.drop t) (runG R (prog.take t))
    (by rw [size_runG, List.length_take]; omega)]

theorem opG_congr {R R' : Array X} {n : ℕ} (h : ∀ i < n, R.getD i 1 = R'.getD i 1)
    {o : SOp} (ho : opIdxLt n o = true) : opG R o = opG R' o := by
  cases o with
  | word w =>
    change wordG R w = wordG R' w
    rw [opIdxLt, List.all_eq_true] at ho
    unfold wordG
    congr 1
    refine List.map_congr_left fun l hl => ?_
    rw [h l.1 (of_decide_eq_true (ho l hl))]
  | pow e i =>
    change R.getD i 1 ^ e = R'.getD i 1 ^ e
    rw [opIdxLt] at ho
    rw [h i (of_decide_eq_true ho)]

end Program

theorem progM_length : progM.length = 192 := by decide +kernel

theorem progM_idx : ∀ t < 192, opIdxLt (8 + t) (progM.getD t (.pow 0 0)) = true := by
  decide +kernel

@[expose, irreducible] noncomputable def regM : Array Mat45ˣ := runG gMArr progM

@[expose, irreducible] noncomputable def regMat (r : ℕ) : Mat45 := decC 45 (nthN regC r)
@[expose, irreducible] noncomputable def regIMat (r : ℕ) : Mat45 := decC 45 (nthN regIC r)

theorem rM_eq (r : ℕ) : rM r = enc (regMat r) := by
  unfold rM regMat
  exact widen_eq _
theorem rIM_eq (r : ℕ) : rIM r = enc (regIMat r) := by
  unfold rIM regIMat
  exact widen_eq _

theorem mrep_opValC {F FI : ℕ → ℕ} {R : Array Mat45ˣ} {o : SOp} {n : ℕ}
    (ho : opIdxLt n o = true) (h : ∀ i < n, MRep (F i) (R.getD i 1) ∧ MRep (FI i) (R.getD i 1)⁻¹) :
    MRep (opValC F FI o) (opG R o) := by
  cases o with
  | word w =>
    rw [opIdxLt, List.all_eq_true] at ho
    exact mrep_wordC w fun l hl => h l.1 (of_decide_eq_true (ho l hl))
  | pow e i =>
    rw [opIdxLt] at ho
    exact mrep_powM (h i (of_decide_eq_true ho)).1 e

theorem mrep_runG {F FI : ℕ → ℕ} {R0 : Array Mat45ˣ} {prog : List SOp}
    (hidx : ∀ t < prog.length, opIdxLt (R0.size + t) (prog.getD t (.pow 0 0)) = true)
    (hFI : ∀ r, ∃ B : Mat45, FI r = enc B)
    (h0 : ∀ r < R0.size, MRep (F r) (R0.getD r 1) ∧ MRep (FI r) (R0.getD r 1)⁻¹)
    (hr : ∀ r, R0.size ≤ r → r < R0.size + prog.length → chkProgReg F FI prog R0.size r = true) :
    ∀ r < R0.size + prog.length,
      MRep (F r) ((runG R0 prog).getD r 1) ∧ MRep (FI r) ((runG R0 prog).getD r 1)⁻¹ := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hrl
    by_cases h8 : r < R0.size
    · rw [runG_getD_lt _ _ h8]
      exact h0 r h8
    · obtain ⟨t, rfl⟩ : ∃ t, r = R0.size + t := ⟨r - R0.size, by omega⟩
      have hlen : t < prog.length := by omega
      have hval : (runG R0 prog).getD (R0.size + t) 1 =
          opG (runG R0 prog) (prog.getD t (.pow 0 0)) := by
        rw [runG_getD_add _ _ _ hlen]
        exact opG_congr (fun i hi => runG_take_getD _ _ _ (by omega)) (hidx t hlen)
      have hc := hr _ (by omega) hrl
      rw [chkProgReg, bAnd_eq] at hc
      have e : Nat.sub (R0.size + t) R0.size = t := Nat.add_sub_cancel_left R0.size t
      rw [e, nthOp_eq] at hc
      have h1 : MRep (F (R0.size + t)) ((runG R0 prog).getD (R0.size + t) 1) := by
        rw [hval]
        unfold MRep
        rw [Nat.eq_of_beq_eq_true hc.1]
        exact mrep_opValC (hidx t hlen) fun i hi =>
          ih i hi (lt_of_lt_of_le hi (Nat.add_le_add_left hlen.le _))
      obtain ⟨B, hB⟩ := hFI (R0.size + t)
      exact ⟨h1, mrep_inv h1 hB hc.2⟩

theorem mrep_regM (hg : chkGensM = true) (hr : ∀ r, 8 ≤ r → r < 200 → chkRegM r = true) :
    ∀ r < 200, MRep (rM r) (regM.getD r 1) ∧ MRep (rIM r) (regM.getD r 1)⁻¹ := by
  have h0 : ∀ r < gMArr.size, MRep (rM r) (gMArr.getD r 1) ∧ MRep (rIM r) (gMArr.getD r 1)⁻¹ := by
    intro r hr8
    rw [size_gMArr] at hr8
    obtain ⟨⟨hm, hmi⟩, hreg, hregi⟩ := chkGensM_spec hg ⟨r, hr8⟩
    have hreg' : nthN regC r = nthN genC r := hreg
    have hregi' : nthN regIC r = nthN genIC r := hregi
    have e : gMArr.getD r 1 = gM ⟨r, hr8⟩ := gMArr_getD ⟨r, hr8⟩
    rw [e]
    refine ⟨?_, ?_⟩
    · have e1 : rM r = genM r := by
        unfold rM genM
        rw [hreg']
      rw [e1]
      exact hm
    · have e1 : rIM r = genIM r := by
        unfold rIM genIM
        rw [hregi']
      rw [e1]
      exact hmi
  have h := mrep_runG (F := rM) (FI := rIM) (R0 := gMArr) (prog := progM)
    (by rw [size_gMArr, progM_length]; exact progM_idx) (fun r => ⟨_, rIM_eq r⟩) h0
    (fun r h1 h2 => by
      rw [size_gMArr] at h1 h2 ⊢
      rw [progM_length] at h2
      exact hr r h1 h2)
  intro r hr200
  rw [regM]
  exact h r (by rw [size_gMArr, progM_length]; omega)

abbrev Sub7 := Submodule (ZMod 7) (Fin 45 → ZMod 7)

noncomputable instance : DecidableEq Sub7 := Classical.decEq _

theorem vml_mul (A B : Mat45) : (A * B).vecMulLinear = B.vecMulLinear.comp A.vecMulLinear :=
  LinearMap.ext fun v => by simp [Matrix.vecMul_vecMul]

theorem vml_one : (1 : Mat45).vecMulLinear = LinearMap.id :=
  LinearMap.ext fun v => by simp

theorem map_vml_mul (A B : Mat45) (U : Sub7) :
    U.map (A * B).vecMulLinear = (U.map A.vecMulLinear).map B.vecMulLinear := by
  rw [vml_mul, Submodule.map_comp]

@[expose] noncomputable def ptAct : Mat45ˣ →* Equiv.Perm Sub7 where
  toFun g :=
    { toFun := fun U => U.map ((g⁻¹ : Mat45ˣ) : Mat45).vecMulLinear
      invFun := fun U => U.map (g : Mat45).vecMulLinear
      left_inv := fun U => by
        change (U.map _).map _ = U
        rw [← map_vml_mul, Units.inv_mul, vml_one, Submodule.map_id]
      right_inv := fun U => by
        change (U.map _).map _ = U
        rw [← map_vml_mul, Units.mul_inv, vml_one, Submodule.map_id] }
  map_one' := Equiv.ext fun U => by
    change U.map (((1 : Mat45ˣ)⁻¹ : Mat45ˣ) : Mat45).vecMulLinear = U
    rw [inv_one, Units.val_one, vml_one, Submodule.map_id]
  map_mul' g h := Equiv.ext fun U => by
    change U.map (((g * h)⁻¹ : Mat45ˣ) : Mat45).vecMulLinear =
      (U.map ((h⁻¹ : Mat45ˣ) : Mat45).vecMulLinear).map ((g⁻¹ : Mat45ˣ) : Mat45).vecMulLinear
    rw [mul_inv_rev, Units.val_mul, map_vml_mul]

theorem ptAct_apply (g : Mat45ˣ) (U : Sub7) :
    ptAct g U = U.map ((g⁻¹ : Mat45ˣ) : Mat45).vecMulLinear := rfl

@[expose, irreducible] noncomputable def ptMat (t : ℕ) : Matrix (Fin 8) (Fin 45) (ZMod 7) :=
  decC 8 (nthN ptsC t)

@[expose, irreducible] noncomputable def pt (t : ℕ) : Sub7 := rowSpan (ptMat t)

theorem ptM_eq (t : ℕ) : ptM t = enc (ptMat t) := by
  unfold ptM ptMat
  exact widenR_eq 8 _

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem chkPtsM_spec (h : ∀ q < 3, chkPtsM (20 * q) 20 = true) :
    (∀ t < 60, pivOK (ptM t) (pvM t) = true) ∧ ∀ s < 60, ∀ t < 60, s ≠ t → pt s ≠ pt t := by
  have h1 : ∀ s < 60, pivOK (ptM s) (pvM s) = true ∧
      ∀ t < 60, s = t ∨ inSpan (ptM s) (ptM t) (pvM t) = false := by
    intro s hs
    have h0 := h (s / 20) (by omega)
    rw [chkPtsM] at h0
    have h2 := (allN_iff 20 _).1 h0 (s % 20) (Nat.mod_lt _ (by norm_num))
    rw [strictB_eq] at h2
    have e : Nat.add (20 * (s / 20)) (s % 20) = s := Nat.add_eq.trans (by omega)
    rw [e, bAnd_eq] at h2
    refine ⟨h2.1, fun t ht => ?_⟩
    have h3 := (allN_iff 60 _).1 h2.2 t ht
    rw [bIf_true_eq, Nat.beq_eq, bNot_eq] at h3
    exact h3
  refine ⟨fun t ht => (h1 t ht).1, fun s hs t ht hst => ?_⟩
  rcases (h1 s hs).2 t ht with e | e
  · exact absurd e hst
  · rw [ptM_eq, ptM_eq] at e
    have hp := (h1 t ht).1
    rw [ptM_eq] at hp
    unfold pt
    exact rowSpan_ne hp e

@[expose] def MapsB (g : Mat45ˣ) (σ : List ℕ) : Prop :=
  ∀ t < 60, ∃ u < 60, u / 10 = σ.getD (t / 10) 0 ∧ ptAct g (pt t) = pt u

theorem mapsBlocksM_spec (hpiv : ∀ t < 60, pivOK (ptM t) (pvM t) = true) {gI : ℕ}
    {g : Mat45ˣ} (hg : MRep gI g⁻¹) {σ : List ℕ} {k : ℕ} (h : mapsBlocksM gI σ k = true) :
    MapsB g σ := by
  intro t ht
  rw [mapsBlocksM] at h
  have h1 := (allN_iff 60 _).1 h t ht
  rw [mapsBlocksM.mapsPt, strictB_eq, mapsBlocksM.mapsAt, bAnd_eq, bAnd_eq, Nat.blt_eq,
    Nat.beq_eq] at h1
  obtain ⟨hu, hb, hs⟩ := h1
  rw [nthN_eq σ] at hb
  refine ⟨_, hu, hb, ?_⟩
  have hpt := hpiv t ht
  have hpu := hpiv _ hu
  unfold MRep at hg
  rw [ptM_eq] at hpt hpu
  rw [ptM_eq, ptM_eq] at hs
  rw [hg] at hs
  rw [ptAct_apply, pt, pt, ← rowSpan_mul]
  exact rowSpan_mul_eq hpt hpu (Units.inv_mul g) hs

theorem out_spec (hpiv : ∀ t < 60, pivOK (ptM t) (pvM t) = true) {gI : ℕ} {g : Mat45ˣ}
    (hg : MRep gI g⁻¹)
    (h : (strictB (imgS (ptM 0) gI) fun U => allN 60 fun t =>
      notB (inSpan U (ptM t) (pvM t))) = true) :
    ∀ t < 60, ptAct g (pt 0) ≠ pt t := by
  intro t ht
  unfold MRep at hg
  rw [strictB_eq] at h
  have h1 := (allN_iff 60 _).1 h t ht
  rw [bNot_eq, ptM_eq, hg, imgS_enc, ptM_eq] at h1
  have hpu := hpiv t ht
  rw [ptM_eq] at hpu
  rw [ptAct_apply, pt, pt, ← rowSpan_mul]
  exact rowSpan_ne hpu h1

noncomputable abbrev eM (r : ℕ) : Mat45ˣ := regM.getD r 1

@[expose] def RegOK : Prop := ∀ r < 200, MRep (rM r) (eM r) ∧ MRep (rIM r) (eM r)⁻¹

theorem allL_iff {α : Type} (l : List α) (f : α → Bool) :
    allL l f = true ↔ ∀ d ∈ l, f d = true := by
  induction l with
  | nil => exact ⟨fun _ d hd => by simp at hd, fun _ => rfl⟩
  | cons x l ih =>
    change andB (f x) (allL l f) = true ↔ _
    rw [bAnd_eq, ih, List.forall_mem_cons]

theorem anyLN_iff (l : List ℕ) (f : ℕ → Bool) : anyLN l f = true ↔ ∃ x ∈ l, f x = true := by
  induction l with
  | nil => exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨_, hx, _⟩ => by simp at hx⟩
  | cons x l ih =>
    change ifB (f x) true (anyLN l f) = true ↔ _
    rw [bIf_true_eq, ih]
    simp only [List.mem_cons, exists_eq_or_imp]

theorem nthLN_eq (l : List (List ℕ)) (i : ℕ) : nthLN l i = l.getD i [] := by
  induction l generalizing i with
  | nil => rfl
  | cons x l ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem nthN_lt {l : List ℕ} {n : ℕ} (h : ∀ x ∈ l, x < n) (hn : 0 < n) (i : ℕ) :
    nthN l i < n := by
  rw [nthN_eq, List.getD_eq_getElem?_getD]
  cases hx : l[i]? with
  | none => exact hn
  | some x => exact h x (List.mem_of_getElem? hx)

theorem rX_lt : ∀ x ∈ rX, x < 200 := by decide

theorem regs_lt : rN1 < 200 ∧ rN2 < 200 ∧ rK1 < 200 ∧ rK2 < 200 ∧ rY1 < 200 ∧ rY3 < 200 ∧
    rX12 < 200 := by decide

theorem mrep_x (hR : RegOK) (i : ℕ) :
    MRep (rM (nthN rX i)) (eM (nthN rX i)) ∧ MRep (rIM (nthN rX i)) (eM (nthN rX i))⁻¹ :=
  hR _ (nthN_lt rX_lt (by norm_num) i)

theorem chkP0M_spec (hR : RegOK) (h : chkP0M = true) :
    (∀ r ∈ rX, eM r ^ 3 = 1) ∧ ∀ i < 4, ∀ j < 4, i ≠ j →
      eM (rX.getD i 0) * (eM (rX.getD j 0) * ((eM (rX.getD i 0))⁻¹ * (eM (rX.getD j 0))⁻¹)) =
        eM 7 ^ omegaN i j := by
  rw [chkP0M, bAnd_eq] at h
  refine ⟨fun r hr => mrep_eq (mrep_powM (hR r (rX_lt r hr)).1 3) mrep_idM
    ((allL_iff _ _).1 h.1 r hr), fun i hi j hj hij => ?_⟩
  have h1 := (allN_iff 4 _).1 ((allN_iff 4 _).1 h.2 i hi) j hj
  rw [bIf_true_eq, Nat.beq_eq] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 hij
  · have := mrep_eq (mrep_mmul (mrep_x hR i).1 (mrep_mmul (mrep_x hR j).1
      (mrep_mmul (mrep_x hR i).2 (mrep_x hR j).2))) (mrep_powM (hR 7 (by norm_num)).1 _) h1
    simp only [nthN_eq] at this
    exact this

theorem conjData_lt : ∀ d ∈ conjData, d.1 < 200 := by decide

theorem chkConjM_spec (hR : RegOK) (h : chkConjM = true) :
    ∀ d ∈ conjData, (eM d.1)⁻¹ * (eM (rX.getD d.2.1 0) * eM d.1) =
      eM (rX.getD 3 0) ^ d.2.2.2.getD 3 0 * (eM (rX.getD 2 0) ^ d.2.2.2.getD 2 0 *
        (eM (rX.getD 1 0) ^ d.2.2.2.getD 1 0 * (eM (rX.getD 0 0) ^ d.2.2.2.getD 0 0 *
          eM 7 ^ d.2.2.1))) := by
  intro d hd
  rw [chkConjM] at h
  have h1 := (allL_iff _ _).1 h d hd
  have hn := hR d.1 (conjData_lt d hd)
  obtain ⟨n, i, c, e⟩ := d
  have := mrep_eq (mrep_mmul hn.2 (mrep_mmul (mrep_x hR i).1 hn.1))
    (mrep_mmul (mrep_powM (mrep_x hR 3).1 _) (mrep_mmul (mrep_powM (mrep_x hR 2).1 _)
      (mrep_mmul (mrep_powM (mrep_x hR 1).1 _) (mrep_mmul (mrep_powM (mrep_x hR 0).1 _)
        (mrep_powM (hR 7 (by norm_num)).1 c))))) h1
  simp only [nthN_eq] at this
  exact this

theorem chkK0M_spec (hR : RegOK) (h : chkK0M = true) :
    (eM rK1 * eM (rX.getD 0 0) = eM (rX.getD 0 0) * eM rK1 ∧
      eM rK2 * eM (rX.getD 0 0) = eM (rX.getD 0 0) * eM rK2) ∧
    eM rY1 = eM (rX.getD 1 0) ∧ eM rY3 = eM rX12 := by
  rw [chkK0M, bAnd_eq, bAnd_eq, allL_iff] at h
  obtain ⟨hk, h1, h3⟩ := h
  have hx := mrep_x hR 0
  rw [nthN_eq] at hx
  obtain ⟨h1', h2', h3', h4', h5', h6', h7'⟩ := regs_lt
  have hc : ∀ k ∈ [rK1, rK2], k < 200 → eM k * eM (rX.getD 0 0) = eM (rX.getD 0 0) * eM k :=
    fun k hk' hk200 => by
      have := hk k hk'
      rw [nthN_eq] at this
      exact mrep_eq (mrep_mmul (hR k hk200).1 hx.1) (mrep_mmul hx.1 (hR k hk200).1) this
  refine ⟨⟨hc _ (by simp) h3', hc _ (by simp) h4'⟩, ?_, ?_⟩
  · have := mrep_eq (hR _ h5').1 (mrep_x hR 1).1 h1
    rw [nthN_eq] at this
    exact this
  · exact mrep_eq (hR _ h6').1 (hR _ h7').1 h3

theorem chkBlocksM_spec (hR : RegOK) (hpiv : ∀ t < 60, pivOK (ptM t) (pvM t) = true)
    (h : chkBlocksM = true) :
    (MapsB (eM rK1) sigK1 ∧ MapsB (eM rK2) sigK2 ∧ MapsB (eM 7) [0, 1, 2, 3, 4, 5]) ∧
      ∀ t < 60, ptAct (eM (rX.getD 0 0)) (pt 0) ≠ pt t := by
  rw [chkBlocksM, bAnd_eq, bAnd_eq, bAnd_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨-, -, hk1, hk2, -⟩ := regs_lt
  refine ⟨⟨mapsBlocksM_spec hpiv (hR _ hk1).2 h1, mapsBlocksM_spec hpiv (hR _ hk2).2 h2,
    mapsBlocksM_spec hpiv (hR 7 (by norm_num)).2 h3⟩, ?_⟩
  have := out_spec hpiv (mrep_x hR 0).2 h4
  rw [nthN_eq] at this
  exact this

abbrev vRegI (j m i : ℕ) : ℕ := ((rV.getD j []).getD m []).getD i 0

theorem vRegs_eq : ∀ j < 2, ∀ m < 3, vRegs j m = (rV.getD j []).getD m [] := by decide +kernel

theorem sigVM_eq : ∀ j < 2, ∀ m < 3, ∀ i < 3,
    sigVM j m i = ((sigV.getD j []).getD m []).getD i [] := by decide +kernel

theorem vRegI_lt : ∀ j < 2, ∀ m < 3, ∀ i < 3, vRegI j m i < 200 := by decide +kernel

theorem vRegI_mem : ∀ j < 2, ∀ m < 3, ∀ i < 3, vRegI j m i ∈ vRegs j m := by decide +kernel

theorem vRegs_len : ∀ j < 2, ∀ m < 3, ∀ x ∈ vRegs j m, ∃ i < 3, x = vRegI j m i := by
  decide +kernel

theorem yRegM_eq {j : ℕ} (hj : j < 2) : yRegM j = if j = 0 then rX.getD 1 0 else rX12 := by
  interval_cases j <;> decide +kernel

theorem vOKM_spec (hR : RegOK) (hpiv : ∀ t < 60, pivOK (ptM t) (pvM t) = true) {j m : ℕ}
    (hj : j < 2) (hm : m < 3) (h : vOKM j m = true) :
    let v := fun i => eM (vRegI j m i)
    let y := eM (if j = 0 then rX.getD 1 0 else rX12)
    v 0 * v 1 = v 2 ∧ v 1 * v 0 = v 2 ∧ (∀ i < 3, v i * v i = 1 ∧ v i ≠ 1) ∧
      (∀ i < 3, ∃ i' < 3, y⁻¹ * (v i * y) = v i') ∧
      ∀ i < 3, MapsB (v i) (((sigV.getD j []).getD m []).getD i []) := by
  intro v y
  have hv : ∀ i, nthN (vRegs j m) i = vRegI j m i := fun i => by
    rw [vRegs_eq j hj m hm, nthN_eq]
  have hR' : ∀ i < 3, MRep (rM (nthN (vRegs j m) i)) (v i) ∧
      MRep (rIM (nthN (vRegs j m) i)) (v i)⁻¹ := fun i hi => by
    rw [hv i]
    exact hR _ (vRegI_lt j hj m hm i hi)
  have hy : MRep (rM (yRegM j)) y ∧ MRep (rIM (yRegM j)) y⁻¹ := by
    rw [yRegM_eq hj]
    refine hR _ ?_
    split_ifs <;> decide
  rw [vOKM] at h
  simp only [strictB_eq] at h
  rw [bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq, allL_iff, allL_iff, allN_iff] at h
  obtain ⟨h01, h10, hsq, hcj, hmb⟩ := h
  have hmem : ∀ i < 3, rM (nthN (vRegs j m) i) ∈
      [rM (nthN (vRegs j m) 0), rM (nthN (vRegs j m) 1), rM (nthN (vRegs j m) 2)] := by
    intro i hi
    interval_cases i <;> simp
  refine ⟨mrep_eq (mrep_mmul (hR' 0 (by norm_num)).1 (hR' 1 (by norm_num)).1)
      (hR' 2 (by norm_num)).1 h01,
    mrep_eq (mrep_mmul (hR' 1 (by norm_num)).1 (hR' 0 (by norm_num)).1)
      (hR' 2 (by norm_num)).1 h10, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · have h1 := hsq _ (hmem i hi)
    rw [bAnd_eq] at h1
    exact ⟨mrep_eq (mrep_mmul (hR' i hi).1 (hR' i hi).1) mrep_idM h1.1,
      mrep_ne (hR' i hi).1 mrep_idM h1.2⟩
  · obtain ⟨x, hx, hb⟩ := (anyLN_iff _ _).1 (hcj _ (hmem i hi))
    have hc := mrep_mmul hy.2 (mrep_mmul (hR' i hi).1 hy.1)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, by norm_num, mrep_eq hc (hR' 0 (by norm_num)).1 hb⟩
    · exact ⟨1, by norm_num, mrep_eq hc (hR' 1 (by norm_num)).1 hb⟩
    · exact ⟨2, by norm_num, mrep_eq hc (hR' 2 (by norm_num)).1 hb⟩
  · rw [← sigVM_eq j hj m hm i hi]
    exact mapsBlocksM_spec hpiv (hR' i hi).2 (hmb i hi)

theorem chkVM_spec (h : chkVM = true) {j m : ℕ} (hj : j < 2) (hm : m < 3) :
    vOKM j m = true := by
  rw [chkVM] at h
  exact (allN_iff 3 _).1 ((allN_iff 2 _).1 h j hj) m hm

theorem rL_lt : ∀ j < 2, ∀ l < 4, (rL.getD j []).getD l 0 < 200 := by decide +kernel

theorem nthW_eq : ∀ t < 108, chkWitM.nthW witData t = witData.getD t (0, 0, 0, 0, 0) := by
  decide +kernel

theorem witData_length : witData.length = 108 := by decide +kernel

theorem witData_bounds : ∀ d ∈ witData, d.1 < 2 ∧ d.2.1 < 4 ∧ d.2.2.1 < 4 ∧ d.2.2.2.1 < 3 ∧
    d.2.2.2.2 < 3 := by decide +kernel

theorem chkWitM_spec (hR : RegOK) (h : ∀ q < 12, chkWitM (9 * q) 9 = true) :
    ∀ d ∈ witData,
      let n₁ := eM ((rL.getD d.1 []).getD d.2.1 0)
      let n₂ := eM ((rL.getD d.1 []).getD d.2.2.1 0)
      let t₀ := n₁⁻¹ * (eM (vRegI d.1 d.2.2.2.1 0) * n₁)
      let s₀ := n₂⁻¹ * (eM (vRegI d.1 d.2.2.2.2 0) * n₂)
      let s₁ := n₂⁻¹ * (eM (vRegI d.1 d.2.2.2.2 1) * n₂)
      (s₁ * (t₀ * (s₀ * t₀))) ^ 3 = 1 ∧ s₁ * (t₀ * (s₀ * t₀)) ≠ 1 := by
  intro d hd
  obtain ⟨t, ht, hdt⟩ := List.getElem_of_mem hd
  have ht' : t < 108 := by rw [← witData_length]; exact ht
  have h0 := h (t / 9) (by omega)
  rw [chkWitM] at h0
  have h1 := (allN_iff 9 _).1 h0 (t % 9) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (9 * (t / 9)) (t % 9) = t := Nat.add_eq.trans (by omega)
  rw [e, nthW_eq t ht', List.getD_eq_getElem _ _ ht, hdt] at h1
  obtain ⟨hj, hl1, hl2, hv1, hv2⟩ := witData_bounds d hd
  obtain ⟨j, l1, l2, v1, v2⟩ := d
  intro n₁ n₂ t₀ s₀ s₁
  rw [witOKM] at h1
  dsimp only at h1
  rw [strictB_eq, witOKM.witS0, strictB_eq, witOKM.witS1, strictB_eq, witOKM.witU, strictB_eq,
    witOKM.witB, bAnd_eq] at h1
  have hn : ∀ l < 4, nthN (nthLN rL j) l = (rL.getD j []).getD l 0 := fun l _ => by
    rw [nthN_eq, nthLN_eq]
  have hvr : ∀ m < 3, ∀ i < 3, nthN (vRegs j m) i = vRegI j m i := fun m hm i _ => by
    rw [vRegs_eq j hj m hm, nthN_eq]
  have pn : ∀ l < 4, MRep (rM (nthN (nthLN rL j) l)) (eM ((rL.getD j []).getD l 0)) ∧
      MRep (rIM (nthN (nthLN rL j) l)) (eM ((rL.getD j []).getD l 0))⁻¹ := fun l hl => by
    rw [hn l hl]
    exact hR _ (rL_lt j hj l hl)
  have pv : ∀ m < 3, ∀ i < 3, MRep (rM (nthN (vRegs j m) i)) (eM (vRegI j m i)) := fun m hm i hi => by
    rw [hvr m hm i hi]
    exact (hR _ (vRegI_lt j hj m hm i hi)).1
  have pw : ∀ l < 4, ∀ m < 3, ∀ i < 3, MRep (witOKM.witT j l m i)
      ((eM ((rL.getD j []).getD l 0))⁻¹ * (eM (vRegI j m i) * eM ((rL.getD j []).getD l 0))) :=
    fun l hl m hm i hi => by
      unfold witOKM.witT conjM
      exact mrep_mmul (pn l hl).2 (mrep_mmul (pv m hm i hi) (pn l hl).1)
  have pu : MRep (mmul (witOKM.witT j l2 v2 1) (mmul (witOKM.witT j l1 v1 0)
      (mmul (witOKM.witT j l2 v2 0) (witOKM.witT j l1 v1 0)))) (s₁ * (t₀ * (s₀ * t₀))) := by
    exact mrep_mmul (pw l2 hl2 v2 hv2 1 (by norm_num)) (mrep_mmul (pw l1 hl1 v1 hv1 0 (by norm_num))
      (mrep_mmul (pw l2 hl2 v2 hv2 0 (by norm_num)) (pw l1 hl1 v1 hv1 0 (by norm_num))))
  exact ⟨mrep_eq (mrep_powM pu 3) mrep_idM h1.1, mrep_ne pu mrep_idM h1.2⟩

theorem mrep_wordNM (hR : RegOK) (w : List ℕ) :
    MRep (wordNM w) ((w.map fun k => eM (if k = 0 then rN1 else rN2)).prod) := by
  induction w with
  | nil => exact mrep_idM
  | cons k w ih =>
    rw [List.map_cons, List.prod_cons]
    have e : ifN (Nat.beq k 0) rN1 rN2 = if k = 0 then rN1 else rN2 := by
      rw [nIf_eq]
      by_cases hk : k = 0
      · rw [ite_eq_left (by rw [hk]; rfl), ite_eq_left hk]
      · rw [ite_eq_right (by rw [Nat.beq_eq]; exact hk), ite_eq_right hk]
    have hk : (if k = 0 then rN1 else rN2) < 200 := by
      split_ifs
      · exact regs_lt.1
      · exact regs_lt.2.1
    change MRep (mmul (rM (ifN (Nat.beq k 0) rN1 rN2)) (wordNM w)) _
    rw [e]
    exact mrep_mmul (hR _ hk).1 ih

theorem lineW_eq : ∀ j < 2, ∀ l < 4, chkLM.lineW j l = (lineWords.getD j []).getD l [] := by
  decide +kernel

theorem chkLM_spec (hR : RegOK) (h : chkLM = true) {j l : ℕ} (hj : j < 2) (hl : l < 4) :
    eM ((rL.getD j []).getD l 0) =
      (((lineWords.getD j []).getD l []).map fun k => eM (if k = 0 then rN1 else rN2)).prod := by
  rw [chkLM] at h
  have h1 := (allN_iff 4 _).1 ((allN_iff 2 _).1 h j hj) l hl
  rw [lineW_eq j hj l hl, nthLN_eq, nthN_eq] at h1
  have hp := (hR _ (rL_lt j hj l hl)).1
  exact mrep_eq hp (mrep_wordNM hR _) h1

theorem chkVx0M_spec (hR : RegOK) (h : chkVx0M = true) {j m i : ℕ} (hj : j < 2) (hm : m < 3)
    (hi : i < 3) :
    eM (vRegI j m i) * eM (rX.getD 0 0) = eM (rX.getD 0 0) * eM (vRegI j m i) := by
  rw [chkVx0M] at h
  have h1 := (allL_iff _ _).1 ((allN_iff 3 _).1 ((allN_iff 2 _).1 h j hj) m hm) _
    (vRegI_mem j hj m hm i hi)
  have hx := mrep_x hR 0
  have hv := hR _ (vRegI_lt j hj m hm i hi)
  have := mrep_eq (mrep_mmul hv.1 hx.1) (mrep_mmul hx.1 hv.1) h1
  rw [nthN_eq] at this
  exact this

theorem chkYM_spec (hR : RegOK) (hpiv : ∀ t < 60, pivOK (ptM t) (pvM t) = true)
    (h : chkYM = true) :
    MapsB (eM rY1) (sYList.getD 0 []) ∧ MapsB (eM rY3) (sYList.getD 1 []) := by
  rw [chkYM, bAnd_eq, nthLN_eq, nthLN_eq] at h
  exact ⟨mapsBlocksM_spec hpiv (hR _ regs_lt.2.2.2.2.1).2 h.1,
    mapsBlocksM_spec hpiv (hR _ regs_lt.2.2.2.2.2.1).2 h.2⟩

theorem chkX12M_spec (hR : RegOK) (h : chkX12M = true) :
    eM rX12 = eM (rX.getD 1 0) * eM (rX.getD 2 0) := by
  have := mrep_eq (hR _ regs_lt.2.2.2.2.2.2).1 (mrep_mmul (mrep_x hR 1).1 (mrep_x hR 2).1) h
  simp only [nthN_eq] at this
  exact this

end CFSG.RankThree.Native.ONTriple

end
