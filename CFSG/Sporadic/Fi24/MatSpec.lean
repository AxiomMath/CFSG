module

public import CFSG.Sporadic.Fi24.WSpec
public import Certificates.Data.CFSGNative.Fi24.Sep

public section

namespace CFSG.Sporadic.Fi24.Native

open CFSG.F3.Native Finset

@[expose] def rowW (X : Array W) (i : ℕ) : W := X[i]?.getD W.zero

@[expose] def matW (r c : ℕ) (X : Array W) : Matrix (Fin r) (Fin c) (ZMod 3) :=
  Matrix.of fun i j => (rowW X i.val).val j.val

theorem matW_apply (r c : ℕ) (X : Array W) (i : Fin r) (j : Fin c) :
    matW r c X i j = (rowW X i.val).val j.val := rfl

@[expose] def RowsWF (X : Array W) : Prop := ∀ x ∈ X, x.wf = true

theorem RowsWF.row {X : Array W} (h : RowsWF X) (i : ℕ) : (rowW X i).wf = true := by
  unfold rowW
  cases hx : X[i]? with
  | none => exact W.wf_zero
  | some x => exact h x (Array.mem_of_getElem? hx)

theorem rowW_getElem! (X : Array W) (i : ℕ) : X[i]! = rowW X i := by
  unfold rowW
  rw [getElem!_def]
  cases X[i]? <;> rfl

theorem rowW_ofFn {n : ℕ} (f : Fin n → W) (i : ℕ) :
    rowW (Array.ofFn f) i = if h : i < n then f ⟨i, h⟩ else W.zero := by
  unfold rowW
  rw [Array.getElem?_ofFn]
  split_ifs <;> rfl

theorem rowW_map (f : W → W) (X : Array W) (hf : f W.zero = W.zero) (i : ℕ) :
    rowW (X.map f) i = f (rowW X i) := by
  unfold rowW
  rw [Array.getElem?_map]
  cases X[i]? <;> simp [hf]

theorem tritVal_mod (n : ℕ) : tritVal (n % 3) = (n : ZMod 3) := by
  have h : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  rw [← ZMod.natCast_mod n 3]
  unfold tritVal
  interval_cases h : n % 3 <;> rfl

theorem ofTrits_spec {d : ℕ} (hd : d ≤ 832) (f : ℕ → ℕ) : ∀ n ≤ d,
    (Nat.fold n (fun j _ v => v.setTrit j (f j % 3)) W.zero).wf = true ∧
      ∀ i, (Nat.fold n (fun j _ v => v.setTrit j (f j % 3)) W.zero).val i =
        if i < n then (f i : ZMod 3) else 0 := by
  intro n hn
  induction n with
  | zero => rw [Nat.fold_zero]; exact ⟨W.wf_zero, fun i => by simp [W.val_zero]⟩
  | succ n ih =>
    obtain ⟨hw, hv⟩ := ih (by omega)
    rw [Nat.fold_succ]
    have h0 : (Nat.fold n (fun j _ v => v.setTrit j (f j % 3)) W.zero).val n = 0 := by
      rw [hv]; simp
    refine ⟨W.wf_setTrit hw (by omega) h0 _, fun i => ?_⟩
    rw [W.val_setTrit (by omega) h0, hv, tritVal_mod]
    by_cases h1 : i = n
    · subst h1; simp
    · rw [ite_eq_right h1]
      by_cases h2 : i < n
      · rw [ite_eq_left h2, ite_eq_left (by omega)]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

theorem ofTrits_wf {d : ℕ} (hd : d ≤ 832) (f : ℕ → ℕ) : (ofTrits d f).wf = true :=
  (ofTrits_spec hd f d le_rfl).1

theorem ofTrits_val {d : ℕ} (hd : d ≤ 832) (f : ℕ → ℕ) (i : ℕ) :
    (ofTrits d f).val i = if i < d then (f i : ZMod 3) else 0 :=
  (ofTrits_spec hd f d le_rfl).2 i

@[expose] def bitZ (b : Bool) : ZMod 3 := if b then 1 else 0

theorem W.val_eq_bits {a : W} (ha : a.wf = true) (j : ℕ) :
    a.val j = bitZ (a.bitP j) - bitZ (a.bitM j) := by
  have h := W.not_both ha j
  unfold W.val bitVal bitZ
  cases hp : a.bitP j <;> cases hm : a.bitM j <;> simp_all <;> decide

theorem frEntry_spec {Y : Array W} (hY : RowsWF Y) (b x c : ℕ) : ∀ n : ℕ,
    (Nat.fold n (fun t _ acc => if x.testBit t then acc.add (Y[8 * b + t]?.getD W.zero) else acc)
        W.zero).wf = true ∧
      (Nat.fold n (fun t _ acc => if x.testBit t then acc.add (Y[8 * b + t]?.getD W.zero)
        else acc) W.zero).val c =
        ∑ t ∈ range n, bitZ (x.testBit t) * (rowW Y (8 * b + t)).val c := by
  intro n
  induction n with
  | zero => rw [Nat.fold_zero]; exact ⟨W.wf_zero, by simp [W.val_zero]⟩
  | succ n ih =>
    rw [Nat.fold_succ, sum_range_succ]
    obtain ⟨hw, hv⟩ := ih
    have hr : (Y[8 * b + n]?.getD W.zero).wf = true := hY.row _
    by_cases hx : x.testBit n
    · rw [ite_eq_left hx]
      refine ⟨W.wf_add hw hr, ?_⟩
      rw [W.val_add hw hr, hv]
      simp [bitZ, hx, rowW]
    · rw [ite_eq_right hx]
      refine ⟨hw, ?_⟩
      rw [hv]
      simp [bitZ, hx]

theorem frEntry_wf {Y : Array W} (hY : RowsWF Y) (b x : ℕ) : (frEntry Y b x).wf = true :=
  (frEntry_spec hY b x 0 8).1

theorem frEntry_val {Y : Array W} (hY : RowsWF Y) (b x c : ℕ) :
    (frEntry Y b x).val c = ∑ t ∈ range 8, bitZ (x.testBit t) * (rowW Y (8 * b + t)).val c :=
  (frEntry_spec hY b x c 8).2

theorem frTable_get (Y : Array W) {b x : ℕ} (hb : b < 98) (hx : x < 256) :
    (frTable Y)[256 * b + x]?.getD W.zero = frEntry Y b x := by
  unfold frTable
  rw [Array.getElem?_ofFn, dite_eq_left (by omega)]
  simp only [Option.getD_some]
  congr 1 <;> omega

theorem W.add_zero (a : W) : a.add W.zero = a := by
  apply W.ext_limbs
  · intro l _
    rw [W.limbP_add, W.limbP_zero, W.limbM_zero]
    simp only [sumP, sumT, UInt64.or_zero]
    rw [← UInt64.xor_assoc, UInt64.xor_comm (a.limbM l), UInt64.xor_assoc, UInt64.xor_self,
      UInt64.xor_zero]
  · intro l _
    rw [W.limbM_add, W.limbP_zero, W.limbM_zero]
    simp only [sumM, sumT, UInt64.or_zero]
    rw [← UInt64.xor_assoc, UInt64.xor_self, UInt64.zero_xor]

theorem W.sub_zero (a : W) : a.sub W.zero = a := by
  rw [W.sub_eq_add_neg]
  have : W.zero.neg = W.zero := rfl
  rw [this, W.add_zero]

theorem frEntry_zero (Y : Array W) (b : ℕ) : frEntry Y b 0 = W.zero := by
  unfold frEntry
  have key : ∀ n, Nat.fold n (fun t _ acc => if (0 : ℕ).testBit t then
      acc.add (Y[8 * b + t]?.getD W.zero) else acc) W.zero = W.zero := by
    intro n
    induction n with
    | zero => rw [Nat.fold_zero]
    | succ n ih => rw [Nat.fold_succ, ih]; simp
  exact key 8

private theorem byte_toNat (w s : UInt64) :
    ((w >>> s) &&& 255).toNat = w.toNat >>> (s.toNat % 64) % 256 := by
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, show (255 : UInt64).toNat = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem frStep_eq (Y : Array W) {b : ℕ} (hb : b < 98) (xp xm s : UInt64) (acc : W) :
    frStep (frTable Y) (256 * b) xp xm s acc =
      (acc.add (frEntry Y b (xp.toNat >>> (s.toNat % 64) % 256))).sub
        (frEntry Y b (xm.toNat >>> (s.toNat % 64) % 256)) := by
  unfold frStep
  simp only [byte_toNat]
  have h1 := Nat.mod_lt (xp.toNat >>> (s.toNat % 64)) (show 256 > 0 by norm_num)
  have h2 := Nat.mod_lt (xm.toNat >>> (s.toNat % 64)) (show 256 > 0 by norm_num)
  rw [frTable_get Y hb h1, frTable_get Y hb h2]
  generalize xp.toNat >>> (s.toNat % 64) % 256 = u at h1 ⊢
  generalize xm.toNat >>> (s.toNat % 64) % 256 = v at h2 ⊢
  by_cases hu : u = 0
  · subst hu
    rw [ite_eq_left rfl, frEntry_zero, W.add_zero]
    by_cases hv : v = 0
    · subst hv; rw [ite_eq_left rfl, frEntry_zero, W.sub_zero]
    · rw [ite_eq_right hv]
  · rw [ite_eq_right hu]
    by_cases hv : v = 0
    · subst hv
      rw [ite_eq_left rfl, frEntry_zero, W.sub_zero]
    · rw [ite_eq_right hv]

theorem frStep_spec {Y : Array W} (hY : RowsWF Y) {b : ℕ} (hb : b < 98) (xp xm : UInt64)
    {s : UInt64} (hs : s.toNat < 64) {acc : W} (hacc : acc.wf = true) (c : ℕ) :
    (frStep (frTable Y) (256 * b) xp xm s acc).wf = true ∧
      (frStep (frTable Y) (256 * b) xp xm s acc).val c = acc.val c +
        ∑ t ∈ range 8, (bitZ (xp.toNat.testBit (s.toNat + t)) -
          bitZ (xm.toNat.testBit (s.toNat + t))) * (rowW Y (8 * b + t)).val c := by
  rw [frStep_eq Y hb]
  have hp := frEntry_wf hY b (xp.toNat >>> (s.toNat % 64) % 256)
  have hm := frEntry_wf hY b (xm.toNat >>> (s.toNat % 64) % 256)
  refine ⟨W.wf_sub (W.wf_add hacc hp) hm, ?_⟩
  have key : ∀ (w : UInt64) (t : ℕ), t ∈ range 8 →
      bitZ ((w.toNat >>> (s.toNat % 64) % 256).testBit t) =
        bitZ (w.toNat.testBit (s.toNat + t)) := by
    intro w t ht
    rw [mem_range] at ht
    have h : ∀ x : ℕ, (x % 256).testBit t = (decide (t < 8) && x.testBit t) :=
      fun x => Nat.testBit_mod_two_pow x 8 t
    rw [h, Nat.testBit_shiftRight, Nat.mod_eq_of_lt hs]
    simp [ht]
  have e1 : ∑ t ∈ range 8, bitZ ((xp.toNat >>> (s.toNat % 64) % 256).testBit t) *
      (rowW Y (8 * b + t)).val c =
      ∑ t ∈ range 8, bitZ (xp.toNat.testBit (s.toNat + t)) * (rowW Y (8 * b + t)).val c :=
    sum_congr rfl fun t ht => by rw [key xp t ht]
  have e2 : ∑ t ∈ range 8, bitZ ((xm.toNat >>> (s.toNat % 64) % 256).testBit t) *
      (rowW Y (8 * b + t)).val c =
      ∑ t ∈ range 8, bitZ (xm.toNat.testBit (s.toNat + t)) * (rowW Y (8 * b + t)).val c :=
    sum_congr rfl fun t ht => by rw [key xm t ht]
  rw [W.val_sub (W.wf_add hacc hp) hm, W.val_add hacc hp, frEntry_val hY, frEntry_val hY,
    add_sub_assoc, e1, e2]
  congr 1
  simp only [sub_mul]
  exact (Finset.sum_sub_distrib _ _).symm

private theorem frLimb_eq_foldl (t : Array W) (base : ℕ) (xp xm : UInt64) (acc : W) :
    frLimb t base xp xm acc =
      (List.range 8).foldl (fun acc k => frStep t (base + 256 * k) xp xm (UInt64.ofNat (8 * k)) acc)
        acc := by
  unfold frLimb; rfl

private theorem foldl_frStep_spec {Y : Array W} (hY : RowsWF Y) {b : ℕ} (xp xm : UInt64) {n : ℕ}
    (hn : n ≤ 8) (hlt : b + n ≤ 98) {acc : W} (hacc : acc.wf = true) (c : ℕ) :
    ((List.range n).foldl
        (fun acc k => frStep (frTable Y) (256 * b + 256 * k) xp xm (UInt64.ofNat (8 * k)) acc)
        acc).wf = true ∧
    ((List.range n).foldl
        (fun acc k => frStep (frTable Y) (256 * b + 256 * k) xp xm (UInt64.ofNat (8 * k)) acc)
        acc).val c = acc.val c + ∑ k ∈ range n, ∑ t ∈ range 8,
          (bitZ (xp.toNat.testBit (8 * k + t)) - bitZ (xm.toNat.testBit (8 * k + t))) *
            (rowW Y (8 * (b + k) + t)).val c := by
  induction n with
  | zero => simp [hacc]
  | succ n ih =>
    obtain ⟨hw, hv⟩ := ih (by omega) (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      show 256 * b + 256 * n = 256 * (b + n) by ring]
    have hs : (UInt64.ofNat (8 * n)).toNat = 8 * n := by
      rw [UInt64.toNat_ofNat']; omega
    obtain ⟨h1, h2⟩ := frStep_spec hY (b := b + n) (by omega) xp xm
      (s := UInt64.ofNat (8 * n)) (by omega) hw c
    refine ⟨h1, ?_⟩
    rw [h2, hv, hs, add_assoc]
    conv_rhs => rw [sum_range_succ]

private theorem sum_range_mul_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) {n a b : ℕ}
    (h : n = b * a) : ∑ j ∈ range n, f j = ∑ i ∈ range a, ∑ j ∈ range b, f (b * i + j) := by
  subst h
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

@[expose] def contrib (Y : Array W) (a : W) (c j : ℕ) : ZMod 3 :=
  (bitZ (a.bitP j) - bitZ (a.bitM j)) * (rowW Y j).val c

theorem frLimb_spec {Y : Array W} (hY : RowsWF Y) (a : W) {l base : ℕ} {xp xm : UInt64}
    (hl : l < 12) (hbase : base = 2048 * l) (hxp : xp = a.limbP l) (hxm : xm = a.limbM l)
    {acc : W} (hacc : acc.wf = true) (c : ℕ) :
    (frLimb (frTable Y) base xp xm acc).wf = true ∧
      (frLimb (frTable Y) base xp xm acc).val c =
        acc.val c + ∑ t ∈ range 64, contrib Y a c (64 * l + t) := by
  subst hbase hxp hxm
  rw [frLimb_eq_foldl, show 2048 * l = 256 * (8 * l) by ring]
  obtain ⟨h1, h2⟩ := foldl_frStep_spec hY (b := 8 * l) (a.limbP l) (a.limbM l) (n := 8) le_rfl
    (by omega) hacc c
  refine ⟨h1, ?_⟩
  rw [h2, sum_range_mul_eq _ (show 64 = 8 * 8 by norm_num)]
  refine congrArg (acc.val c + ·) ?_
  refine sum_congr rfl fun k hk => sum_congr rfl fun t ht => ?_
  rw [mem_range] at hk ht
  unfold contrib
  rw [W.bitP_eq, W.bitM_eq, show (64 * l + (8 * k + t)) / 64 = l by omega,
    show (64 * l + (8 * k + t)) % 64 = 8 * k + t by omega,
    show 8 * (8 * l + k) + t = 64 * l + (8 * k + t) by ring]

theorem frStep12_spec {Y : Array W} (hY : RowsWF Y) (a : W) {k base : ℕ} {xp xm s : UInt64}
    (hk : k < 2) (hbase : base = 256 * (96 + k)) (hs : s = UInt64.ofNat (8 * k))
    (hxp : xp = a.limbP 12) (hxm : xm = a.limbM 12) {acc : W} (hacc : acc.wf = true) (c : ℕ) :
    (frStep (frTable Y) base xp xm s acc).wf = true ∧
      (frStep (frTable Y) base xp xm s acc).val c =
        acc.val c + ∑ t ∈ range 8, contrib Y a c (768 + 8 * k + t) := by
  subst hbase hs hxp hxm
  have hs' : (UInt64.ofNat (8 * k)).toNat = 8 * k := by rw [UInt64.toNat_ofNat']; omega
  obtain ⟨h1, h2⟩ := frStep_spec hY (b := 96 + k) (by omega) (a.limbP 12) (a.limbM 12)
    (s := UInt64.ofNat (8 * k)) (by omega) hacc c
  refine ⟨h1, ?_⟩
  rw [h2, hs']
  refine congrArg (acc.val c + ·) ?_
  refine sum_congr rfl fun t ht => ?_
  rw [mem_range] at ht
  unfold contrib
  rw [W.bitP_eq, W.bitM_eq, show (768 + 8 * k + t) / 64 = 12 by omega,
    show (768 + 8 * k + t) % 64 = 8 * k + t by omega,
    show 8 * (96 + k) + t = 768 + 8 * k + t by ring]

theorem frApply_spec {Y : Array W} (hY : RowsWF Y) {a : W} (ha : a.wf = true) (c : ℕ) :
    (frApply (frTable Y) a).wf = true ∧
      (frApply (frTable Y) a).val c = ∑ j ∈ range 784, a.val j * (rowW Y j).val c := by
  unfold frApply
  obtain ⟨w0, v0⟩ := frLimb_spec hY a (l := 0) (base := 0) (xp := a.p0) (xm := a.m0)
    (by norm_num) (by norm_num) rfl rfl W.wf_zero c
  obtain ⟨w1, v1⟩ := frLimb_spec hY a (l := 1) (base := 2048) (xp := a.p1) (xm := a.m1)
    (by norm_num) (by norm_num) rfl rfl w0 c
  obtain ⟨w2, v2⟩ := frLimb_spec hY a (l := 2) (base := 4096) (xp := a.p2) (xm := a.m2)
    (by norm_num) (by norm_num) rfl rfl w1 c
  obtain ⟨w3, v3⟩ := frLimb_spec hY a (l := 3) (base := 6144) (xp := a.p3) (xm := a.m3)
    (by norm_num) (by norm_num) rfl rfl w2 c
  obtain ⟨w4, v4⟩ := frLimb_spec hY a (l := 4) (base := 8192) (xp := a.p4) (xm := a.m4)
    (by norm_num) (by norm_num) rfl rfl w3 c
  obtain ⟨w5, v5⟩ := frLimb_spec hY a (l := 5) (base := 10240) (xp := a.p5) (xm := a.m5)
    (by norm_num) (by norm_num) rfl rfl w4 c
  obtain ⟨w6, v6⟩ := frLimb_spec hY a (l := 6) (base := 12288) (xp := a.p6) (xm := a.m6)
    (by norm_num) (by norm_num) rfl rfl w5 c
  obtain ⟨w7, v7⟩ := frLimb_spec hY a (l := 7) (base := 14336) (xp := a.p7) (xm := a.m7)
    (by norm_num) (by norm_num) rfl rfl w6 c
  obtain ⟨w8, v8⟩ := frLimb_spec hY a (l := 8) (base := 16384) (xp := a.p8) (xm := a.m8)
    (by norm_num) (by norm_num) rfl rfl w7 c
  obtain ⟨w9, v9⟩ := frLimb_spec hY a (l := 9) (base := 18432) (xp := a.p9) (xm := a.m9)
    (by norm_num) (by norm_num) rfl rfl w8 c
  obtain ⟨w10, v10⟩ := frLimb_spec hY a (l := 10) (base := 20480) (xp := a.p10) (xm := a.m10)
    (by norm_num) (by norm_num) rfl rfl w9 c
  obtain ⟨w11, v11⟩ := frLimb_spec hY a (l := 11) (base := 22528) (xp := a.p11) (xm := a.m11)
    (by norm_num) (by norm_num) rfl rfl w10 c
  obtain ⟨w12, v12⟩ := frStep12_spec hY a (k := 0) (base := 24576) (xp := a.p12) (xm := a.m12)
    (s := 0) (by norm_num) (by norm_num) rfl rfl rfl w11 c
  obtain ⟨w13, v13⟩ := frStep12_spec hY a (k := 1) (base := 24832) (xp := a.p12) (xm := a.m12)
    (s := 8) (by norm_num) (by norm_num) rfl rfl rfl w12 c
  refine ⟨w13, ?_⟩
  rw [v13, v12, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1, v0, W.val_zero, zero_add]
  have hj : ∀ j, a.val j * (rowW Y j).val c = contrib Y a c j := by
    intro j; unfold contrib; rw [W.val_eq_bits ha]
  simp only [hj]
  rw [show range 784 = range (768 + 8 + 8) from rfl, sum_range_add, sum_range_add,
    sum_range_mul_eq _ (show 768 = 64 * 12 by norm_num)]
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.mul_zero, add_zero, Nat.mul_one]

theorem frApply_zero (t : Array W) : frApply t W.zero = W.zero := by
  have h : ∀ (base : ℕ) (s : UInt64) (acc : W), frStep t base 0 0 s acc = acc := by
    intro base s acc
    unfold frStep
    simp
  simp only [frApply, frLimb, W.zero, h]

theorem rowW_mulW (X Y : Array W) (i : ℕ) : rowW (mulW X Y) i = frApply (frTable Y) (rowW X i) :=
  rowW_map _ X (frApply_zero _) i

theorem RowsWF.mulW {X Y : Array W} (hX : RowsWF X) (hY : RowsWF Y) : RowsWF (mulW X Y) := by
  intro x hx
  unfold Native.mulW at hx
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
  rw [Array.getElem_map]
  exact (frApply_spec hY (hX _ (Array.getElem_mem _)) 0).1

theorem mulW_size (X Y : Array W) : (mulW X Y).size = X.size := by
  unfold mulW; simp

theorem rowW_ge {X : Array W} {i : ℕ} (hi : X.size ≤ i) : rowW X i = W.zero := by
  unfold rowW; rw [Array.getElem?_eq_none hi]; rfl

theorem val_mulW {X Y : Array W} (hX : RowsWF X) (hY : RowsWF Y) (i k : ℕ) :
    (rowW (mulW X Y) i).val k = ∑ j ∈ range 784, (rowW X i).val j * (rowW Y j).val k := by
  rw [rowW_mulW]
  exact (frApply_spec hY (hX.row i) k).2

theorem matW_mulW {r m c : ℕ} (hm : m ≤ 784) {X Y : Array W} (hX : RowsWF X) (hY : RowsWF Y)
    (hYs : Y.size ≤ m) : matW r c (mulW X Y) = matW r m X * matW m c Y := by
  ext i k
  rw [matW_apply, val_mulW hX hY, Matrix.mul_apply]
  rw [← Finset.sum_range_add_sum_Ico _ hm, show ∑ j ∈ Ico m 784, (rowW X i).val j *
      (rowW Y j).val k = 0 from sum_eq_zero fun j hj => by
        rw [rowW_ge (X := Y) (by rw [mem_Ico] at hj; omega), W.val_zero, mul_zero], add_zero,
    ← Fin.sum_univ_eq_sum_range]
  rfl

theorem tritZ_eq_val {a : W} (ha : a.wf = true) (j : ℕ) : ((a.trit j : ℕ) : ZMod 3) = a.val j := by
  have h := W.not_both ha j
  unfold W.trit W.val bitVal
  cases hp : a.bitP j <;> cases hm : a.bitM j <;> simp_all

theorem rowW_transposeW {n d : ℕ} (X : Array W) (j : ℕ) (hj : j < d) :
    rowW (transposeW n d X) j = ofTrits n fun i => (X[i]?.getD W.zero).trit j := by
  unfold transposeW
  rw [rowW_ofFn, dite_eq_left hj]

theorem RowsWF.transposeW {n : ℕ} (hn : n ≤ 832) (d : ℕ) (X : Array W) :
    RowsWF (transposeW n d X) := by
  intro x hx
  unfold Native.transposeW at hx
  obtain ⟨j, rfl⟩ := Array.mem_ofFn.1 hx
  exact ofTrits_wf hn _

theorem transposeW_size (n d : ℕ) (X : Array W) : (transposeW n d X).size = d := by
  unfold transposeW; simp

theorem matW_transposeW {n d : ℕ} (hn : n ≤ 832) {X : Array W} (hX : RowsWF X) :
    matW d n (transposeW n d X) = (matW n d X).transpose := by
  ext j i
  rw [Matrix.transpose_apply, matW_apply, matW_apply, rowW_transposeW X j.val j.isLt,
    ofTrits_val hn, ite_eq_left i.isLt]
  exact tritZ_eq_val (hX.row i.val) j.val

theorem rowW_idW {d : ℕ} (i : ℕ) (hi : i < d) : rowW (idW d) i = W.zero.setTrit i 1 := by
  unfold idW; rw [rowW_ofFn, dite_eq_left hi]

theorem RowsWF.idW {d : ℕ} (hd : d ≤ 832) : RowsWF (idW d) := by
  intro x hx
  unfold Native.idW at hx
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.1 hx
  exact W.wf_setTrit W.wf_zero (by omega) (W.val_zero _) 1

theorem idW_size (d : ℕ) : (idW d).size = d := by unfold idW; simp

theorem matW_idW {d : ℕ} (hd : d ≤ 832) : matW d d (idW d) = 1 := by
  ext i j
  rw [matW_apply, rowW_idW _ i.isLt, W.val_setTrit (by omega) (W.val_zero _), Matrix.one_apply,
    W.val_zero]
  by_cases h : i = j
  · subst h; simp [tritVal]
  · have h' : j.val ≠ i.val := fun e => h (Fin.ext e.symm)
    simp [h, h']

theorem powW_size (d : ℕ) (M : Array W) (e : ℕ) : (powW d M e).size = d := by
  induction e with
  | zero => exact idW_size d
  | succ e ih => rw [powW, mulW_size, ih]

theorem RowsWF.powW {d : ℕ} (hd : d ≤ 832) {M : Array W} (hM : RowsWF M) (e : ℕ) :
    RowsWF (powW d M e) := by
  induction e with
  | zero => exact RowsWF.idW hd
  | succ e ih => exact RowsWF.mulW ih hM

theorem matW_powW {d : ℕ} (hd : d ≤ 784) {M : Array W} (hM : RowsWF M) (hMs : M.size ≤ d)
    (e : ℕ) : matW d d (powW d M e) = matW d d M ^ e := by
  induction e with
  | zero => rw [pow_zero]; exact matW_idW (by omega)
  | succ e ih => rw [Native.powW, matW_mulW hd (RowsWF.powW (by omega) hM e) hM hMs, ih, pow_succ]

theorem W.canon_wf {a : W} (h : a.canon = true) : a.wf = true := by
  unfold W.canon at h; simp only [Bool.and_eq_true] at h; exact h.1.1

theorem W.canon_bits {a : W} (h : a.canon = true) {j : ℕ} (hj : 781 ≤ j) :
    a.bitP j = false ∧ a.bitM j = false := by
  unfold W.canon at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨_, hp⟩, hm⟩ := h
  by_cases hl : j / 64 < 13
  · have hl12 : j / 64 = 12 := by omega
    have key : ∀ x : UInt64, x >>> 13 = 0 → x.toNat.testBit (j % 64) = false := by
      intro x hx
      have e := congrArg (fun y : UInt64 => y.toNat.testBit (j % 64 - 13)) hx
      simp only [UInt64.toNat_shiftRight, Nat.testBit_shiftRight, UInt64.toNat_zero,
        Nat.zero_testBit] at e
      rwa [show (13 : UInt64).toNat % 64 = 13 from rfl,
        show 13 + (j % 64 - 13) = j % 64 by omega] at e
    rw [W.bitP_eq, W.bitM_eq, hl12]
    exact ⟨key _ hp, key _ hm⟩
  · rw [W.bitP_eq, W.bitM_eq, W.limbP_ge _ (by omega), W.limbM_ge _ (by omega)]
    simp

theorem W.canon_val {a : W} (h : a.canon = true) {j : ℕ} (hj : 781 ≤ j) : a.val j = 0 := by
  obtain ⟨hp, hm⟩ := W.canon_bits h hj
  unfold W.val; rw [hp, hm]; rfl

private theorem bitVal_inj : ∀ p m p' m' : Bool, (p && m) = false → (p' && m') = false →
    bitVal p m = bitVal p' m' → p = p' ∧ m = m' := by
  decide

theorem W.eq_of_val {a b : W} (ha : a.canon = true) (hb : b.canon = true)
    (h : ∀ j < 781, a.val j = b.val j) : a = b := by
  have hbits : ∀ j, a.bitP j = b.bitP j ∧ a.bitM j = b.bitM j := by
    intro j
    by_cases hj : j < 781
    · exact bitVal_inj _ _ _ _ (W.not_both (W.canon_wf ha) j) (W.not_both (W.canon_wf hb) j)
        (h j hj)
    · obtain ⟨h1, h2⟩ := W.canon_bits ha (j := j) (by omega)
      obtain ⟨h3, h4⟩ := W.canon_bits hb (j := j) (by omega)
      rw [h1, h2, h3, h4]; exact ⟨rfl, rfl⟩
  apply W.ext_limbs
  · intro l _
    apply uint64_eq_of_testBit
    intro t ht
    have := (hbits (64 * l + t)).1
    rwa [W.bitP_eq, W.bitP_eq, show (64 * l + t) / 64 = l by omega,
      show (64 * l + t) % 64 = t by omega] at this
  · intro l _
    apply uint64_eq_of_testBit
    intro t ht
    have := (hbits (64 * l + t)).2
    rwa [W.bitM_eq, W.bitM_eq, show (64 * l + t) / 64 = l by omega,
      show (64 * l + t) % 64 = t by omega] at this

theorem canonRows_spec {d : ℕ} {X : Array W} (h : canonRows d X = true) :
    X.size = d ∧ ∀ x ∈ X, x.canon = true := by
  unfold canonRows at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true] at h
  refine ⟨h.1, fun x hx => ?_⟩
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
  exact h.2 i hi

theorem RowsWF.of_canonRows {d : ℕ} {X : Array W} (h : canonRows d X = true) : RowsWF X :=
  fun x hx => W.canon_wf ((canonRows_spec h).2 x hx)

theorem eq_of_eqRows {d : ℕ} {X Y : Array W} (h : eqRows d X Y = true) : X.size = d ∧ X = Y := by
  unfold eqRows at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact h

theorem eq_of_matW_eq {r : ℕ} {X Y : Array W} (hX : canonRows r X = true)
    (hY : canonRows r Y = true) (h : matW r 781 X = matW r 781 Y) : X = Y := by
  obtain ⟨hXs, hXc⟩ := canonRows_spec hX
  obtain ⟨hYs, hYc⟩ := canonRows_spec hY
  apply Array.ext (by rw [hXs, hYs])
  intro i hi hi'
  have key : ∀ j < 781, (rowW X i).val j = (rowW Y i).val j := by
    intro j hj
    have := congrFun (congrFun h ⟨i, by omega⟩) ⟨j, hj⟩
    simpa [matW_apply] using this
  have e1 : rowW X i = X[i] := by unfold rowW; rw [Array.getElem?_eq_getElem hi]; rfl
  have e2 : rowW Y i = Y[i] := by unfold rowW; rw [Array.getElem?_eq_getElem hi']; rfl
  rw [e1, e2] at key
  exact W.eq_of_val (hXc _ (Array.getElem_mem _)) (hYc _ (Array.getElem_mem _)) key

theorem W.canon_of_val {a : W} (ha : a.wf = true) (h : ∀ j, 781 ≤ j → a.val j = 0) :
    a.canon = true := by
  have hbits : ∀ j, 781 ≤ j → a.bitP j = false ∧ a.bitM j = false := by
    intro j hj
    have h0 := h j hj
    have hn := W.not_both ha j
    unfold W.val bitVal at h0
    cases hp : a.bitP j <;> cases hm : a.bitM j <;> simp_all
    exact absurd h0 (by decide)
  unfold W.canon
  simp only [ha, Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  have key : ∀ x : UInt64, (∀ t, 13 ≤ t → t < 64 → x.toNat.testBit t = false) → x >>> 13 = 0 := by
    intro x hx
    apply uint64_eq_of_testBit
    intro t ht
    rw [UInt64.toNat_shiftRight, Nat.testBit_shiftRight,
      show (13 : UInt64).toNat % 64 = 13 from rfl]
    by_cases h' : 13 + t < 64
    · rw [hx _ (by omega) h']; simp
    · rw [CFSG.Sporadic.Fi23.Native.testBit_toNat_ge _ (by omega)]; simp
  constructor
  · apply key
    intro t h1 h2
    have := (hbits (768 + t) (by omega)).1
    rwa [W.bitP_eq, show (768 + t) / 64 = 12 by omega, show (768 + t) % 64 = t by omega] at this
  · apply key
    intro t h1 h2
    have := (hbits (768 + t) (by omega)).2
    rwa [W.bitM_eq, show (768 + t) / 64 = 12 by omega, show (768 + t) % 64 = t by omega] at this

theorem canonRows_idW : canonRows 781 (idW 781) = true := by
  unfold canonRows
  rw [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
  refine ⟨idW_size 781, fun i hi => ?_⟩
  have e : (idW 781)[i] = rowW (idW 781) i := by unfold rowW; rw [Array.getElem?_eq_getElem hi]; rfl
  rw [e]
  have hi' : i < 781 := by rwa [idW_size] at hi
  apply W.canon_of_val ((RowsWF.idW (by norm_num)).row i)
  intro j hj
  rw [rowW_idW _ hi', W.val_setTrit (by omega) (W.val_zero _), ite_eq_right (by omega),
    W.val_zero]

theorem canonRows_mulW {X Y : Array W} (hX : canonRows 781 X = true) (hY : canonRows 781 Y = true) :
    canonRows 781 (mulW X Y) = true := by
  obtain ⟨hXs, _⟩ := canonRows_spec hX
  obtain ⟨hYs, hYc⟩ := canonRows_spec hY
  have hXw := RowsWF.of_canonRows hX
  have hYw := RowsWF.of_canonRows hY
  unfold canonRows
  rw [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
  refine ⟨by rw [mulW_size, hXs], fun i hi => ?_⟩
  have e : (mulW X Y)[i] = rowW (mulW X Y) i := by
    unfold rowW; rw [Array.getElem?_eq_getElem hi]; rfl
  rw [e]
  apply W.canon_of_val ((RowsWF.mulW hXw hYw).row i)
  intro k hk
  rw [val_mulW hXw hYw]
  refine sum_eq_zero fun j _ => ?_
  by_cases hj : j < Y.size
  · have hc : (rowW Y j).canon = true := by
      unfold rowW; rw [Array.getElem?_eq_getElem hj]; exact hYc _ (Array.getElem_mem _)
    rw [W.canon_val hc hk, mul_zero]
  · rw [rowW_ge (X := Y) (by omega), W.val_zero, mul_zero]

end CFSG.Sporadic.Fi24.Native
