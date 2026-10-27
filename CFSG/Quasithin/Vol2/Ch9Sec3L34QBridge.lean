module

public import CFSG.Quasithin.Vol2.Ch9Sec3L34QData
public import CFSG.Quasithin.Background.Module
public import Mathlib.Algebra.Group.Equiv.Finite
public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Presheaf
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.H13.Ch9.L34Q

open CFSG.Fischer CFSG.Quasithin

theorem code_lt (X : M2) : code X < 256 := by
  have h1 := (X 0 0).code.isLt
  have h2 := (X 0 1).code.isLt
  have h3 := (X 1 0).code.isLt
  have h4 := (X 1 1).code.isLt
  unfold code
  omega

theorem f4_code (x : F4) : f4 x.code.val = x := by
  obtain ⟨⟨n, hn⟩⟩ := x
  unfold f4
  congr
  exact Nat.mod_eq_of_lt hn

theorem f4_add_mul (a m : ℕ) (x : F4) (ha : a = x.code.val) : f4 (a + 4 * m) = x := by
  subst ha
  have : (x.code.val + 4 * m) % 4 = x.code.val := by
    have := x.code.isLt
    omega
  unfold f4
  obtain ⟨⟨n, hn⟩⟩ := x
  congr

theorem decode_code (X : M2) : decode (code X) = X := by
  have h1 := (X 0 0).code.isLt
  have h2 := (X 0 1).code.isLt
  have h3 := (X 1 0).code.isLt
  have h4 := (X 1 1).code.isLt
  ext i j
  fin_cases i <;> fin_cases j
  · show f4 (code X) = X 0 0
    exact f4_add_mul _ _ _ rfl
  · show f4 (code X / 4) = X 0 1
    have : code X / 4 = (X 0 1).code.val + 4 * ((X 1 0).code.val + 4 * (X 1 1).code.val) := by
      unfold code; omega
    rw [this]
    exact f4_add_mul _ _ _ rfl
  · show f4 (code X / 16) = X 1 0
    have : code X / 16 = (X 1 0).code.val + 4 * (X 1 1).code.val := by
      unfold code; omega
    rw [this]
    exact f4_add_mul _ _ _ rfl
  · show f4 (code X / 64) = X 1 1
    have : code X / 64 = (X 1 1).code.val := by
      unfold code; omega
    rw [this]
    exact f4_code _

theorem code_decode {v : ℕ} (hv : v < 256) : code (decode v) = v := by
  unfold code decode f4
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  omega

theorem decode_injOn {u v : ℕ} (hu : u < 256) (hv : v < 256)
    (h : decode u = decode v) : u = v := by
  rw [← code_decode hu, ← code_decode hv, h]

theorem xor_add_four {a b m n : ℕ} (ha : a < 4) (hb : b < 4) :
    (a + 4 * m) ^^^ (b + 4 * n) = (a ^^^ b) + 4 * (m ^^^ n) := by
  have hab : a ^^^ b < 2 ^ 2 := Nat.xor_lt_two_pow (by simpa using ha) (by simpa using hb)
  have e1 : a + 4 * m = 2 ^ 2 * m + a := by ring
  have e2 : b + 4 * n = 2 ^ 2 * n + b := by ring
  have e3 : (a ^^^ b) + 4 * (m ^^^ n) = 2 ^ 2 * (m ^^^ n) + (a ^^^ b) := by ring
  rw [e1, e2, e3]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ (by simpa using ha),
    Nat.testBit_two_pow_mul_add _ (by simpa using hb), Nat.testBit_two_pow_mul_add _ hab]
  split_ifs
  · exact (Nat.testBit_xor _ _ _).symm
  · exact (Nat.testBit_xor _ _ _).symm

theorem code_val_add (x y : F4) : (x + y).code.val = x.code.val ^^^ y.code.val := by
  have hx := x.code.isLt
  have hy := y.code.isLt
  show (x.code ^^^ y.code).val = _
  rw [Fin.xor_val]
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 2) (by simp [hx]) (by simp [hy]))

theorem code_add (X Y : M2) : code (X + Y) = code X ^^^ code Y := by
  unfold code
  simp only [Matrix.add_apply, code_val_add]
  rw [xor_add_four (X 0 0).code.isLt (Y 0 0).code.isLt,
    xor_add_four (X 0 1).code.isLt (Y 0 1).code.isLt,
    xor_add_four (X 1 0).code.isLt (Y 1 0).code.isLt]

theorem decode_xor {u v : ℕ} (hu : u < 256) (hv : v < 256) :
    decode (u ^^^ v) = decode u + decode v := by
  rw [← decode_code (decode u + decode v), code_add, code_decode hu, code_decode hv]

theorem testBit_one_shiftLeft (w v : ℕ) : (1 <<< w).testBit v = decide (w = v) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem testBit_foldl_mask (P : ℕ → Bool) (l : List ℕ) (m v : ℕ) :
    (l.foldl (fun m w => if P w then m ||| (1 <<< w) else m) m).testBit v =
      (m.testBit v || (decide (v ∈ l) && P v)) := by
  induction l generalizing m with
  | nil => simp
  | cons w l ih =>
    rw [List.foldl_cons, ih]
    by_cases hP : P w = true
    · simp only [hP, ↓reduceIte]
      rw [Nat.testBit_lor, testBit_one_shiftLeft]
      by_cases hvw : w = v
      · subst hvw; simp [hP]
      · simp [hvw, Ne.symm hvw]
    · simp only [hP, Bool.false_eq_true, ↓reduceIte]
      by_cases hvw : w = v
      · subst hvw; simp [hP]
      · simp [Ne.symm hvw]

theorem testBit_maskOf (P : ℕ → Bool) (v : ℕ) :
    (maskOf P).testBit v = (decide (v < 256) && P v) := by
  unfold maskOf
  rw [testBit_foldl_mask]
  simp

theorem testBit_foldl_or (f : ℕ → ℕ) (l : List ℕ) (m v : ℕ) :
    (l.foldl (fun m w => m ||| (1 <<< f w)) m).testBit v =
      (m.testBit v || decide (∃ w ∈ l, f w = v)) := by
  induction l generalizing m with
  | nil => simp
  | cons w l ih =>
    rw [List.foldl_cons, ih, Nat.testBit_lor, testBit_one_shiftLeft]
    by_cases h : f w = v
    · simp [h]
    · simp [h]

theorem testBit_lo (k v : ℕ) : (lo k).testBit v = (decide (v < 256) && !v.testBit k) :=
  testBit_maskOf _ v

theorem loTab_getD {k : ℕ} (hk : k < 8) : loTab.getD k 0 = lo k := by
  interval_cases k <;> rfl

theorem bit_facts : ∀ v < 256, ∀ k < 8,
    (v.testBit k = true → 2 ^ k ≤ v ∧ (v - 2 ^ k).testBit k = false ∧ v - 2 ^ k = v ^^^ 2 ^ k) ∧
    (v.testBit k = false → (2 ^ k ≤ v → (v - 2 ^ k).testBit k = true) ∧
      2 ^ k + v = v ^^^ 2 ^ k) := by
  decide +kernel

theorem testBit_tr1 (m : ℕ) {k v : ℕ} (hk : k < 8) (hv : v < 256) :
    (tr1 m k).testBit v = m.testBit (v ^^^ 2 ^ k) := by
  unfold tr1
  rw [loTab_getD hk, Nat.testBit_lor, Nat.testBit_shiftLeft, Nat.testBit_land,
    Nat.testBit_land, Nat.testBit_shiftRight, testBit_lo, testBit_lo]
  obtain ⟨h1, h2⟩ := bit_facts v hv k hk
  cases hb : v.testBit k
  · obtain ⟨h3, h4⟩ := h2 hb
    by_cases hle : 2 ^ k ≤ v
    · simp [hle, h3 hle, hv, h4]
    · simp [hle, hv, h4]
  · obtain ⟨h3, h4, h5⟩ := h1 hb
    have hlt : v - 2 ^ k < 256 := lt_of_le_of_lt (Nat.sub_le v _) hv
    have hlt' : v ^^^ 2 ^ k < 256 := h5 ▸ hlt
    simp [h3, h5, hb, hlt']

theorem mod_two_pow_succ_eq (w j : ℕ) :
    w % 2 ^ (j + 1) = (w % 2 ^ j) ^^^ (if w.testBit j then 2 ^ j else 0) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_mod_two_pow]
  by_cases hw : w.testBit j = true
  · simp only [hw, ↓reduceIte]
    rw [Nat.testBit_two_pow]
    rcases lt_trichotomy i j with h | h | h
    · simp [h, Nat.lt_succ_of_lt h, Nat.ne_of_gt h]
    · subst h; simp [hw]
    · simp [Nat.not_lt.mpr h.le, Nat.ne_of_lt h, show ¬ i < j + 1 by omega]
  · simp only [hw, Bool.false_eq_true, ↓reduceIte]
    rw [Nat.zero_testBit, Bool.xor_false]
    rcases lt_trichotomy i j with h | h | h
    · simp [h, Nat.lt_succ_of_lt h]
    · subst h; simp at hw; simp [hw]
    · simp [Nat.not_lt.mpr h.le, show ¬ i < j + 1 by omega]

theorem testBit_transB (m w : ℕ) {j v : ℕ} (hj : j ≤ 8) (hv : v < 256) :
    (transB m w j).testBit v = m.testBit (v ^^^ (w % 2 ^ j)) := by
  induction j generalizing v with
  | zero => simp [transB, Nat.mod_one]
  | succ j ih =>
    have hj' : j < 8 := by omega
    have hxv : v ^^^ 2 ^ j < 256 :=
      Nat.xor_lt_two_pow (n := 8) (by simpa using hv)
        (by calc 2 ^ j < 2 ^ 8 := Nat.pow_lt_pow_right (by norm_num) hj'
          _ = 2 ^ 8 := rfl)
    rw [mod_two_pow_succ_eq]
    unfold transB
    by_cases hw : w.testBit j = true
    · simp only [hw, ↓reduceIte]
      rw [testBit_tr1 _ hj' hv, ih (by omega) hxv, Nat.xor_assoc, Nat.xor_comm (2 ^ j)]
    · simp only [hw, Bool.false_eq_true, ↓reduceIte]
      rw [ih (by omega) hv, Nat.xor_zero]

theorem testBit_FULL (v : ℕ) : FULL.testBit v = decide (v < 256) := by
  unfold FULL
  rw [testBit_maskOf]
  simp

theorem testBit_sumOne (m : ℕ) {w : ℕ} (hw : w < 256) (v : ℕ) :
    (sumOne m w).testBit v = (decide (v < 256) && (m.testBit v || m.testBit (v ^^^ w))) := by
  unfold sumOne
  rw [Nat.testBit_land, testBit_FULL]
  by_cases hv : v < 256
  · rw [Nat.testBit_lor, testBit_transB _ _ le_rfl hv,
      Nat.mod_eq_of_lt (show w < 2 ^ 8 by norm_num; exact hw)]
    simp [hv]
  · simp [hv]

theorem mem_of_bfind (a : Array ℕ) (x : ℕ) :
    ∀ (fuel lo hi : ℕ), hi ≤ a.size → bfind a x fuel lo hi = true → x ∈ a.toList := by
  intro fuel
  induction fuel with
  | zero => intro lo hi _ h; simp [bfind] at h
  | succ fuel ih =>
    intro lo hi hhi h
    unfold bfind at h
    by_cases hlt : lo < hi
    · simp only [hlt, ↓reduceIte] at h
      have hmid : (lo + hi) / 2 < a.size := by omega
      by_cases heq : (a.getD ((lo + hi) / 2) 0 == x) = true
      · have h1 : a.getD ((lo + hi) / 2) 0 = x := by simpa using heq
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hmid, Option.getD_some] at h1
        rw [← h1]
        exact Array.getElem_mem_toList hmid
      · simp only [heq, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hlt2 : a.getD ((lo + hi) / 2) 0 < x
        · simp only [hlt2, ↓reduceIte] at h
          exact ih _ _ hhi h
        · simp only [hlt2, ↓reduceIte] at h
          exact ih _ _ (by omega) h
    · simp only [hlt, ↓reduceIte] at h
      exact absurd h (by simp)

theorem mem_of_memS {a : Array ℕ} {x : ℕ} (h : memS a x = true) : x ∈ a.toList :=
  mem_of_bfind a x 20 0 a.size le_rfl h

theorem mem_capL_of_memS {x : ℕ} (h : memS capA x = true) : x ∈ capL := by
  have := mem_of_memS h
  simpa [capA] using this

theorem mem_plusL_of_memS {x : ℕ} (h : memS plusA x = true) : x ∈ plusL := by
  have := mem_of_memS h
  simpa [plusA] using this

abbrev VM4 : Type := Multiplicative M2

@[expose] def Realizes (g : MulAut VM4) (p : Par) : Prop :=
  ∀ X : M2, Multiplicative.toAdd (g (Multiplicative.ofAdd X)) = gmap p.A p.B p.s p.t X

theorem add_self_m2 (X : M2) : X + X = 0 := by
  ext i j
  exact CharTwo.add_self_eq_zero (X i j)

theorem neg_m2 (X : M2) : -X = X := by
  ext i j
  rfl

theorem act_eq_of_realizes {g : MulAut VM4} {p : Par} (hg : Realizes g p) {v : ℕ} :
    act p v = code (Multiplicative.toAdd (g (Multiplicative.ofAdd (decode v)))) := by
  rw [hg]
  rfl

theorem isInvAct_of_realizes {g : MulAut VM4} {p : Par} (hg : Realizes g p)
    (h2 : g * g = 1) :
    isInvAct p = true := by
  unfold isInvAct
  rw [List.all_eq_true]
  intro k hk
  have hk8 : k < 8 := List.mem_range.mp hk
  have hlt : 2 ^ k < 256 := by
    calc 2 ^ k < 2 ^ 8 := Nat.pow_lt_pow_right (by norm_num) hk8
      _ = 256 := by norm_num
  rw [act_eq_of_realizes hg, act_eq_of_realizes hg, decode_code]
  have e : g (Multiplicative.ofAdd (Multiplicative.toAdd (g (Multiplicative.ofAdd
      (decode (2 ^ k)))))) = Multiplicative.ofAdd (decode (2 ^ k)) := by
    rw [ofAdd_toAdd, ← MulAut.mul_apply, h2, MulAut.one_apply]
  rw [e, toAdd_ofAdd, code_decode hlt]
  simp

theorem act_eq_self_iff {g : MulAut VM4} {p : Par} (hg : Realizes g p) {v : ℕ}
    (hv : v < 256) :
    act p v = v ↔ g (Multiplicative.ofAdd (decode v)) = Multiplicative.ofAdd (decode v) := by
  rw [act_eq_of_realizes hg]
  constructor
  · intro h
    have h1 := congrArg decode h
    rw [decode_code] at h1
    rw [← ofAdd_toAdd (g _), h1]
  · intro h
    rw [h, toAdd_ofAdd, code_decode hv]

theorem testBit_comM_iff (p : Par) (w : ℕ) :
    (comM p).testBit w = true ↔
      ∃ v < 256, code (gmap p.A p.B p.s p.t (decode v) + decode v) = w := by
  unfold comM
  rw [testBit_foldl_or]
  simp

noncomputable def mset (S : Set VM4) : ℕ :=
  by classical exact maskOf fun v => decide (Multiplicative.ofAdd (decode v) ∈ S)

theorem testBit_mset (S : Set VM4) (v : ℕ) :
    (mset S).testBit v = true ↔ v < 256 ∧ Multiplicative.ofAdd (decode v) ∈ S := by
  classical
  unfold mset
  rw [testBit_maskOf]
  simp

theorem code_lt' (x : VM4) : code (Multiplicative.toAdd x) < 256 := code_lt _

theorem mem_iff_testBit_mset (S : Set VM4) (x : VM4) :
    x ∈ S ↔ (mset S).testBit (code (Multiplicative.toAdd x)) = true := by
  rw [testBit_mset, decode_code, ofAdd_toAdd]
  exact ⟨fun h => ⟨code_lt' x, h⟩, fun h => h.2⟩

theorem mset_injective {S S' : Set VM4} (h : mset S = mset S') : S = S' := by
  ext x
  rw [mem_iff_testBit_mset, mem_iff_testBit_mset, h]

def codeEquiv : VM4 ≃ Fin 256 where
  toFun x := ⟨code (Multiplicative.toAdd x), code_lt' x⟩
  invFun v := Multiplicative.ofAdd (decode v)
  left_inv x := by simp [decode_code]
  right_inv v := Fin.ext (code_decode v.2)

theorem countP_range_eq (P : ℕ → Bool) :
    (List.range 256).countP P = ((Finset.range 256).filter fun v => P v = true).card := by
  rw [List.countP_eq_length_filter, Finset.card_def, Finset.filter_val, Finset.range_val]
  rfl

theorem popcount_mset (S : Set VM4) : popcount (mset S) = Nat.card S := by
  classical
  unfold popcount
  rw [countP_range_eq]
  have e1 : ((Finset.range 256).filter fun v => (mset S).testBit v = true).card =
      ((Finset.range 256).filter fun v => Multiplicative.ofAdd (decode v) ∈ S).card := by
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_range, testBit_mset]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.1, h.2⟩⟩
  have e2 : ((Finset.range 256).filter fun v => Multiplicative.ofAdd (decode v) ∈ S).card =
      (Finset.univ.filter fun v : Fin 256 => Multiplicative.ofAdd (decode v) ∈ S).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.sum_range]
  rw [e1, e2, Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeEquiv codeEquiv.symm fun v => Iff.rfl)

theorem mul_self_vm4 (x : VM4) : x * x = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, add_self_m2, toAdd_one]

theorem inv_vm4 (x : VM4) : x⁻¹ = x := by
  rw [inv_eq_iff_mul_eq_one, mul_self_vm4]

theorem toAdd_comm {g : MulAut VM4} {p : Par} (hg : Realizes g p) (x : VM4) :
    Multiplicative.toAdd (g x * x⁻¹) =
      gmap p.A p.B p.s p.t (Multiplicative.toAdd x) + Multiplicative.toAdd x := by
  rw [toAdd_mul, inv_vm4, ← hg, ofAdd_toAdd]

theorem testBit_comM_of {g : MulAut VM4} {p : Par} (hg : Realizes g p) (x : VM4) :
    (comM p).testBit (code (Multiplicative.toAdd (g x * x⁻¹))) = true := by
  rw [testBit_comM_iff]
  refine ⟨code (Multiplicative.toAdd x), code_lt' x, ?_⟩
  rw [decode_code, toAdd_comm hg]

theorem exists_of_testBit_comM {g : MulAut VM4} {p : Par} (hg : Realizes g p) {w : ℕ}
    (hw : (comM p).testBit w = true) :
    w < 256 ∧ ∃ x : VM4, Multiplicative.ofAdd (decode w) = g x * x⁻¹ := by
  obtain ⟨v, hv, rfl⟩ := (testBit_comM_iff p w).mp hw
  refine ⟨code_lt _, Multiplicative.ofAdd (decode v), ?_⟩
  apply Multiplicative.toAdd.injective
  rw [decode_code, toAdd_comm hg, toAdd_ofAdd, toAdd_ofAdd]

theorem realizes_injective {g g' : MulAut VM4} {p : Par} (hg : Realizes g p)
    (hg' : Realizes g' p) : g = g' := by
  refine MulEquiv.ext fun x => ?_
  have h1 := hg (Multiplicative.toAdd x)
  have h2 := hg' (Multiplicative.toAdd x)
  rw [ofAdd_toAdd] at h1 h2
  exact Multiplicative.toAdd.injective (h1.trans h2.symm)

instance : Finite (MulAut VM4) :=
  Finite.of_injective (fun e : MulAut VM4 => (e : VM4 → VM4)) fun _ _ h => MulEquiv.ext (congrFun h)

theorem elat_of {g : MulAut VM4} {p : Par} (hg : Realizes g p) {W : Set VM4}
    (h1 : ∀ x ∈ W, g x = x) (h2 : ∀ x, g x * x⁻¹ ∈ W) : elat (mset W) (dataOf p) = true := by
  have e1 : mset W &&& fixM p = mset W := by
    apply Nat.eq_of_testBit_eq
    intro v
    rw [Nat.testBit_land]
    cases hv : (mset W).testBit v
    · rfl
    · obtain ⟨hv1, hv2⟩ := (testBit_mset W v).mp hv
      unfold fixM
      rw [testBit_maskOf]
      simp only [hv1, decide_true, Bool.true_and, beq_iff_eq]
      exact (act_eq_self_iff hg hv1).mpr (h1 _ hv2)
  have e2 : comM p &&& mset W = comM p := by
    apply Nat.eq_of_testBit_eq
    intro w
    rw [Nat.testBit_land]
    cases hw : (comM p).testBit w
    · rfl
    · obtain ⟨hw1, x, hx⟩ := exists_of_testBit_comM hg hw
      have := (testBit_mset W w).mpr ⟨hw1, hx ▸ h2 x⟩
      rw [this]
      rfl
  have e3 : elat (mset W) (dataOf p) =
      ((mset W &&& fixM p == mset W) && (comM p &&& mset W == comM p)) := by
    simp only [elat, dataOf]
  rw [e3, e1, e2, beq_self_eq_true, beq_self_eq_true]
  rfl

theorem card_le_count {E : Subgroup (MulAut VM4)}
    (hE : ∀ g ∈ E, ∃ p ∈ params, Realizes g p) (hel : IsElemAbelian2 E) {W : Set VM4}
    (h1 : ∀ g ∈ E, ∀ x ∈ W, g x = x) (h2 : ∀ g ∈ E, ∀ x, g x * x⁻¹ ∈ W) :
    Nat.card E ≤ count (mset W) := by
  classical
  have hfin : (E : Set (MulAut VM4)).Finite := Set.toFinite _
  set EF := hfin.toFinset with hEF
  have hcard : Nat.card E = EF.card := Nat.card_eq_card_finite_toFinset hfin
  set P : Par → Bool := fun p => elat (mset W) (dataOf p) with hP
  set PS := (invPars.filter P).toFinset with hPS
  have hcount : count (mset W) = (invPars.filter P).length := by
    unfold count invData
    rw [List.countP_map, List.countP_eq_length_filter]
    rfl
  let f : MulAut VM4 → Par := fun g =>
    if h : ∃ p ∈ params, Realizes g p then h.choose else ⟨1, 1, false, false⟩
  have hf : ∀ g ∈ E, f g ∈ params ∧ Realizes g (f g) := by
    intro g hg
    have h := hE g hg
    simp only [f, h, ↓reduceDIte]
    exact h.choose_spec
  have hmaps : ∀ g ∈ EF, f g ∈ PS := by
    intro g hg
    have hgE : g ∈ E := hfin.mem_toFinset.mp hg
    obtain ⟨hp, hr⟩ := hf g hgE
    have h2' : g * g = 1 := by rw [← pow_two]; exact hel.2 g hgE
    rw [hPS, List.mem_toFinset, List.mem_filter]
    exact ⟨List.mem_filter.mpr ⟨hp, isInvAct_of_realizes hr h2'⟩,
      elat_of hr (h1 g hgE) (h2 g hgE)⟩
  have hinj : Set.InjOn f EF := by
    intro g hg g' hg' hgg
    have hgE : g ∈ E := hfin.mem_toFinset.mp hg
    have hgE' : g' ∈ E := hfin.mem_toFinset.mp hg'
    have hr := (hf g hgE).2
    have hr' := (hf g' hgE').2
    rw [hgg] at hr
    exact realizes_injective hr hr'
  rw [hcard, hcount]
  exact (Finset.card_le_card_of_injOn f hmaps hinj).trans (List.toFinset_card_le _)

theorem mem_invPars {p : Par} (hp : p ∈ params) (h : isInvAct p = true) : p ∈ invPars := by
  unfold invPars
  exact List.mem_filter.mpr ⟨hp, h⟩

theorem mem_invData {p : Par} (hp : p ∈ invPars) : dataOf p ∈ invData := by
  unfold invData
  exact List.mem_map_of_mem hp

theorem dataOf_fix (p : Par) : (dataOf p).fix = fixM p := by
  simp only [dataOf]

theorem dataOf_com (p : Par) : (dataOf p).com = comM p := by
  simp only [dataOf]

theorem dataOf_bas (p : Par) : (dataOf p).bas = basisOf (comM p) := by
  simp only [dataOf]

theorem testBit_mset' (S : Set VM4) (v : ℕ) :
    (mset S).testBit v = (decide (v < 256) &&
      (by classical exact decide (Multiplicative.ofAdd (decode v) ∈ S))) := by
  classical
  unfold mset
  rw [testBit_maskOf]

def fixSet (S : Finset (MulAut VM4)) : Set VM4 := {x | ∀ g ∈ S, g x = x}

theorem mset_fixSet_empty : mset (fixSet ∅) = FULL := by
  classical
  apply Nat.eq_of_testBit_eq
  intro v
  rw [testBit_mset', testBit_FULL]
  simp [fixSet]

theorem mset_fixSet_insert {g : MulAut VM4} {p : Par} (hg : Realizes g p)
    (S : Finset (MulAut VM4)) : mset (fixSet (insert g S)) = mset (fixSet S) &&& fixM p := by
  classical
  apply Nat.eq_of_testBit_eq
  intro v
  rw [Nat.testBit_land, testBit_mset', testBit_mset']
  unfold fixM
  rw [testBit_maskOf]
  by_cases hv : v < 256
  · have h := act_eq_self_iff hg hv
    by_cases hgv : g (Multiplicative.ofAdd (decode v)) = Multiplicative.ofAdd (decode v)
    · have h' : (act p v == v) = true := beq_iff_eq.mpr (h.mpr hgv)
      simp only [hv, decide_true, Bool.true_and, h', Bool.and_true]
      congr 1
      simp only [fixSet, Set.mem_ofPred_eq, Finset.mem_insert, forall_eq_or_imp, hgv, true_and]
    · have h' : (act p v == v) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun h2 => hgv (h.mp h2)
      simp only [hv, decide_true, Bool.true_and, h', Bool.and_false]
      simp only [fixSet, Set.mem_ofPred_eq, Finset.mem_insert, forall_eq_or_imp, hgv, false_and,
        decide_false]
  · simp [hv]

theorem fixSet_eq_fixV {E : Subgroup (MulAut VM4)} {S : Finset (MulAut VM4)}
    (hS : ∀ g, g ∈ S ↔ g ∈ E) : fixSet S = (fixV E : Set VM4) := by
  ext x
  simp only [fixSet, Set.mem_ofPred_eq, SetLike.mem_coe, mem_fixV, hS]

theorem mset_fixV_mem (hcap : capOK = true) {E : Subgroup (MulAut VM4)}
    (hE : ∀ g ∈ E, ∃ p ∈ params, Realizes g p) (hel : IsElemAbelian2 E) :
    mset (fixV E : Set VM4) ∈ capL := by
  classical
  unfold capOK at hcap
  simp only [Bool.and_eq_true, List.all_eq_true] at hcap
  obtain ⟨⟨h0, hcl⟩, -⟩ := hcap
  have hfin : (E : Set (MulAut VM4)).Finite := Set.toFinite _
  have key : ∀ S : Finset (MulAut VM4), (∀ g ∈ S, g ∈ E) → mset (fixSet S) ∈ capL := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      rw [mset_fixSet_empty]
      exact mem_capL_of_memS h0
    | insert g S hgS ih =>
      intro hS
      have hgE : g ∈ E := hS g (Finset.mem_insert_self g S)
      have ih' := ih fun g' hg' => hS g' (Finset.mem_insert_of_mem hg')
      obtain ⟨p, hp, hr⟩ := hE g hgE
      have h2 : g * g = 1 := by rw [← pow_two]; exact hel.2 g hgE
      have hpi : p ∈ invPars := mem_invPars hp (isInvAct_of_realizes hr h2)
      have hd : dataOf p ∈ invData := mem_invData hpi
      have h3 := hcl _ ih' _ hd
      rw [dataOf_fix] at h3
      rw [mset_fixSet_insert hr]
      exact mem_capL_of_memS h3
  have := key hfin.toFinset fun g hg => hfin.mem_toFinset.mp hg
  rwa [fixSet_eq_fixV fun g => hfin.mem_toFinset] at this

theorem card_pow_four_le (hchk : qCheck = true) {E : Subgroup (MulAut VM4)}
    (hE : ∀ g ∈ E, ∃ p ∈ params, Realizes g p) (hel : IsElemAbelian2 E) (hq : IsQuadratic E) :
    Nat.card E ^ 4 * Nat.card (fixV E) ^ 3 ≤ 2 ^ 24 := by
  classical
  have hcap : capOK = true := by
    unfold qCheck at hchk
    simp only [Bool.and_eq_true] at hchk
    exact hchk.1.1
  have hW := mset_fixV_mem hcap hE hel
  unfold capOK at hcap
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hcap
  have hbd := hcap.2 _ hW
  have hc := card_le_count hE hel (W := (fixV E : Set VM4))
    (fun g hg x hx => (mem_fixV.mp hx) g hg)
    (fun g hg x => hq (Subgroup.subset_closure ⟨g, hg, x, rfl⟩))
  rw [popcount_mset] at hbd
  calc Nat.card E ^ 4 * Nat.card (fixV E) ^ 3
      ≤ count (mset (fixV E : Set VM4)) ^ 4 * Nat.card (fixV E : Set VM4) ^ 3 :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hc 4)
    _ ≤ 2 ^ 24 := hbd

theorem decode_zero : decode 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem mset_bot : mset ((⊥ : Subgroup VM4) : Set VM4) = 1 := by
  classical
  apply Nat.eq_of_testBit_eq
  intro v
  rw [testBit_mset']
  by_cases hv : v < 256
  · have e : (Multiplicative.ofAdd (decode v) ∈ ((⊥ : Subgroup VM4) : Set VM4)) ↔ v = 0 := by
      rw [SetLike.mem_coe, Subgroup.mem_bot]
      constructor
      · intro h
        have h1 : decode v = decode 0 := by
          rw [decode_zero]
          exact congrArg Multiplicative.toAdd h
        exact decode_injOn hv (by norm_num) h1
      · rintro rfl
        rw [decode_zero]
        rfl
    rw [show (1 : ℕ) = 2 ^ 0 from rfl, Nat.testBit_two_pow]
    simp only [hv, decide_true, Bool.true_and]
    rw [decide_eq_decide, e]
    exact eq_comm
  · have h0 : v ≠ 0 := by omega
    rw [show (1 : ℕ) = 2 ^ 0 from rfl, Nat.testBit_two_pow]
    simp [hv, Ne.symm h0]

theorem mem_sup_closure_singleton (U : Subgroup VM4) (y x : VM4) :
    x ∈ U ⊔ Subgroup.closure {y} ↔ x ∈ U ∨ x * y ∈ U := by
  constructor
  · intro hx
    let W : Subgroup VM4 :=
      { carrier := {x | x ∈ U ∨ x * y ∈ U}
        one_mem' := Or.inl U.one_mem
        mul_mem' := by
          rintro a b (ha | ha) (hb | hb)
          · exact Or.inl (U.mul_mem ha hb)
          · right
            rw [mul_assoc]
            exact U.mul_mem ha hb
          · right
            rw [mul_assoc, mul_comm b y, ← mul_assoc]
            exact U.mul_mem ha hb
          · left
            have e : a * b = a * y * (b * y) := by
              rw [mul_mul_mul_comm, mul_self_vm4, mul_one]
            rw [e]
            exact U.mul_mem ha hb
        inv_mem' := by
          intro a ha
          rwa [inv_vm4] }
    have hle : U ⊔ Subgroup.closure {y} ≤ W := by
      refine sup_le (fun u hu => Or.inl hu) ?_
      rw [Subgroup.closure_le]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact Or.inr (by rw [mul_self_vm4]; exact U.one_mem)
    exact hle hx
  · rintro (h | h)
    · exact Subgroup.mem_sup_left h
    · have e : x = x * y * y := by rw [mul_assoc, mul_self_vm4, mul_one]
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h)
        (Subgroup.mem_sup_right (Subgroup.subset_closure rfl))

theorem sumOne_mset (U : Subgroup VM4) {b : ℕ} (hb : b < 256) :
    sumOne (mset (U : Set VM4)) b =
      mset ((U ⊔ Subgroup.closure {Multiplicative.ofAdd (decode b)} : Subgroup VM4) :
        Set VM4) := by
  classical
  apply Nat.eq_of_testBit_eq
  intro v
  rw [testBit_sumOne _ hb, testBit_mset', testBit_mset', testBit_mset']
  by_cases hv : v < 256
  · have hvb : v ^^^ b < 256 := Nat.xor_lt_two_pow (n := 8) (by simpa using hv) (by simpa using hb)
    have e : Multiplicative.ofAdd (decode (v ^^^ b)) =
        Multiplicative.ofAdd (decode v) * Multiplicative.ofAdd (decode b) := by
      rw [decode_xor hv hb]
      rfl
    simp only [hv, hvb, decide_true, Bool.true_and, e, SetLike.mem_coe,
      mem_sup_closure_singleton]
    by_cases h1 : Multiplicative.ofAdd (decode v) ∈ U
    · simp [h1]
    · simp [h1]
  · simp [hv]

def spanOf (bs : List ℕ) : Subgroup VM4 :=
  Subgroup.closure {y | ∃ b ∈ bs, Multiplicative.ofAdd (decode b) = y}

theorem foldl_sumOne_mset (bs : List ℕ) (hbs : ∀ b ∈ bs, b < 256) (U : Subgroup VM4) :
    bs.foldl sumOne (mset (U : Set VM4)) = mset ((U ⊔ spanOf bs : Subgroup VM4) : Set VM4) := by
  induction bs generalizing U with
  | nil =>
    have : spanOf [] = ⊥ := by
      unfold spanOf
      simp
    simp [this]
  | cons b bs ih =>
    rw [List.foldl_cons, sumOne_mset U (hbs b (List.mem_cons_self ..)),
      ih (fun b' hb' => hbs b' (List.mem_cons_of_mem _ hb'))]
    congr 2
    have e : spanOf (b :: bs) = Subgroup.closure {Multiplicative.ofAdd (decode b)} ⊔ spanOf bs := by
      unfold spanOf
      rw [← Subgroup.closure_union]
      congr 1
      ext y
      simp [eq_comm]
    rw [e, sup_assoc]

theorem basisOf_lt (m : ℕ) : ∀ b ∈ basisOf m, b < 256 := by
  unfold basisOf
  have key : ∀ (l : List ℕ) (acc : List ℕ × ℕ), (∀ b ∈ acc.1, b < 256) → (∀ v ∈ l, v < 256) →
      ∀ b ∈ (l.foldl (fun (acc : List ℕ × ℕ) v =>
        if m.testBit v && !acc.2.testBit v then (v :: acc.1, sumOne acc.2 v) else acc) acc).1,
        b < 256 := by
    intro l
    induction l with
    | nil => intro acc h _; exact h
    | cons v l ih =>
      intro acc h hl
      rw [List.foldl_cons]
      apply ih _ _ (fun v' hv' => hl v' (List.mem_cons_of_mem _ hv'))
      split_ifs
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hl b (List.mem_cons_self ..)
        · exact h b hb
      · exact h
  exact key _ _ (by simp) (fun v hv => List.mem_range.mp hv)

def cmSet (S : Finset (MulAut VM4)) : Subgroup VM4 :=
  Subgroup.closure {y | ∃ g ∈ S, ∃ x, g x * x⁻¹ = y}

theorem cmSet_insert (g : MulAut VM4) (S : Finset (MulAut VM4)) :
    cmSet (insert g S) = cmSet S ⊔ Subgroup.closure {y | ∃ x, g x * x⁻¹ = y} := by
  unfold cmSet
  rw [← Subgroup.closure_union]
  congr 1
  ext y
  simp only [Finset.mem_insert, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨g', hg' | hg', x, rfl⟩
    · subst hg'; exact Or.inr ⟨x, rfl⟩
    · exact Or.inl ⟨g', hg', x, rfl⟩
  · rintro (⟨g', hg', x, rfl⟩ | ⟨x, rfl⟩)
    · exact ⟨g', Or.inr hg', x, rfl⟩
    · exact ⟨g, Or.inl rfl, x, rfl⟩

theorem closure_comm_eq_spanOf (hbas : basOK = true) {g : MulAut VM4} {p : Par}
    (hg : Realizes g p) (hp : p ∈ invPars) :
    Subgroup.closure {y | ∃ x, g x * x⁻¹ = y} = spanOf (basisOf (comM p)) := by
  classical
  let Cg : Subgroup VM4 :=
    { carrier := {y | ∃ x, g x * x⁻¹ = y}
      one_mem' := ⟨1, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        refine ⟨a * b, ?_⟩
        rw [map_mul, inv_vm4, inv_vm4, inv_vm4]
        rw [mul_mul_mul_comm]
      inv_mem' := by
        rintro _ ⟨a, rfl⟩
        exact ⟨a, by rw [inv_vm4 (g a * a⁻¹)]⟩ }
  have hCg : Subgroup.closure {y | ∃ x, g x * x⁻¹ = y} = Cg :=
    le_antisymm ((Subgroup.closure_le Cg).mpr fun y hy => hy) Subgroup.subset_closure
  rw [hCg]
  unfold basOK at hbas
  rw [List.all_eq_true] at hbas
  have h1 := hbas _ (mem_invData hp)
  rw [dataOf_bas, dataOf_com, beq_iff_eq] at h1
  have h2 := foldl_sumOne_mset (basisOf (comM p)) (basisOf_lt _) ⊥
  rw [mset_bot, bot_sup_eq] at h2
  rw [h1] at h2
  have h3 : comM p = mset (Cg : Set VM4) := by
    apply Nat.eq_of_testBit_eq
    intro w
    apply Bool.eq_iff_iff.mpr
    rw [testBit_mset]
    constructor
    · intro hw
      obtain ⟨hw1, x, hx⟩ := exists_of_testBit_comM hg hw
      exact ⟨hw1, ⟨x, hx.symm⟩⟩
    · rintro ⟨hw1, x, hx⟩
      have := testBit_comM_of hg x
      rwa [hx, toAdd_ofAdd, code_decode hw1] at this
  exact SetLike.coe_injective (mset_injective (h3.symm.trans h2))

theorem cmSet_empty : cmSet ∅ = ⊥ := by
  unfold cmSet
  simp

theorem cmSet_eq_commV {E : Subgroup (MulAut VM4)} {S : Finset (MulAut VM4)}
    (hS : ∀ g, g ∈ S ↔ g ∈ E) : cmSet S = commV E := by
  unfold cmSet commV
  congr 1
  ext y
  simp only [Set.mem_ofPred_eq, hS]

theorem mset_commV_mem (hplus : plusOK = true) (hbas : basOK = true)
    {E : Subgroup (MulAut VM4)} (hE : ∀ g ∈ E, ∃ p ∈ params, Realizes g p)
    (hel : IsElemAbelian2 E) : mset (commV E : Set VM4) ∈ plusL := by
  classical
  unfold plusOK at hplus
  simp only [Bool.and_eq_true, List.all_eq_true] at hplus
  obtain ⟨⟨h0, hcl⟩, -⟩ := hplus
  have hfin : (E : Set (MulAut VM4)).Finite := Set.toFinite _
  have key : ∀ S : Finset (MulAut VM4), (∀ g ∈ S, g ∈ E) → mset (cmSet S : Set VM4) ∈ plusL := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      rw [cmSet_empty, mset_bot]
      exact mem_plusL_of_memS h0
    | insert g S hgS ih =>
      intro hS
      have hgE : g ∈ E := hS g (Finset.mem_insert_self g S)
      have ih' := ih fun g' hg' => hS g' (Finset.mem_insert_of_mem hg')
      obtain ⟨p, hp, hr⟩ := hE g hgE
      have h2 : g * g = 1 := by rw [← pow_two]; exact hel.2 g hgE
      have hpi : p ∈ invPars := mem_invPars hp (isInvAct_of_realizes hr h2)
      have hd : dataOf p ∈ invData := mem_invData hpi
      have h3 := hcl _ ih' _ hd
      rw [dataOf_bas, foldl_sumOne_mset _ (basisOf_lt _)] at h3
      rw [cmSet_insert, closure_comm_eq_spanOf hbas hr hpi]
      exact mem_plusL_of_memS h3
  have := key hfin.toFinset fun g hg => hfin.mem_toFinset.mp hg
  rwa [cmSet_eq_commV fun g => hfin.mem_toFinset] at this

theorem card_lt_card_commV (hchk : qCheck = true) {E : Subgroup (MulAut VM4)}
    (hE : ∀ g ∈ E, ∃ p ∈ params, Realizes g p) (hel : IsElemAbelian2 E) (hq : IsQuadratic E)
    (hne : E ≠ ⊥) : Nat.card E < Nat.card (commV E) := by
  classical
  unfold qCheck at hchk
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨-, hplus⟩, hbas⟩ := hchk
  have hU := mset_commV_mem hplus hbas hE hel
  unfold plusOK at hplus
  simp only [Bool.and_eq_true, List.all_eq_true] at hplus
  have hbd := hplus.2 _ hU
  have hc := card_le_count hE hel (W := (commV E : Set VM4))
    (fun g hg x hx => (mem_fixV.mp (hq hx)) g hg)
    (fun g hg x => Subgroup.subset_closure ⟨g, hg, x, rfl⟩)
  by_cases h1 : mset (commV E : Set VM4) = 1
  · exfalso
    apply hne
    have hU0 : commV E = ⊥ := by
      rw [← mset_bot] at h1
      exact SetLike.coe_injective (mset_injective h1)
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    refine MulEquiv.ext fun x => ?_
    have hx : g x * x⁻¹ ∈ commV E := Subgroup.subset_closure ⟨g, hg, x, rfl⟩
    rw [hU0, Subgroup.mem_bot, mul_inv_eq_one] at hx
    exact hx
  · have h1' : (mset (commV E : Set VM4) == 1) = false := beq_eq_false_iff_ne.mpr h1
    rw [h1', Bool.false_or, decide_eq_true_eq, popcount_mset] at hbd
    exact lt_of_le_of_lt hc hbd

end CFSG.Quasithin.H13.Ch9.L34Q
