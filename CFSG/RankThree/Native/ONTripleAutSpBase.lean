
module

public import CFSG.RankThree.Native.ONTripleAutData
public import CFSG.RankThree.Native.ONTripleNorm
public import CFSG.RankThree.Native.ONTripleA6
public meta import CFSG.RankThree.Native.ONTripleNorm
public meta import CFSG.RankThree.Native.ONTripleAutData
public meta import CFSG.RankThree.Native.ONTripleA6
public import CFSG.RankThree.Native.ONTripleAutSpInputs

@[expose] public section

namespace CFSG.RankThree.Native.ONTriple

open Equiv

@[expose] def matNM (k : ℕ) : M4 := Matrix.of (matN k)

@[expose] def decA (a : Array ℕ) : M4 :=
  Matrix.of fun i j => ((a[4 * i.val + j.val]! : ℕ) : ZMod 3)

@[expose] def ValidA (a : Array ℕ) : Prop := a.size = 16 ∧ ∀ k < 16, a[k]! < 3

theorem encA_getElem! (T : M4) {k : ℕ} (hk : k < 16) :
    (encA T)[k]! = (T ⟨k / 4, by omega⟩ ⟨k % 4, Nat.mod_lt _ (by norm_num)⟩).val := by
  rw [encA, getElem!_pos _ _ (by simpa using hk), Array.getElem_ofFn]

theorem decA_encA (T : M4) : decA (encA T) = T := by
  ext i j
  rw [decA, Matrix.of_apply, encA_getElem! T (by omega)]
  have hi : (4 * i.val + j.val) / 4 = i.val := by omega
  have hj : (4 * i.val + j.val) % 4 = j.val := by omega
  simp only [hi, hj, ZMod.natCast_val, ZMod.cast_id', id]

theorem validA_encA (T : M4) : ValidA (encA T) := by
  refine ⟨by simp [encA], fun k hk => ?_⟩
  rw [encA_getElem! T hk]
  exact ZMod.val_lt _

theorem encA_decA {a : Array ℕ} (ha : ValidA a) : encA (decA a) = a := by
  apply Array.ext
  · rw [ha.1]
    simp [encA]
  · intro k hk1 hk2
    have hk : k < 16 := by simpa [encA] using hk1
    have e := encA_getElem! (decA a) hk
    rw [getElem!_pos (encA (decA a)) k hk1] at e
    rw [e, decA, Matrix.of_apply]
    have hidx : 4 * (k / 4) + k % 4 = k := by omega
    simp only [hidx]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (ha.2 k hk), getElem!_pos a k hk2]

theorem decA_injective {a b : Array ℕ} (ha : ValidA a) (hb : ValidA b) (h : decA a = decA b) :
    a = b := by
  rw [← encA_decA ha, ← encA_decA hb, h]

theorem amul_getElem! (a b : Array ℕ) {k : ℕ} (hk : k < 16) :
    (amul a b)[k]! = (a[4 * (k / 4)]! * b[k % 4]! + a[4 * (k / 4) + 1]! * b[4 + k % 4]! +
      a[4 * (k / 4) + 2]! * b[8 + k % 4]! + a[4 * (k / 4) + 3]! * b[12 + k % 4]!) % 3 := by
  rw [amul, getElem!_pos _ _ (by simpa using hk), Array.getElem_ofFn]

theorem validA_amul (a b : Array ℕ) : ValidA (amul a b) := by
  refine ⟨by simp [amul], fun k hk => ?_⟩
  rw [amul_getElem! a b hk]
  exact Nat.mod_lt _ (by norm_num)

theorem decA_amul (a b : Array ℕ) : decA (amul a b) = decA a * decA b := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_four, decA, Matrix.of_apply, amul_getElem! a b (by omega)]
  have hi : (4 * i.val + j.val) / 4 = i.val := by omega
  have hj : (4 * i.val + j.val) % 4 = j.val := by omega
  simp only [hi, hj, decA, Matrix.of_apply, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul,
    Fin.val_zero, Fin.val_one, Fin.val_two, show ((3 : Fin 4) : ℕ) = 3 from rfl]
  ring_nf

theorem validA_idA : ValidA idA := ⟨rfl, by decide⟩

theorem decA_idA : decA idA = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem decA_apow (a : Array ℕ) (k : ℕ) : decA (apow a k) = decA a ^ k := by
  induction k with
  | zero => exact decA_idA
  | succ k ih => rw [apow, decA_amul, ih, pow_succ]

theorem validA_apow (a : Array ℕ) (k : ℕ) : ValidA (apow a k) := by
  cases k with
  | zero => exact validA_idA
  | succ k => exact validA_amul _ _

theorem decA_atr (a : Array ℕ) : decA (atr a) = (decA a).transpose := by
  ext i j
  rw [Matrix.transpose_apply, decA, decA, Matrix.of_apply, Matrix.of_apply, atr,
    getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]
  have hi : (4 * i.val + j.val) % 4 = j.val := by omega
  have hj : (4 * i.val + j.val) / 4 = i.val := by omega
  simp only [hi, hj]

theorem decA_M0A : decA M0A = matNM 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem decA_M1A : decA M1A = matNM 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem decA_toArray (l : List ℕ) : decA l.toArray = toM4 l := by
  ext i j
  rw [decA, toM4, Matrix.of_apply, Matrix.of_apply, List.getElem!_toArray,
    List.getD_eq_getElem?_getD, getElem!_def]
  cases l[4 * i.val + j.val]? <;> rfl

theorem validA_toArray {l : List ℕ} (hl : l.length = 16) (h3 : ∀ x ∈ l, x < 3) :
    ValidA l.toArray := by
  refine ⟨by simpa using hl, fun k hk => ?_⟩
  rw [List.getElem!_toArray, getElem!_pos l k (by rw [hl]; exact hk)]
  exact h3 _ (List.getElem_mem _)

theorem matNM_of_ne {k : ℕ} (hk : ¬ k = 0) : matNM k = matNM 1 := by
  ext i j
  simp only [matNM, Matrix.of_apply, matN, eN, hk, ↓reduceIte, one_ne_zero]

theorem foldl_amul (w : List ℕ) (a : Array ℕ) :
    decA (w.foldl (fun a k => amul a (if k = 0 then M0A else M1A)) a) =
      decA a * (w.map fun k => matNM k).prod := by
  induction w generalizing a with
  | nil => simp
  | cons k w ih =>
    rw [List.foldl_cons, ih, decA_amul, List.map_cons, List.prod_cons, mul_assoc]
    congr 2
    split_ifs with hk
    · rw [hk, decA_M0A]
    · rw [matNM_of_ne hk, decA_M1A]

@[expose] def vcode (v : Fin 4 → ZMod 3) : ℕ :=
  (v 0).val + 3 * (v 1).val + 9 * (v 2).val + 27 * (v 3).val

theorem vcode_lt (v : Fin 4 → ZMod 3) : vcode v < 81 := by
  have := ZMod.val_lt (v 0)
  have := ZMod.val_lt (v 1)
  have := ZMod.val_lt (v 2)
  have := ZMod.val_lt (v 3)
  unfold vcode
  omega

theorem vdec_vcode (v : Fin 4 → ZMod 3) : vdec (vcode v) = v := by
  have h0 := ZMod.val_lt (v 0)
  have h1 := ZMod.val_lt (v 1)
  have h2 := ZMod.val_lt (v 2)
  have h3 := ZMod.val_lt (v 3)
  have e0 : vcode v % 3 = (v 0).val := by unfold vcode; omega
  have e1 : vcode v / 3 % 3 = (v 1).val := by unfold vcode; omega
  have e2 : vcode v / 9 % 3 = (v 2).val := by unfold vcode; omega
  have e3 : vcode v / 27 % 3 = (v 3).val := by unfold vcode; omega
  funext i
  fin_cases i
  · show ((vcode v % 3 : ℕ) : ZMod 3) = v 0
    rw [e0, ZMod.natCast_val, ZMod.cast_id', id]
  · show ((vcode v / 3 % 3 : ℕ) : ZMod 3) = v 1
    rw [e1, ZMod.natCast_val, ZMod.cast_id', id]
  · show ((vcode v / 9 % 3 : ℕ) : ZMod 3) = v 2
    rw [e2, ZMod.natCast_val, ZMod.cast_id', id]
  · show ((vcode v / 27 % 3 : ℕ) : ZMod 3) = v 3
    rw [e3, ZMod.natCast_val, ZMod.cast_id', id]

theorem tpTab_getElem! {a b : ℕ} (ha : a < 81) (hb : b < 81) :
    tpTab[a * 81 + b]! = (ThreeQRel.threePair omegaZ (vdec a) (vdec b)).val := by
  rw [tpTab, getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]
  simp only
  rw [show (a * 81 + b) / 81 = a by omega, show (a * 81 + b) % 81 = b by omega]

@[expose] def symInvM (T : M4) : M4 := decA OmA * T.transpose * decA OmInvA

theorem decA_symInvA (T : M4) : decA (symInvA (encA T)) = symInvM T := by
  rw [symInvA, decA_amul, decA_amul, decA_atr, decA_encA, symInvM]

theorem omegaZ_vals : (omegaZ 0 1).val = 0 ∧ (omegaZ 0 2).val = 0 ∧ (omegaZ 1 2).val = 2 ∧
    (omegaZ 0 3).val = 1 ∧ (omegaZ 1 3).val = 2 ∧ (omegaZ 2 3).val = 0 := by
  decide

theorem map_evW {X Y : Type*} [Monoid X] [Monoid Y] (f : X →* Y) (a b : X) (w : List ℕ) :
    f (evW a b w) = evW (f a) (f b) w := by
  rw [evW, evW, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  simp only [Function.comp_apply]
  split_ifs <;> rfl

theorem sK_words : evW sK1 sK2 Wy0 = sY 0 ∧ evW sK1 sK2 Wy1 = sY 1 ∧ evW sK1 sK2 Wt4 = s4 ∧
    sK1 ^ 3 = 1 ∧ sK2 ^ 3 = 1 ∧ (sK1 * sK2) ^ 5 = 1 := by
  decide +kernel

end CFSG.RankThree.Native.ONTriple
