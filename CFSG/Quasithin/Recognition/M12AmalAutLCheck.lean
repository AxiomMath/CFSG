module

public import CFSG.Quasithin.Recognition.M12AmalAutJCheck
public import CFSG.Quasithin.Recognition.M12AmalAutLData
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

public section

namespace CFSG.Quasithin.M12AmalAut

open CFSG.Sporadic.Bridge Equiv

@[expose] def NormFwd (gs : List ℕ) (L : List ℕ) : Prop :=
  ∀ k ∈ gs, ∀ j ∈ L, ∃ i' ∈ L, compL (compL (gl k) (tl j)) (gil k) = tl i'

instance (gs L : List ℕ) : Decidable (NormFwd gs L) := by unfold NormFwd; infer_instance

@[expose] def NormBoth (gs : List ℕ) (L : List ℕ) : Prop :=
  ∀ k ∈ gs, ∀ j ∈ L,
    (∃ i' ∈ L, compL (compL (gl k) (tl j)) (gil k) = tl i') ∧
      (∃ i' ∈ L, compL (compL (gil k) (tl j)) (gl k) = tl i')

instance (gs L : List ℕ) : Decidable (NormBoth gs L) := by unfold NormBoth; infer_instance

@[expose] def commI (i j : ℕ) : ℕ := telMul (telMul (telMul i j) (telInv i)) (telInv j)

@[expose] def LAq (i : ℕ) : Prop :=
  compL (compL (gl 3) (tl i)) (gil 3) ∈ telTab ∧ compL (compL (gil 3) (tl i)) (gl 3) ∈ telTab

instance (i : ℕ) : Decidable (LAq i) := by unfold LAq; infer_instance

theorem laIdx_basic_chk : laIdx.length = 64 ∧ laIdx.Nodup ∧ (∀ i ∈ laIdx, i < 128) ∧ 0 ∈ laIdx := by
  decide +kernel

theorem laIdx_mul_chk1 : ∀ i ∈ laIdx.take 32, ∀ j ∈ laIdx, telMul i j ∈ laIdx := by decide +kernel

theorem laIdx_mul_chk2 : ∀ i ∈ laIdx.drop 32, ∀ j ∈ laIdx, telMul i j ∈ laIdx := by decide +kernel

theorem laIdx_chk : laIdx.length = 64 ∧ laIdx.Nodup ∧ (∀ i ∈ laIdx, i < 128) ∧ 0 ∈ laIdx ∧
    (∀ i ∈ laIdx, ∀ j ∈ laIdx, telMul i j ∈ laIdx) := by
  refine ⟨laIdx_basic_chk.1, laIdx_basic_chk.2.1, laIdx_basic_chk.2.2.1, laIdx_basic_chk.2.2.2,
    fun i hi j hj => ?_⟩
  have h : i ∈ laIdx.take 32 ∨ i ∈ laIdx.drop 32 := by
    rw [← List.mem_append, List.take_append_drop]
    exact hi
  rcases h with h | h
  · exact laIdx_mul_chk1 i h j hj
  · exact laIdx_mul_chk2 i h j hj

theorem laIdx_inv_chk : ∀ i ∈ laIdx, telInv i ∈ laIdx := by decide +kernel

theorem laIdx_iff_chk : ∀ i < 128, LAq i ↔ i ∈ laIdx := by decide +kernel

theorem laIdx_norm_chk : NormBoth [0, 1, 2, 3] laIdx := by decide +kernel

theorem zIdx_chk : (∀ i ∈ zIdx, i ∈ laIdx) ∧ 0 ∈ zIdx ∧
    ∀ i ∈ laIdx, (∀ j ∈ laIdx, telMul i j = telMul j i) ↔ i ∈ zIdx := by decide +kernel

theorem fIdx_chk : fIdx.length = 8 ∧ fIdx.Nodup ∧ (∀ i ∈ fIdx, i ∈ laIdx) ∧ (∀ i ∈ fIdx, telMul i i = 0) ∧
    ∀ i ∈ laIdx, (∀ j ∈ laIdx, commI i j ∈ zIdx) ↔ i ∈ fIdx := by decide +kernel

@[expose] def cosetOf (k : ℕ) : List ℕ := cosetTab.getD k []

theorem cosetTab_chk : cosetTab.length = 8 ∧ (∀ k < 8, (cosetOf k).Nodup) ∧
    (∀ k < 8, ∀ i ∈ cosetOf k, i ∈ laIdx) ∧ (∀ i ∈ laIdx, ∃ k < 8, i ∈ cosetOf k) ∧
    (∀ k < 8, ∀ i ∈ cosetOf k, ∃ f ∈ fIdx, telMul ((cosetOf k).headD 0) f = i) ∧
    (∀ k < 8, ∀ i ∈ cosetOf k, ∃ f ∈ fIdx, telMul i f = (cosetOf k).headD 0) ∧
    (cosetOf 0).headD 0 = 0 := by decide +kernel

@[expose] def maskOf (p : ℕ → Bool) : List Bool := [p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7]

theorem maskOf_getD (p : ℕ → Bool) (k : ℕ) (hk : k < 8) : (maskOf p).getD k false = p k := by
  unfold maskOf
  interval_cases k <;> rfl

@[expose] def maskSet (bs : List Bool) : List ℕ :=
  (List.range 8).flatMap fun k => if bs.getD k false then cosetOf k else []

theorem mem_maskSet {bs : List Bool} {i : ℕ} :
    i ∈ maskSet bs ↔ ∃ k < 8, bs.getD k false = true ∧ i ∈ cosetOf k := by
  unfold maskSet
  simp only [List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨k, hk, h⟩
    split_ifs at h with hb
    · exact ⟨k, hk, hb, h⟩
    · simp at h
  · rintro ⟨k, hk, hb, h⟩
    refine ⟨k, hk, ?_⟩
    split_ifs
    exact h

@[expose] def TrichotomyOK (X : List ℕ) : Prop :=
  (∀ i < 128, i ∈ X ↔ i ∈ fIdx) ∨ (X.length = 16 ∧ ∀ i ∈ X, telMul i i = 0 → i ∈ fIdx) ∨
    (∀ i ∈ wIdx, i ∈ X)

instance (X : List ℕ) : Decidable (TrichotomyOK X) := by unfold TrichotomyOK; infer_instance

@[expose] def MaskOK (bs : List Bool) : Prop :=
  (maskSet bs).Nodup ∧ (bs.getD 0 false = true →
    (∀ i ∈ maskSet bs, ∀ j ∈ maskSet bs, telMul i j ∈ maskSet bs) →
    NormFwd [0, 1, 2, 3] (maskSet bs) → TrichotomyOK (maskSet bs))

instance (bs : List Bool) : Decidable (MaskOK bs) := by unfold MaskOK; infer_instance

theorem mask_c0 : ∀ b4 b5 b6 b7 : Bool, MaskOK [false, false, false, false, b4, b5, b6, b7] := by
  decide +kernel

theorem mask_c1 : ∀ b4 b5 b6 b7 : Bool, MaskOK [false, false, false, true, b4, b5, b6, b7] := by
  decide +kernel

theorem mask_c2 : ∀ b4 b5 b6 b7 : Bool, MaskOK [false, false, true, false, b4, b5, b6, b7] := by
  decide +kernel

theorem mask_c3 : ∀ b4 b5 b6 b7 : Bool, MaskOK [false, false, true, true, b4, b5, b6, b7] := by
  decide +kernel

theorem mask_c4 : ∀ b4 b5 b6 b7 : Bool, MaskOK [false, true, false, false, b4, b5, b6, b7] := by
  decide +kernel

theorem mask_c5 : ∀ b4 b5 b6 b7 : Bool, MaskOK [false, true, false, true, b4, b5, b6, b7] := by
  decide +kernel

theorem mask_c6 : ∀ b4 b5 b6 b7 : Bool, MaskOK [false, true, true, false, b4, b5, b6, b7] := by
  decide +kernel

theorem mask_c7 : ∀ b4 b5 b6 b7 : Bool, MaskOK [false, true, true, true, b4, b5, b6, b7] := by
  decide +kernel

theorem mask_c8 : ∀ b4 b5 b6 b7 : Bool, MaskOK [true, false, false, false, b4, b5, b6, b7] := by
  decide +kernel

theorem mask_c9 : ∀ b4 b5 b6 b7 : Bool, MaskOK [true, false, false, true, b4, b5, b6, b7] := by
  decide +kernel

theorem mask_c10 : ∀ b4 b5 b6 b7 : Bool, MaskOK [true, false, true, false, b4, b5, b6, b7] := by
  decide +kernel

theorem mask_c11 : ∀ b4 b5 b6 b7 : Bool, MaskOK [true, false, true, true, b4, b5, b6, b7] := by
  decide +kernel

theorem mask_c12 : ∀ b4 b5 b6 b7 : Bool, MaskOK [true, true, false, false, b4, b5, b6, b7] := by
  decide +kernel

theorem mask_c13 : ∀ b4 b5 b6 b7 : Bool, MaskOK [true, true, false, true, b4, b5, b6, b7] := by
  decide +kernel

theorem mask_c14 : ∀ b4 b5 b6 b7 : Bool, MaskOK [true, true, true, false, b4, b5, b6, b7] := by
  decide +kernel

theorem mask_c15 : ∀ b4 b5 b6 b7 : Bool, MaskOK [true, true, true, true, b4, b5, b6, b7] := by
  decide +kernel

theorem mask_chk8 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool, MaskOK [b0, b1, b2, b3, b4, b5, b6, b7] := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3
  exacts [
    mask_c0 b4 b5 b6 b7,
    mask_c1 b4 b5 b6 b7,
    mask_c2 b4 b5 b6 b7,
    mask_c3 b4 b5 b6 b7,
    mask_c4 b4 b5 b6 b7,
    mask_c5 b4 b5 b6 b7,
    mask_c6 b4 b5 b6 b7,
    mask_c7 b4 b5 b6 b7,
    mask_c8 b4 b5 b6 b7,
    mask_c9 b4 b5 b6 b7,
    mask_c10 b4 b5 b6 b7,
    mask_c11 b4 b5 b6 b7,
    mask_c12 b4 b5 b6 b7,
    mask_c13 b4 b5 b6 b7,
    mask_c14 b4 b5 b6 b7,
    mask_c15 b4 b5 b6 b7]

theorem mask_chk (p : ℕ → Bool) : MaskOK (maskOf p) :=
  mask_chk8 (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6) (p 7)

theorem invPIdx_chk : (∀ i ∈ invPIdx, i ∈ laIdx ∧ i ≠ 0 ∧ telMul i i = 0) ∧
    ∀ i ∈ laIdx, i ≠ 0 → telMul i i = 0 → i ∈ invPIdx := by decide +kernel

theorem wIdx_chk : wIdx.length = 32 ∧ wIdx.Nodup ∧ (∀ i ∈ wIdx, i ∈ laIdx) ∧ 0 ∈ wIdx ∧
    (∀ i ∈ wIdx, ∀ j ∈ wIdx, telMul i j ∈ wIdx) := by decide +kernel

theorem wIdx_inv_chk : ∀ i ∈ wIdx, telInv i ∈ wIdx := by decide +kernel

theorem wIdx_invol_chk : ∀ i ∈ laIdx, telMul i i = 0 → i ∈ wIdx := by decide +kernel

theorem wWords_chk : ∀ i ∈ wIdx, ∃ w ∈ wWords, (∀ l ∈ w, l ∈ invPIdx) ∧ w.foldl telMul 0 = i := by
  decide +kernel

@[expose] def q8Idx' (A X : List ℕ) : QuaternionGroup 2 → ℕ
  | .a i => A.getD i.val 0
  | .xa i => X.getD i.val 0

@[expose] def Q8Tab (A X : List ℕ) : Prop :=
  (∀ g h : QuaternionGroup 2, q8Idx' A X g < 128 ∧ q8Idx' A X h < 128 ∧
    compL (tl (q8Idx' A X g)) (tl (q8Idx' A X h)) = tl (q8Idx' A X (g * h))) ∧
  (∀ g h : QuaternionGroup 2, q8Idx' A X g = q8Idx' A X h → g = h) ∧ q8Idx' A X 1 = 0

instance (A X : List ℕ) : Decidable (Q8Tab A X) := by unfold Q8Tab; infer_instance

theorem q8a_chk : Q8Tab q8aA q8aX := by decide +kernel

theorem q8b_chk : Q8Tab q8bA q8bX := by decide +kernel

@[expose] def q8List (A X : List ℕ) : List ℕ := A ++ X

theorem q8_lt_chk : (∀ i ∈ q8List q8aA q8aX, i < 128) ∧ (∀ i ∈ q8List q8bA q8bX, i < 128) := by
  decide +kernel

theorem q8_incl_chk : (∀ i ∈ q8List q8aA q8aX, i ∈ wIdx) ∧ (∀ i ∈ q8List q8bA q8bX, i ∈ wIdx) := by
  decide +kernel

theorem q8_comm_chk : ∀ i ∈ q8List q8aA q8aX, ∀ j ∈ q8List q8bA q8bX, telMul i j = telMul j i := by
  decide +kernel

theorem q8_gen_chk : ∀ i ∈ wIdx, ∃ a ∈ q8List q8aA q8aX, ∃ b ∈ q8List q8bA q8bX, telMul a b = i := by
  decide +kernel

theorem q8_surj_chk : (∀ i ∈ q8List q8aA q8aX, ∃ g : QuaternionGroup 2, q8Idx' q8aA q8aX g = i) ∧
    (∀ i ∈ q8List q8bA q8bX, ∃ g : QuaternionGroup 2, q8Idx' q8bA q8bX g = i) ∧
    (∀ g : QuaternionGroup 2, q8Idx' q8aA q8aX g ∈ q8List q8aA q8aX) ∧
    (∀ g : QuaternionGroup 2, q8Idx' q8bA q8bX g ∈ q8List q8bA q8bX) := by
  decide +kernel

theorem erIdx_chk8 : erIdx.length = 8 ∧ erIdx.Nodup ∧ (∀ i ∈ erIdx, i ∈ wIdx) := by decide +kernel

theorem V4_chk : ∀ ia ∈ invPIdx, ∀ ib ∈ laIdx, ib ≠ 0 → ib ≠ ia →
    (∀ i ∈ [0, ia, ib, telMul ia ib], ∀ j ∈ [0, ia, ib, telMul ia ib],
      telMul i j ∈ [0, ia, ib, telMul ia ib]) →
    NormFwd [0, 1, 2, 4] [0, ia, ib, telMul ia ib] →
    ia ∈ erIdx ∧ ib ∈ erIdx ∧ telMul ia ib ∈ erIdx := by decide +kernel

end CFSG.Quasithin.M12AmalAut
