module

public import CFSG.Quasithin.Recognition.G2AmalE8Data
public import CFSG.Quasithin.Recognition.CertPermList
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

public section

namespace CFSG.Quasithin.G2AmalE8

@[expose] def gl (k : ℕ) : List ℕ := genTab.getD k []

@[expose] def gil (k : ℕ) : List ℕ := genInvTab.getD k []

@[expose] def idl : List ℕ := List.range 28

@[expose] def sl (i : ℕ) : List ℕ := sTab.getD i []

@[expose] def smul (i j : ℕ) : ℕ := (mulTab.getD i []).getD j 0

@[expose] def sinv (i : ℕ) : ℕ := invTab.getD i 0

theorem sTab_chk : ∀ i < 64,
    sl i = compL (telTab.getD (i % 32) []) (if i < 32 then idl else piTab) := by decide +kernel

theorem sl_inj_chk : ∀ i < 64, ∀ j < 64, sl i = sl j → i = j := by decide +kernel

theorem sl_mem_chk : ∀ i < 64, sl i ∈ sTab := by decide +kernel

@[expose] def MulRowOK (i : ℕ) : Prop :=
  ∀ j < 64, smul i j < 64 ∧ compL (sl i) (sl j) = sl (smul i j)

instance (i : ℕ) : Decidable (MulRowOK i) := by unfold MulRowOK; infer_instance

theorem smul_c0 : ∀ i, 0 ≤ i → i < 16 → MulRowOK i := by decide +kernel

theorem smul_c1 : ∀ i, 16 ≤ i → i < 32 → MulRowOK i := by decide +kernel

theorem smul_c2 : ∀ i, 32 ≤ i → i < 48 → MulRowOK i := by decide +kernel

theorem smul_c3 : ∀ i, 48 ≤ i → i < 64 → MulRowOK i := by decide +kernel

theorem smul_chk (i : ℕ) (hi : i < 64) : MulRowOK i := by
  by_cases h0 : i < 16
  · exact smul_c0 i (by omega) h0
  by_cases h1 : i < 32
  · exact smul_c1 i (by omega) h1
  by_cases h2 : i < 48
  · exact smul_c2 i (by omega) h2
  exact smul_c3 i (by omega) hi

theorem sinv_chk : ∀ i < 64, sinv i < 64 ∧ compL (sl i) (sl (sinv i)) = idl := by decide +kernel

@[expose] def NormFwd (gs : List ℕ) (L : List ℕ) : Prop :=
  ∀ k ∈ gs, ∀ j ∈ L, ∃ i' ∈ L, compL (compL (gl k) (sl j)) (gil k) = sl i'

instance (gs L : List ℕ) : Decidable (NormFwd gs L) := by unfold NormFwd; infer_instance

@[expose] def NormBoth (gs : List ℕ) (L : List ℕ) : Prop :=
  ∀ k ∈ gs, ∀ j ∈ L,
    (∃ i' ∈ L, compL (compL (gl k) (sl j)) (gil k) = sl i') ∧
      (∃ i' ∈ L, compL (compL (gil k) (sl j)) (gl k) = sl i')

instance (gs L : List ℕ) : Decidable (NormBoth gs L) := by unfold NormBoth; infer_instance

@[expose] def LX (k : ℕ) (i : ℕ) : Prop :=
  compL (compL (gl k) (sl i)) (gil k) ∈ sTab ∧ compL (compL (gil k) (sl i)) (gl k) ∈ sTab

instance (k i : ℕ) : Decidable (LX k i) := by unfold LX; infer_instance

theorem qIdx_chk : qIdx.length = 32 ∧ qIdx.Nodup ∧ (∀ i ∈ qIdx, i < 64) ∧ 0 ∈ qIdx ∧
    (∀ i ∈ qIdx, ∀ j ∈ qIdx, smul i j ∈ qIdx) := by decide +kernel

theorem qIdx_inv_chk : ∀ i ∈ qIdx, sinv i ∈ qIdx := by decide +kernel

theorem qIdx_iff_chk : ∀ i < 64, LX 4 i ↔ i ∈ qIdx := by decide +kernel

theorem qIdx_norm_chk : NormBoth [0, 1, 2, 4, 5] qIdx := by decide +kernel

theorem cIdx_chk : cIdx.length = 32 ∧ cIdx.Nodup ∧ (∀ i ∈ cIdx, i < 64) ∧ 0 ∈ cIdx ∧
    (∀ i ∈ cIdx, ∀ j ∈ cIdx, smul i j ∈ cIdx) := by decide +kernel

theorem cIdx_inv_chk : ∀ i ∈ cIdx, sinv i ∈ cIdx := by decide +kernel

theorem cIdx_iff_chk : ∀ i < 64, LX 3 i ↔ i ∈ cIdx := by decide +kernel

theorem cIdx_norm_chk : NormBoth [0, 1, 2, 3, 5] cIdx := by decide +kernel

theorem cIdx_central_chk : 8 ∈ cIdx ∧ 12 ∈ cIdx ∧ sl 8 ≠ idl ∧ sl 12 ≠ idl ∧ sl 8 ≠ sl 12 ∧
    ∀ i ∈ cIdx, smul 8 i = smul i 8 ∧ smul 12 i = smul i 12 := by decide +kernel

theorem invQIdx_chk : (∀ i ∈ invQIdx, i ∈ qIdx ∧ i ≠ 0 ∧ smul i i = 0) ∧
    ∀ i ∈ qIdx, i ≠ 0 → smul i i = 0 → i ∈ invQIdx := by decide +kernel

theorem eIdx_chk : eIdx.length = 8 ∧ eIdx.Nodup ∧ (∀ i ∈ eIdx, i ∈ qIdx) ∧ 0 ∈ eIdx ∧
    ∀ i ∈ eIdx, ∀ j ∈ eIdx, smul i j ∈ eIdx ∧ smul i j = smul j i ∧ smul i i = 0 := by
  decide +kernel

theorem eIdx_inv_chk : ∀ i ∈ eIdx, sinv i ∈ eIdx := by decide +kernel

theorem eIdx_norm_chk : NormBoth [0, 1, 2, 3, 5] eIdx := by decide +kernel

theorem V4_chk : ∀ ia ∈ invQIdx, ∀ ib ∈ qIdx, ib ≠ 0 → ib ≠ ia →
    (∀ i ∈ [0, ia, ib, smul ia ib], ∀ j ∈ [0, ia, ib, smul ia ib],
      smul i j ∈ [0, ia, ib, smul ia ib]) →
    NormFwd [0, 1, 2, 3, 5] [0, ia, ib, smul ia ib] →
    ia ∈ eIdx ∧ ib ∈ eIdx ∧ smul ia ib ∈ eIdx := by decide +kernel

@[expose] def q8Idx' (A X : List ℕ) : QuaternionGroup 2 → ℕ
  | .a i => A.getD i.val 0
  | .xa i => X.getD i.val 0

@[expose] def Q8Tab (A X : List ℕ) : Prop :=
  (∀ g h : QuaternionGroup 2, q8Idx' A X g < 64 ∧ q8Idx' A X h < 64 ∧
    compL (sl (q8Idx' A X g)) (sl (q8Idx' A X h)) = sl (q8Idx' A X (g * h))) ∧
  (∀ g h : QuaternionGroup 2, q8Idx' A X g = q8Idx' A X h → g = h) ∧ q8Idx' A X 1 = 0

instance (A X : List ℕ) : Decidable (Q8Tab A X) := by unfold Q8Tab; infer_instance

theorem q8a_chk : Q8Tab q8aA q8aX := by decide +kernel

theorem q8b_chk : Q8Tab q8bA q8bX := by decide +kernel

@[expose] def q8List (A X : List ℕ) : List ℕ := A ++ X

theorem q8_incl_chk : (∀ i ∈ q8List q8aA q8aX, i ∈ qIdx) ∧ (∀ i ∈ q8List q8bA q8bX, i ∈ qIdx) := by
  decide +kernel

theorem q8_comm_chk : ∀ i ∈ q8List q8aA q8aX, ∀ j ∈ q8List q8bA q8bX, smul i j = smul j i := by
  decide +kernel

theorem q8_gen_chk : ∀ i ∈ qIdx, ∃ a ∈ q8List q8aA q8aX, ∃ b ∈ q8List q8bA q8bX, smul a b = i := by
  decide +kernel

theorem q8_surj_chk : (∀ i ∈ q8List q8aA q8aX, ∃ g : QuaternionGroup 2, q8Idx' q8aA q8aX g = i) ∧
    (∀ i ∈ q8List q8bA q8bX, ∃ g : QuaternionGroup 2, q8Idx' q8bA q8bX g = i) ∧
    (∀ g : QuaternionGroup 2, q8Idx' q8aA q8aX g ∈ q8List q8aA q8aX) ∧
    (∀ g : QuaternionGroup 2, q8Idx' q8bA q8bX g ∈ q8List q8bA q8bX) := by
  decide +kernel

end CFSG.Quasithin.G2AmalE8
