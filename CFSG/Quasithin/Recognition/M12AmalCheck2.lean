module

public import CFSG.Open.LocalVocabulary
public import CFSG.Quasithin.Recognition.CertPermList
public import CFSG.Quasithin.Recognition.M12AmalData
public import CFSG.Sporadic.Bridge.Common

public section

namespace CFSG.Quasithin.M12Amal

open CFSG.Sporadic.Bridge Equiv

@[expose] def tl (i : ℕ) : List ℕ := telTab.getD i []

@[expose] def gl (k : ℕ) : List ℕ := genTab.getD k []

@[expose] def gil (k : ℕ) : List ℕ := genInvTab.getD k []

@[expose] def idl : List ℕ := List.range 12

theorem tl_inj_chk : ∀ i < 64, ∀ j < 64, tl i = tl j → i = j := by decide +kernel

theorem tl_mem_chk : ∀ i < 64, tl i ∈ telTab := by decide +kernel

theorem hg_chk : ∀ i' < 64, ∀ i < 64,
    compL (compL (dTab.getD 17 []) (tl i')) (dInvTab.getD 17 []) = tl i → tl i = idl := by
  decide +kernel

theorem a_ne_one_chk : gl 0 ≠ idl := by decide +kernel

theorem x_ne_one_chk : gl 3 ≠ idl := by decide +kernel

theorem y_ne_one_chk : gl 4 ≠ idl := by decide +kernel

theorem xN_chk : ∀ i' < 64, compL (compL (gl 3) (tl 2)) (gil 3) ≠ tl i' := by decide +kernel

theorem yN_chk : ∀ i' < 64, compL (compL (gl 4) (tl 1)) (gil 4) ≠ tl i' := by decide +kernel

theorem z_ne_one_chk : tl 4 ≠ idl := by decide +kernel

theorem z_comm_chk : ∀ k < 4, compL (gl k) (tl 4) = compL (tl 4) (gl k) := by decide +kernel

theorem u8_ne_one_chk : tl 8 ≠ idl := by decide +kernel

theorem z_ne_u8_chk : tl 4 ≠ tl 8 := by decide +kernel

theorem U_norm_chk : ∀ k ∈ [0, 1, 2, 4], ∀ j ∈ [4, 8, 29],
    compL (compL (gl k) (tl j)) (gil k) ∈ [tl 4, tl 8, tl 29] ∧
      compL (compL (gil k) (tl j)) (gl k) ∈ [tl 4, tl 8, tl 29] := by decide +kernel

@[expose] def LAp (i : ℕ) : Prop :=
  compL (compL (gl 3) (tl i)) (gil 3) ∈ telTab ∧ compL (compL (gil 3) (tl i)) (gl 3) ∈ telTab

instance (i : ℕ) : Decidable (LAp i) := by unfold LAp; infer_instance

@[expose] def LBp (i : ℕ) : Prop :=
  compL (compL (gl 4) (tl i)) (gil 4) ∈ telTab ∧ compL (compL (gil 4) (tl i)) (gl 4) ∈ telTab

instance (i : ℕ) : Decidable (LBp i) := by unfold LBp; infer_instance

@[expose] def ACentralOK (i j : ℕ) : Prop := LAp i → LAp j →
    compL (tl i) (gl 3) = compL (gl 3) (tl i) → compL (tl i) (tl j) = compL (tl j) (tl i)

instance (i j : ℕ) : Decidable (ACentralOK i j) := by unfold ACentralOK; infer_instance

theorem A_central_chk : ∀ i < 64, ∀ j < 64, ACentralOK i j := by decide +kernel

theorem B_central_chk : ∀ i < 64, LBp i →
    compL (tl 4) (tl i) = compL (tl i) (tl 4) ∧ compL (tl 8) (tl i) = compL (tl i) (tl 8) := by
  decide +kernel

@[expose] def KIdx : List ℕ := [0, 1, 4, 12, 57, 59, 62, 63]

theorem K_mul_chk : ∀ i ∈ KIdx, ∀ j ∈ KIdx, ∃ k ∈ KIdx, compL (tl i) (tl j) = tl k := by
  decide +kernel

theorem K_inv_chk : ∀ i ∈ KIdx, ∃ k ∈ KIdx, compL (tl i) (tl k) = idl := by decide +kernel

theorem K_norm_chk : ∀ g ∈ [0, 1, 2, 3], ∀ i ∈ KIdx,
    (∃ k ∈ KIdx, compL (compL (gl g) (tl i)) (gil g) = tl k) ∧
      (∃ k ∈ KIdx, compL (compL (gil g) (tl i)) (gl g) = tl k) := by decide +kernel

theorem K_lt_chk : ∀ i ∈ KIdx, i < 64 := by decide +kernel

@[expose] def q8Idx : QuaternionGroup 2 → ℕ
  | .a i => [0, 1, 4, 12].getD i.val 0
  | .xa i => [63, 59, 62, 57].getD i.val 0

theorem q8_mul_chk : ∀ g h : QuaternionGroup 2,
    compL (tl (q8Idx g)) (tl (q8Idx h)) = tl (q8Idx (g * h)) := by decide +kernel

theorem q8_inj_chk : ∀ g h : QuaternionGroup 2, q8Idx g = q8Idx h → g = h := by decide +kernel

theorem q8_mem_chk : ∀ g : QuaternionGroup 2, q8Idx g ∈ KIdx := by decide +kernel

theorem q8_surj_chk : ∀ i ∈ KIdx, ∃ g : QuaternionGroup 2, q8Idx g = i := by decide +kernel

theorem q8_one_chk : q8Idx 1 = 0 := by decide +kernel

end CFSG.Quasithin.M12Amal
