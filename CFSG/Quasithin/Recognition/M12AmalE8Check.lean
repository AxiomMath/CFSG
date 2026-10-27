module

public import CFSG.Quasithin.Recognition.M12AmalE8Data
public import CFSG.Quasithin.Recognition.M12AmalCheck2

public section

namespace CFSG.Quasithin.M12AmalE8

open CFSG.Sporadic.Bridge Equiv CFSG.Quasithin.M12Amal

@[expose] def tmul (i j : ℕ) : ℕ := (mulTab.getD i []).getD j 0

@[expose] def tinv (i : ℕ) : ℕ := invTab.getD i 0

@[expose] def MulRowOK (i : ℕ) : Prop :=
  ∀ j < 64, tmul i j < 64 ∧ compL (tl i) (tl j) = tl (tmul i j)

instance (i : ℕ) : Decidable (MulRowOK i) := by unfold MulRowOK; infer_instance

theorem tmul_c0 : ∀ i, 0 ≤ i → i < 32 → MulRowOK i := by decide +kernel

theorem tmul_c1 : ∀ i, 32 ≤ i → i < 64 → MulRowOK i := by decide +kernel

theorem tmul_chk (i : ℕ) (hi : i < 64) : MulRowOK i := by
  by_cases h : i < 32
  · exact tmul_c0 i (by omega) h
  · exact tmul_c1 i (by omega) hi

theorem tinv_chk : ∀ i < 64, tinv i < 64 ∧ compL (tl i) (tl (tinv i)) = idl := by decide +kernel

@[expose] def NormFwd (gs : List ℕ) (L : List ℕ) : Prop :=
  ∀ k ∈ gs, ∀ j ∈ L, ∃ i' ∈ L, compL (compL (gl k) (tl j)) (gil k) = tl i'

instance (gs L : List ℕ) : Decidable (NormFwd gs L) := by unfold NormFwd; infer_instance

@[expose] def NormBoth (gs : List ℕ) (L : List ℕ) : Prop :=
  ∀ k ∈ gs, ∀ j ∈ L,
    (∃ i' ∈ L, compL (compL (gl k) (tl j)) (gil k) = tl i') ∧
      (∃ i' ∈ L, compL (compL (gil k) (tl j)) (gl k) = tl i')

instance (gs L : List ℕ) : Decidable (NormBoth gs L) := by unfold NormBoth; infer_instance

theorem laIdx_chk : laIdx.length = 32 ∧ laIdx.Nodup ∧ (∀ i ∈ laIdx, i < 64) ∧ 0 ∈ laIdx ∧
    (∀ i ∈ laIdx, ∀ j ∈ laIdx, tmul i j ∈ laIdx) := by decide +kernel

theorem laIdx_inv_chk : ∀ i ∈ laIdx, tinv i ∈ laIdx := by decide +kernel

theorem laIdx_iff_chk : ∀ i < 64, LAp i ↔ i ∈ laIdx := by decide +kernel

theorem laIdx_norm_chk : NormBoth [0, 1, 2, 3] laIdx := by decide +kernel

theorem invPIdx_chk : (∀ i ∈ invPIdx, i ∈ laIdx ∧ i ≠ 0 ∧ tmul i i = 0) ∧
    ∀ i ∈ laIdx, i ≠ 0 → tmul i i = 0 → i ∈ invPIdx := by decide +kernel

theorem erIdx_chk : erIdx.length = 8 ∧ erIdx.Nodup ∧ (∀ i ∈ erIdx, i ∈ laIdx) ∧ 0 ∈ erIdx ∧
    ∀ i ∈ erIdx, ∀ j ∈ erIdx, tmul i j ∈ erIdx ∧ tmul i j = tmul j i ∧ tmul i i = 0 := by
  decide +kernel

theorem erIdx_inv_chk : ∀ i ∈ erIdx, tinv i ∈ erIdx := by decide +kernel

theorem erIdx_norm_chk : NormBoth [0, 1, 2, 4] erIdx := by decide +kernel

theorem V4_chk : ∀ ia ∈ invPIdx, ∀ ib ∈ laIdx, ib ≠ 0 → ib ≠ ia →
    (∀ i ∈ [0, ia, ib, tmul ia ib], ∀ j ∈ [0, ia, ib, tmul ia ib],
      tmul i j ∈ [0, ia, ib, tmul ia ib]) →
    NormFwd [0, 1, 2, 4] [0, ia, ib, tmul ia ib] →
    ia ∈ erIdx ∧ ib ∈ erIdx ∧ tmul ia ib ∈ erIdx := by decide +kernel

end CFSG.Quasithin.M12AmalE8
