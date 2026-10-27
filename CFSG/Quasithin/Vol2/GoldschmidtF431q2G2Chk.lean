module

public import CFSG.Quasithin.Vol2.GoldschmidtF431q2G2Tab

public section

namespace CFSG.Quasithin.H13.F431.G2Two

open CFSG.Quasithin CFSG.Quasithin.F6

namespace Tab

theorem zc_chk : ∀ j < 64, mulT 26 j = mulT j 26 := by decide +kernel

theorem zz_chk : mulT 26 26 = 0 := by decide +kernel

theorem ZS_chk : ∀ i < 64, (∀ j < 64, mulT i j = mulT j i) → i = 0 ∨ i = 26 := by
  decide +kernel

theorem R2_comm_chk : ∀ i ∈ g22R2Idx, ∀ j ∈ g22R2Idx, commT i j = 0 ∨ commT i j = 26 := by
  decide +kernel

theorem R2_Z_chk : ∀ i ∈ g22R2Idx, (∀ j ∈ g22R2Idx, mulT i j = mulT j i) → i = 0 ∨ i = 26 := by
  decide +kernel

theorem R2_nonab_chk : ∃ i ∈ g22R2Idx, ∃ j ∈ g22R2Idx, mulT i j ≠ mulT j i := by decide +kernel

theorem inv_chk : ∀ i < 32, mulT i i = 0 → i ≠ 0 →
    i = 5 ∨ i = 8 ∨ i = 12 ∨ i = 21 ∨ i = 24 ∨ i = 26 ∨ i = 31 := by decide +kernel

theorem out_ex_chk : ∃ i ∈ g22R2Idx, 32 ≤ i ∧ mulT i i = 0 := by decide +kernel

theorem out_pair_chk : ∀ i ∈ g22R2Idx, 32 ≤ i → mulT i i = 0 →
    ∃ a ∈ g22R2Idx, ∃ b ∈ g22R2Idx, mulT a i = mulT i a ∧ mulT b i = mulT i b ∧
      commT a b = 26 := by decide +kernel

theorem out_t_chk : ∀ i ∈ g22R2Idx, 32 ≤ i → mulT i i = 0 →
    commT 1 i ≠ 0 ∧ commT 1 i ≠ 26 := by decide +kernel

theorem commT_lt : ∀ i < 64, ∀ j < 64, commT i j < 64 := by decide +kernel

theorem Tp_mul_chk : ∀ i < 32, ∀ j < 32, mulT i j < 32 := by decide +kernel

theorem Tp_inv_chk : ∀ i < 32, invT i < 32 := by decide +kernel

theorem range32_lt : ∀ i ∈ List.range 32, i < 64 := by decide +kernel

theorem Tp_mul : ∀ i ∈ List.range 32, ∀ j ∈ List.range 32,
    ∃ l ∈ List.range 32, compL (u33XL i) (u33XL j) = u33XL l := by
  intro i hi j hj
  rw [List.mem_range] at hi hj
  exact ⟨mulT i j, List.mem_range.2 (Tp_mul_chk i hi j hj), (mulT_spec i (by omega) j (by omega)).2⟩

theorem Tp_inv : ∀ i ∈ List.range 32, ∃ l ∈ List.range 32,
    compL (u33XL i) (u33XL l) = g22id := by
  intro i hi
  rw [List.mem_range] at hi
  exact ⟨invT i, List.mem_range.2 (Tp_inv_chk i hi), (invT_spec i (by omega)).2⟩

@[expose] def R2TpIdx : List ℕ := [0, 5, 6, 7, 8, 9, 11, 12, 18, 20, 21, 23, 24, 25, 26, 31]

theorem R2Tp_lt : ∀ i ∈ R2TpIdx, i < 64 := by decide +kernel

theorem R2Tp_mul : ∀ i ∈ R2TpIdx, ∀ j ∈ R2TpIdx, ∃ k ∈ R2TpIdx,
    compL (u33XL i) (u33XL j) = u33XL k := by decide +kernel

theorem R2Tp_inv : ∀ i ∈ R2TpIdx, ∃ k ∈ R2TpIdx, compL (u33XL i) (u33XL k) = g22id := by
  decide +kernel

theorem R2Tp_norm : ∀ j ∈ R2TpIdx, g22ConjIn [0, 1, 2, 4] R2TpIdx j = true := by decide +kernel

theorem R2Tp_of_lt : ∀ i ∈ g22R2Idx, i < 32 → i ∈ R2TpIdx := by decide +kernel

theorem R2Tp_mem : ∀ i ∈ R2TpIdx, i ∈ g22R2Idx ∧ i < 32 := by decide +kernel

theorem conjS_chk : mulT (mulT 1 21) (invT 1) = 5 ∧ mulT (mulT 2 24) (invT 2) = 5 ∧
    mulT (mulT 7 31) (invT 7) = 5 ∧ mulT (mulT 5 12) (invT 5) = 8 := by decide +kernel

theorem conjY_chk : compL (compL (g22gl 4) (u33XL 5)) (g22gil 4) = u33XL 8 := by decide +kernel

theorem conjX_chk : compL (compL (g22gl 3) (u33XL 8)) (g22gil 3) = u33XL 26 := by decide +kernel

end Tab

end CFSG.Quasithin.H13.F431.G2Two
