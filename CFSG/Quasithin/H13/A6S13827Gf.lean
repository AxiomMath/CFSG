module

public import CFSG.Quasithin.Background.SmithB42U33GenData

public section

namespace CFSG.Quasithin.H13.A6.A6G2

open CFSG.Quasithin.H13.Orbit CFSG.Quasithin.B42U33

@[expose] def tW1 : List ℕ := [2, 3, 0, 1, 0]

@[expose] def tW2 : List ℕ := [0, 1, 0, 1, 2, 3, 2]

@[expose] def pow4 (w : List ℕ) : List ℕ := w ++ w ++ w ++ w

@[expose] def sFind (m : List ℕ) : ℕ := ((List.range 64).find? fun k => sM k == m).getD 64

theorem sFind_sM : ∀ k < 64, sFind (sM k) = k := by
  decide +kernel

theorem fix_eight : (∀ i < 64, mact (sM i) 8 = 8) ∧ mact (wordC tW1) 8 = 8 ∧
    mact (wordC tW2) 8 = 8 ∧ mact (wordC [0, 1, 0]) 2 = 8 := by
  decide +kernel

theorem no_inv_fixed : ∀ i ∈ sInv,
    ¬ (conjC (pow4 tW1) (sM i) = sM i ∧ conjC (pow4 tW2) (sM i) = sM i) := by
  decide +kernel

theorem e4_normalized : ∀ i ∈ sInv, ∀ j ∈ sInv, i ≠ j →
    mmul (sM i) (sM j) = mmul (sM j) (sM i) →
    (∀ e ∈ [i, j, sFind (mmul (sM i) (sM j))], ∀ w ∈ [tW1, tW2],
      conjC (pow4 w) (sM e) ∈ [sM i, sM j, sM (sFind (mmul (sM i) (sM j)))]) →
    i ∈ [2, 4, 6] ∧ j ∈ [2, 4, 6] := by
  decide +kernel

theorem z0_third : ∀ i ∈ [2, 4, 6], ∀ j ∈ [2, 4, 6], i ≠ j →
    sFind (mmul (sM i) (sM j)) ∈ [2, 4, 6] ∧ sFind (mmul (sM i) (sM j)) ≠ i ∧
      sFind (mmul (sM i) (sM j)) ≠ j := by
  decide +kernel

theorem comm_witness : mact (sM 6) 2 ^^^ 2 = 8 ∧ mact (sM 6) 64 ^^^ 64 = 48 ∧
    mact (sM 4) 64 ^^^ 64 = 32 ∧
    ∀ a ∈ [0, 8], ∀ b ∈ [0, 48], ∀ c ∈ [0, 32], ∀ a' ∈ [0, 8], ∀ b' ∈ [0, 48], ∀ c' ∈ [0, 32],
      (a ^^^ b ^^^ c = a' ^^^ b' ^^^ c' ∨ a ^^^ b ^^^ c = a' ^^^ b' ^^^ c' ^^^ 129) →
        a = a' ∧ b = b' ∧ c = c' := by
  decide +kernel

end CFSG.Quasithin.H13.A6.A6G2
