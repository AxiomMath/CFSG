module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinLinear

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
open CFSG.LieType.SpecialLinear.ExteriorModel

theorem lt_orbitSize_of_symmetric_eight (S : Finset (Fin 8)) (h0 : (⟨0, by omega⟩ : Fin 8) ∉ S)
    (hS : S ≠ ∅)
    (hsym : ∀ (j : Fin 8) (hj : 1 ≤ j.val), (j ∈ S ↔ (⟨8 - j.val, by omega⟩ : Fin 8) ∈ S)) :
    28 < orbitSize S := by
  classical
  have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
  rcases lt_or_ge S.card 2 with hlt | hge
  · have hcard : S.card = 1 := by omega
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hcard
    have hj0 : (j : ℕ) ≠ 0 := by
      intro h
      exact h0 (by rw [Finset.mem_singleton]; exact Fin.ext h.symm)
    have hj1 : 1 ≤ (j : ℕ) := Nat.one_le_iff_ne_zero.mpr hj0
    have hrep : (⟨8 - (j : ℕ), by omega⟩ : Fin 8) = j := by
      have hmem : (⟨8 - (j : ℕ), by omega⟩ : Fin 8) ∈ ({j} : Finset (Fin 8)) :=
        (hsym j hj1).mp (by rw [Finset.mem_singleton])
      simpa using hmem
    have hjval : (j : ℕ) = 4 := by
      have hv := congrArg Fin.val hrep
      simp only [Fin.val_mk] at hv
      omega
    have hjeq : j = (⟨4, by omega⟩ : Fin 8) := Fin.ext (by simpa using hjval)
    rw [hjeq, orbitSize_singleton]
    show 28 < Nat.choose 8 4
    decide
  · rw [orbitSize, card_rearr_topWt]
    have hb : ∀ i, 0 < blocks S i := fun i => blocks_pos (by norm_num) (by simpa using h0) i
    have hsum := sum_blocks S
    have hl : 3 ≤ S.card + 1 := by omega
    have hN := multinomial_lower (b := blocks S) hb hsum (m := 8) hl
    omega

theorem finRowStmt_psl_eight_twentyeight :
    FinRowStmt .PSL 8 1 28 :=
  finRowStmt_psl_of_orbit_bound 8 28 (by norm_num) (by norm_num) lt_orbitSize_of_symmetric_eight

end CFSG.LocalAnalysis.WeakClosure81
