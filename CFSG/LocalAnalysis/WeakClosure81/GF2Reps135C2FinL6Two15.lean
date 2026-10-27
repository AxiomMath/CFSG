module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinLinear

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

theorem lt_orbitSize_of_symmetric_six (S : Finset (Fin 6)) (h0 : (⟨0, by omega⟩ : Fin 6) ∉ S)
    (hS : S ≠ ∅)
    (hsym : ∀ (j : Fin 6) (hj : 1 ≤ j.val), (j ∈ S ↔ (⟨6 - j.val, by omega⟩ : Fin 6) ∈ S)) :
    15 < orbitSize S := by
  classical
  have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
  rcases lt_or_ge S.card 2 with hlt | hge
  · have hcard : S.card = 1 := by omega
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hcard
    have hj0 : (j : ℕ) ≠ 0 := by
      intro h
      exact h0 (by rw [Finset.mem_singleton]; exact Fin.ext h.symm)
    have hj1 : 1 ≤ (j : ℕ) := Nat.one_le_iff_ne_zero.mpr hj0
    have hrep : (⟨6 - (j : ℕ), by omega⟩ : Fin 6) = j := by
      have hmem : (⟨6 - (j : ℕ), by omega⟩ : Fin 6) ∈ ({j} : Finset (Fin 6)) :=
        (hsym j hj1).mp (by rw [Finset.mem_singleton])
      simpa using hmem
    have hjval : (j : ℕ) = 3 := by
      have hv := congrArg Fin.val hrep
      simp only [Fin.val_mk] at hv
      omega
    have hjeq : j = (⟨3, by omega⟩ : Fin 6) := Fin.ext (by simpa using hjval)
    rw [hjeq, orbitSize_singleton]
    show 15 < Nat.choose 6 3
    decide
  · rw [orbitSize, CFSG.LieType.SpecialLinear.ExteriorModel.card_rearr_topWt]
    have hb : ∀ i, 0 < CFSG.LieType.SpecialLinear.ExteriorModel.blocks S i :=
      fun i =>
        CFSG.LieType.SpecialLinear.ExteriorModel.blocks_pos (n := 6) (S := S)
          (by norm_num) (by simpa using h0) i
    have hsum := CFSG.LieType.SpecialLinear.ExteriorModel.sum_blocks S
    have hl : 3 ≤ S.card + 1 := by omega
    have hN := multinomial_lower
      (b := CFSG.LieType.SpecialLinear.ExteriorModel.blocks S) hb hsum (m := 6) hl
    omega

theorem finL6Two15_holds :
    FinL6Two15 :=
  finRowStmt_psl_of_orbit_bound 6 15 (by norm_num) (by norm_num) lt_orbitSize_of_symmetric_six

end CFSG.LocalAnalysis.WeakClosure81
