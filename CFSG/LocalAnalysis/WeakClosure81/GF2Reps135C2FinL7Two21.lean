module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinLinear

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
open CFSG.LieType.SpecialLinear.ExteriorModel

theorem lt_orbitSize_of_symmetric_seven (S : Finset (Fin 7)) (h0 : (⟨0, by omega⟩ : Fin 7) ∉ S)
    (hS : S ≠ ∅)
    (hsym : ∀ (j : Fin 7) (hj : 1 ≤ j.val), (j ∈ S ↔ (⟨7 - j.val, by omega⟩ : Fin 7) ∈ S)) :
    21 < orbitSize S := by
  classical
  obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hS
  have hj0 : j ≠ (⟨0, by omega⟩ : Fin 7) := by
    intro h
    exact h0 (h ▸ hj)
  have hj0val : (j : ℕ) ≠ 0 := by
    intro h
    exact hj0 (Fin.ext (by simpa using h))
  have hj1 : 1 ≤ (j : ℕ) := by
    have := j.isLt
    omega
  have hkj : (⟨7 - (j : ℕ), by omega⟩ : Fin 7) ∈ S := (hsym j hj1).mp hj
  have hne : j ≠ (⟨7 - (j : ℕ), by omega⟩ : Fin 7) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_mk] at hv
    omega
  have h2 : 2 ≤ S.card := by
    have h := Finset.one_lt_card.mpr ⟨j, hj, _, hkj, hne⟩
    omega
  rw [orbitSize, card_rearr_topWt]
  have hb : ∀ i, 0 < blocks S i :=
    fun i => blocks_pos (by norm_num : 0 < 7) (by simpa using h0) i
  have hsum := sum_blocks S
  have hl : 3 ≤ S.card + 1 := by omega
  have hN := multinomial_lower (b := blocks S) hb hsum hl
  omega

theorem finL7Two21_holds :
    FinL7Two21 :=
  finRowStmt_psl_of_orbit_bound 7 21 (by norm_num) (by norm_num) lt_orbitSize_of_symmetric_seven

end CFSG.LocalAnalysis.WeakClosure81
