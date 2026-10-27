module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Model

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native


theorem exists_zElt_of_isConj {u : D} (h : IsConj d4z u) : ∃ i : Fin 819, zElt i = u := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  obtain ⟨i, hi⟩ := exists_conj_zElt c pt0
  refine ⟨i, ?_⟩
  rw [← hi, zElt_zero, hc]

theorem memR_cz_iff {y : Array ℕ} {v : D} (hy : validR y = true) (hrep : RepE d4E y v) :
    memR cz.T cz.idx y = true ↔ IsConj d4z v := by
  constructor
  · intro hm
    obtain ⟨hlt, heq⟩ := memR_spec hm
    obtain ⟨c, hc⟩ := exists_conj_cz _ hlt
    rw [heq] at hc
    exact isConj_iff.2 ⟨c, eq_of_repE d4E_injective hc hrep⟩
  · intro hconj
    obtain ⟨i, hi⟩ := exists_zElt_of_isConj hconj
    have hi' := repE_zElt i
    rw [hi] at hi'
    have heq : cz.T[i.1]! = y := arr_eq_of_repE (validR_cz i.2) hy hi' hrep
    unfold memR
    rw [← heq, idx_cz i.2]
    simp [lt_size_cz i.2]

end CFSG.Quasithin.D4Hex
