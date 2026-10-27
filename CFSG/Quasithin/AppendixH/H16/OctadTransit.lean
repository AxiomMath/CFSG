module

public import CFSG.Quasithin.AppendixH.H16.OctadGroup

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24
  CFSG.Monster.Code CFSG.ASVolI.AppH

@[expose] def trTab : Array (Array ℕ) := #[
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
  #[1, 2, 3, 0, 5, 4, 6, 7, 9, 11, 8, 10, 16, 18, 17, 19, 13, 15, 12, 14, 20, 22, 21, 23],
  #[5, 7, 6, 4, 1, 0, 3, 2, 9, 10, 8, 11, 16, 19, 17, 18, 13, 14, 12, 15, 20, 23, 21, 22],
  #[0, 5, 4, 1, 2, 3, 7, 6, 9, 13, 8, 12, 16, 20, 17, 21, 11, 15, 10, 14, 18, 22, 19, 23],
  #[2, 6, 7, 3, 0, 1, 4, 5, 9, 12, 8, 13, 16, 21, 17, 20, 11, 14, 10, 15, 18, 23, 19, 22],
  #[3, 4, 5, 2, 1, 0, 6, 7, 9, 15, 8, 14, 16, 22, 17, 23, 11, 13, 10, 12, 18, 20, 19, 21],
  #[1, 7, 6, 0, 3, 2, 5, 4, 9, 14, 8, 15, 16, 23, 17, 22, 11, 12, 10, 13, 18, 21, 19, 20],
  #[4, 2, 0, 7, 5, 6, 1, 3, 9, 17, 8, 16, 12, 20, 13, 21, 11, 19, 10, 18, 14, 22, 15, 23],
  #[5, 3, 1, 6, 4, 7, 0, 2, 9, 16, 8, 17, 12, 21, 13, 20, 11, 18, 10, 19, 14, 23, 15, 22],
  #[6, 0, 2, 5, 7, 4, 3, 1, 9, 19, 8, 18, 12, 22, 13, 23, 11, 17, 10, 16, 14, 20, 15, 21],
  #[7, 1, 3, 4, 6, 5, 2, 0, 9, 18, 8, 19, 12, 23, 13, 22, 11, 16, 10, 17, 14, 21, 15, 20],
  #[0, 6, 4, 3, 1, 2, 5, 7, 9, 21, 8, 20, 12, 16, 13, 17, 11, 23, 10, 22, 14, 18, 15, 19],
  #[1, 7, 5, 2, 0, 3, 4, 6, 9, 20, 8, 21, 12, 17, 13, 16, 11, 22, 10, 23, 14, 19, 15, 18],
  #[2, 4, 6, 1, 3, 0, 7, 5, 9, 23, 8, 22, 12, 18, 13, 19, 11, 21, 10, 20, 14, 16, 15, 17],
  #[3, 5, 7, 0, 2, 1, 6, 4, 9, 22, 8, 23, 12, 19, 13, 18, 11, 20, 10, 21, 14, 17, 15, 16]
]

@[expose] def trInvTab : Array (Array ℕ) := #[
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
  #[3, 0, 1, 2, 5, 4, 6, 7, 10, 8, 11, 9, 18, 16, 19, 17, 12, 14, 13, 15, 20, 22, 21, 23],
  #[5, 4, 7, 6, 3, 0, 2, 1, 10, 8, 9, 11, 18, 16, 17, 19, 12, 14, 15, 13, 20, 22, 23, 21],
  #[0, 3, 4, 5, 2, 1, 7, 6, 10, 8, 18, 16, 11, 9, 19, 17, 12, 14, 20, 22, 13, 15, 21, 23],
  #[4, 5, 0, 3, 6, 7, 1, 2, 10, 8, 18, 16, 9, 11, 17, 19, 12, 14, 20, 22, 15, 13, 23, 21],
  #[5, 4, 3, 0, 1, 2, 6, 7, 10, 8, 18, 16, 19, 17, 11, 9, 12, 14, 20, 22, 21, 23, 13, 15],
  #[3, 0, 5, 4, 7, 6, 2, 1, 10, 8, 18, 16, 17, 19, 9, 11, 12, 14, 20, 22, 23, 21, 15, 13],
  #[2, 6, 1, 7, 0, 4, 5, 3, 10, 8, 18, 16, 12, 14, 20, 22, 11, 9, 19, 17, 13, 15, 21, 23],
  #[6, 2, 7, 1, 4, 0, 3, 5, 10, 8, 18, 16, 12, 14, 20, 22, 9, 11, 17, 19, 15, 13, 23, 21],
  #[1, 7, 2, 6, 5, 3, 0, 4, 10, 8, 18, 16, 12, 14, 20, 22, 19, 17, 11, 9, 21, 23, 13, 15],
  #[7, 1, 6, 2, 3, 5, 4, 0, 10, 8, 18, 16, 12, 14, 20, 22, 17, 19, 9, 11, 23, 21, 15, 13],
  #[0, 4, 5, 3, 2, 6, 1, 7, 10, 8, 18, 16, 12, 14, 20, 22, 13, 15, 21, 23, 11, 9, 19, 17],
  #[4, 0, 3, 5, 6, 2, 7, 1, 10, 8, 18, 16, 12, 14, 20, 22, 15, 13, 23, 21, 9, 11, 17, 19],
  #[5, 3, 0, 4, 1, 7, 2, 6, 10, 8, 18, 16, 12, 14, 20, 22, 21, 23, 13, 15, 19, 17, 11, 9],
  #[3, 5, 4, 0, 7, 1, 6, 2, 10, 8, 18, 16, 12, 14, 20, 22, 23, 21, 15, 13, 17, 19, 9, 11]
]

theorem tr_ok : ∀ t < 16, InvPairOK 24 (trTab[t]!) (trInvTab[t]!) = true := by decide +kernel

theorem tr_aut : ∀ t < 16, autArrOK (trTab[t]!) (trInvTab[t]!) = true := by decide +kernel

theorem tr_stab : ∀ t < 16, ∀ j < 24, (j < 8 ↔ (trTab[t]!)[j]! < 8) := by decide +kernel

theorem tr_conj : ∀ t < 16, 1 ≤ t →
    cArr (cArr (trTab[t]!) (koArr 1)) (trInvTab[t]!) = koArr t := by decide +kernel

theorem exists_octStab_conj_koPerm (t : Fin 16) (ht : t ≠ 0) :
    ∃ m ∈ octStab octad0, m * koPerm 1 * m⁻¹ = koPerm t := by
  have htv : (t : ℕ) ≠ 0 := fun h => ht (Fin.ext h)
  have ht1 : 1 ≤ (t : ℕ) := Nat.pos_iff_ne_zero.2 htv
  let a := trTab[(t : ℕ)]!
  let b := trInvTab[(t : ℕ)]!
  have hok : InvPairOK 24 a b = true := tr_ok (t : ℕ) t.2
  let m : Equiv.Perm (Fin 24) := permOfArr 24 a b hok
  have hma : HasArr m a := hasArr_permOfArr hok
  have hmb : HasArr m⁻¹ b := hasArr_permOfArr_inv hok
  have hconj : cArr (cArr a (koArr 1)) b = koArr t := tr_conj (t : ℕ) t.2 ht1
  refine ⟨m, mem_octStab_iff.2 ⟨?_, ?_⟩, ?_⟩
  · show m ∈ M24g
    exact mem_AutPerm_of_arr hok (tr_aut (t : ℕ) t.2)
  · exact smul_octad0_eq_of_arr hma (tr_stab (t : ℕ) t.2)
  · refine perm_eq_of_hasArr (a := koArr t) ?_ (hasArr_permOfArr (koArr_ok t).1)
    rw [← hconj]
    exact hasArr_mul (hasArr_mul hma (hasArr_permOfArr (koArr_ok 1).1)) hmb

end CFSG.ASVolI.H16
