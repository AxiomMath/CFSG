module

public import CFSG.Quasithin.AppendixH.H16.OctadBetaMask

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24
  CFSG.Monster.Code CFSG.ASVolI.AppH CFSG.Quasithin.H156

@[expose] def wz0Basis : List ℕ := [3, 5, 9, 17, 160, 352, 512]

@[expose] def vz0Basis : List ℕ := [3, 12, 20, 512]

@[expose] def z8Basis : List ℕ := 1024 :: wz0Basis

theorem wz0Basis_lt : ∀ a ∈ wz0Basis, a < 2 ^ 11 := by decide

theorem vz0Basis_lt : ∀ a ∈ vz0Basis, a < 2 ^ 11 := by decide

theorem z8Basis_lt : ∀ a ∈ z8Basis, a < 2 ^ 11 := by decide

theorem vz0_nodup : (combos vz0Basis).Nodup := by decide

theorem z8_nodup : (combos z8Basis).Nodup := by decide +kernel

theorem fix_koOne_iff : ∀ m < 2 ^ 11, (actC11 (koArr 1) m = m ↔ m ∈ combos wz0Basis) := by
  decide +kernel

theorem oct5_inf_wz0 :
    ∀ m < 2 ^ 11, ((m ∈ combos oct5Basis ∧ m ∈ combos wz0Basis) ↔ m ∈ combos vz0Basis) := by
  decide +kernel

theorem oct5_split_vz : ∀ m ∈ combos oct5Basis, m ∈ combos vz0Basis ∨ (m ^^^ 1024) ∈ combos vz0Basis := by
  decide +kernel

theorem not_mem_vz_1024 : 1024 ∉ combos vz0Basis := by decide

theorem oct5_sub_z8 : ∀ m ∈ combos oct5Basis, m ∈ combos z8Basis := by decide +kernel

theorem wz0_sub_z8 : ∀ m ∈ combos wz0Basis, m ∈ combos z8Basis := by decide +kernel

theorem z8_sub_sum : ∀ m ∈ combos z8Basis, ∃ a ∈ combos wz0Basis, ∃ b ∈ combos oct5Basis, m = a ^^^ b := by
  decide +kernel

theorem octQmask_z8 : ∀ m ∈ combos z8Basis, octQmask (actM liftCCols m) = 0 := by decide +kernel

@[expose] def dTab : Array (Array ℕ) := #[
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
  #[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22],
  #[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15, 17, 16, 19, 18, 21, 20, 23, 22],
  #[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 16, 17, 18, 19, 20, 21, 22, 23],
  #[2, 3, 0, 1, 7, 6, 5, 4, 8, 9, 10, 11, 13, 12, 15, 14, 16, 17, 18, 19, 21, 20, 23, 22],
  #[2, 3, 0, 1, 7, 6, 5, 4, 9, 8, 11, 10, 12, 13, 14, 15, 17, 16, 19, 18, 20, 21, 22, 23],
  #[3, 2, 1, 0, 6, 7, 4, 5, 8, 9, 10, 11, 13, 12, 15, 14, 17, 16, 19, 18, 20, 21, 22, 23],
  #[3, 2, 1, 0, 6, 7, 4, 5, 9, 8, 11, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 20, 23, 22],
  #[4, 5, 7, 6, 0, 1, 3, 2, 8, 9, 11, 10, 12, 13, 15, 14, 16, 17, 19, 18, 20, 21, 23, 22],
  #[4, 5, 7, 6, 0, 1, 3, 2, 9, 8, 10, 11, 13, 12, 14, 15, 17, 16, 18, 19, 21, 20, 22, 23],
  #[5, 4, 6, 7, 1, 0, 2, 3, 8, 9, 11, 10, 12, 13, 15, 14, 17, 16, 18, 19, 21, 20, 22, 23],
  #[5, 4, 6, 7, 1, 0, 2, 3, 9, 8, 10, 11, 13, 12, 14, 15, 16, 17, 19, 18, 20, 21, 23, 22],
  #[7, 6, 4, 5, 2, 3, 1, 0, 8, 9, 11, 10, 13, 12, 14, 15, 16, 17, 19, 18, 21, 20, 22, 23],
  #[7, 6, 4, 5, 2, 3, 1, 0, 9, 8, 10, 11, 12, 13, 15, 14, 17, 16, 18, 19, 20, 21, 23, 22],
  #[6, 7, 5, 4, 3, 2, 0, 1, 8, 9, 11, 10, 13, 12, 14, 15, 17, 16, 18, 19, 20, 21, 23, 22],
  #[6, 7, 5, 4, 3, 2, 0, 1, 9, 8, 10, 11, 12, 13, 15, 14, 16, 17, 19, 18, 21, 20, 22, 23]
]

@[expose] def dArr (u : ℕ) : Array ℕ := dTab.getD u idArr

@[expose] def dColsTab : Array (List ℕ) := #[
  [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024],
  [514, 513, 519, 523, 531, 47, 87, 143, 280, 512, 1027],
  [173, 174, 168, 164, 188, 47, 94, 143, 274, 512, 1039],
  [686, 685, 683, 679, 703, 32, 73, 128, 266, 512, 1036],
  [469, 470, 464, 476, 452, 62, 87, 157, 266, 512, 1047],
  [982, 981, 979, 991, 967, 49, 64, 146, 274, 512, 1044],
  [378, 377, 383, 371, 363, 49, 73, 146, 280, 512, 1048],
  [889, 890, 892, 880, 872, 62, 94, 157, 256, 512, 1051],
  [2, 1, 4, 8, 16, 128, 384, 32, 96, 512, 1536],
  [513, 514, 519, 523, 531, 143, 407, 47, 120, 512, 1539],
  [174, 173, 168, 164, 188, 143, 413, 47, 113, 512, 1551],
  [685, 686, 683, 679, 703, 128, 394, 32, 105, 512, 1548],
  [470, 469, 464, 476, 452, 157, 407, 62, 105, 512, 1559],
  [981, 982, 979, 991, 967, 146, 384, 49, 113, 512, 1556],
  [377, 378, 383, 371, 363, 146, 394, 49, 120, 512, 1560],
  [890, 889, 892, 880, 872, 157, 413, 62, 96, 512, 1563]
]

@[expose] def dCols (u : ℕ) : List ℕ := dColsTab.getD u []

theorem dArr_ok : ∀ u < 16, InvPairOK 24 (dArr u) (dArr u) = true := by decide +kernel

theorem dArr_aut : ∀ u < 16, autArrOK (dArr u) (dArr u) = true := by decide +kernel

theorem dCols_eq : ∀ u < 16, matOf 11 (actC11 (dArr u)) = dCols u := by decide +kernel

theorem dArr_fix_vz : ∀ u < 16, ∀ m ∈ combos vz0Basis, actC11 (dArr u) m = m := by decide +kernel

theorem dArr_fix_octad_iff : ∀ u < 16, ((∀ i < 8, (dArr u)[i]! = i) ↔ u < 2) := by decide +kernel

theorem dArr_triv_wz : ∀ u < 16, (∀ m ∈ combos wz0Basis, actC11 (dArr u) m = m) → u < 2 := by
  decide +kernel

theorem dArr_triv_wz_mod : ∀ u < 16, ∀ m ∈ combos wz0Basis, actC11 (dArr u) m ^^^ m ∈ combos oct5Basis := by
  decide +kernel

end CFSG.ASVolI.H16
