module

public import CFSG.Quasithin.Background.A318PHatIrr
public import CFSG.Quasithin.Background.A318POutMore
public import CFSG.Quasithin.Background.A318POutSpor
public import CFSG.RankThree.Asc83Table.M22

public section

namespace CFSG.Quasithin

namespace A318P

open CFSG.Blueprint

abbrev a6a : Equiv.Perm (Fin 6) := List.formPerm [0, 1, 2]

abbrev a6b : Equiv.Perm (Fin 6) := List.formPerm [3, 4, 5]

abbrev a6n : Equiv.Perm (Fin 6) := List.formPerm [0, 3] * List.formPerm [1, 4, 2, 5]

abbrev a7a : Equiv.Perm (Fin 7) := List.formPerm [0, 1, 2]

abbrev a7b : Equiv.Perm (Fin 7) := List.formPerm [3, 4, 5]

abbrev a7n : Equiv.Perm (Fin 7) := List.formPerm [0, 3] * List.formPerm [1, 4, 2, 5]

theorem hatData_alt6 : HatData (alternatingGroup (Fin 6)) where
  out := not_dvd_outer_alternating_six (MulEquiv.refl _) Nat.prime_three (by norm_num)
  card := ⟨40, by
    have := CFSG.LieType.SteinbergBR.SmallAlt.card_alternating (m := 6) (by norm_num)
    rw [show Nat.factorial 6 = 720 by decide] at this
    omega, by norm_num⟩
  irr := exists_irr_perm (alternatingGroup (Fin 6)) (a := a6a) (b := a6b) (n := a6n)
    (Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)) (Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel))
    (Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem hatData_alt7 : HatData (alternatingGroup (Fin 7)) where
  out := not_dvd_outer_alternating (Or.inr (by norm_num)) (MulEquiv.refl _) Nat.prime_three
    (by norm_num)
  card := ⟨280, by
    have := CFSG.LieType.SteinbergBR.SmallAlt.card_alternating (m := 7) (by norm_num)
    rw [show Nat.factorial 7 = 5040 by decide] at this
    omega, by norm_num⟩
  irr := exists_irr_perm (alternatingGroup (Fin 7)) (a := a7a) (b := a7b) (n := a7n)
    (Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)) (Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel))
    (Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem hatData_M22
    : HatData (NativeSporadic.Carrier .M22) where
  out := by
    have : Finite (NativeSporadic.Carrier .M22) := inferInstanceAs (Finite NativeSporadic.M22)
    exact not_dvd_outer_M22 (MulEquiv.refl _) Nat.prime_three (by norm_num)
  card := ⟨49280, by
    rw [show Nat.card (NativeSporadic.Carrier .M22) = 443520 from CFSG.Sporadic.Schreier.m22_card], by norm_num⟩
  irr := exists_irr_perm NativeSporadic.M22 (a := CFSG.RankThree.Asc83Table.M22.x)
    (b := CFSG.RankThree.Asc83Table.M22.y) (n := CFSG.RankThree.Asc83Table.M22.gI)
    CFSG.RankThree.Asc83Table.M22.x_mem CFSG.RankThree.Asc83Table.M22.y_mem
    CFSG.RankThree.Asc83Table.M22.gI_mem (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end A318P

end CFSG.Quasithin
