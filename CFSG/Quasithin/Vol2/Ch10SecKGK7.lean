module

public import CFSG.Quasithin.Vol2.Ch10SecCFacts2
public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGC
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Quasithin.Vol2.Ch11.SecA.C11P9B

theorem factK7_holds : FactK7 := by
  intro X _ s r e hX f hf
  have hsimp : IsSimpleGroup X := by
    cases s
    · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 3 r e hX).2
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 r e hX).2
  have hinj : Function.Injective f := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff f).mp h
    · exfalso
      have : Nontrivial (alternatingGroup (Fin 7)) :=
        alternatingGroup.nontrivial_of_three_le_card (by simp)
      obtain ⟨y, hy⟩ := exists_ne (1 : alternatingGroup (Fin 7))
      obtain ⟨x, rfl⟩ := hf y
      exact hy ((MonoidHom.mem_ker (f := f)).mp (by rw [h]; exact Subgroup.mem_top x))
  have hN : Nat.card X = 2520 := by
    rw [Nat.card_congr (Equiv.ofBijective f ⟨hinj, hf⟩), Nat.card_eq_fintype_card,
      card_alternatingGroup, Fintype.card_fin]
    rfl
  cases s
  · have h := card_mul_gcd_of_isPSU3 hX
    generalize r ^ e = q at h
    have hd1 : 1 ≤ Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hd3 : Nat.gcd 3 (q + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    rw [hN] at h
    obtain ⟨h1, h2⟩ := window_U hd1 hd3 h (a := 2) (b := 3) (by norm_num) (by norm_num)
    interval_cases q
    norm_num at h
  · have h := card_mul_gcd_of_isPSL3' hX
    generalize r ^ e = q at h
    have hd1 : 1 ≤ Nat.gcd 3 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hd3 : Nat.gcd 3 (q - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    rw [hN] at h
    obtain ⟨h1, h2⟩ := window_L hd1 hd3 h (a := 2) (b := 3) (by norm_num) (by norm_num)
    interval_cases q
    norm_num at h

end CFSG.Quasithin.Vol2.Ch10.SecC
