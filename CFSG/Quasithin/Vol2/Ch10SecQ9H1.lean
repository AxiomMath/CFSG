module

public import CFSG.Quasithin.Vol2.Ch10SecQ9G12
public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGC
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Quasithin.Vol2.Ch11.SecA.C11P9B

theorem card_SL_five_two : Nat.card (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) = 9999360 := by
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_five]

theorem injective_of_simple {X Y : Type} [Group X] [Group Y] [IsSimpleGroup X] [Nontrivial Y]
    (f : X →* Y) (hf : Function.Surjective f) : Function.Injective f := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff f).mp h
  · exfalso
    obtain ⟨y, hy⟩ := exists_ne (1 : Y)
    obtain ⟨x, rfl⟩ := hf y
    exact hy ((MonoidHom.mem_ker (f := f)).mp (by rw [h]; exact Subgroup.mem_top x))

theorem isSimpleGroup_of_isPSLEps3 {X : Type} [Group X] {s : Bool} {r e : ℕ}
    (hX : IsPSLEps3 s r e X) : IsSimpleGroup X := by
  cases s
  · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 3 r e hX).2
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 r e hX).2

theorem factK7L5_holds : FactK7L5 := by
  intro X _ s r e hX f hf
  have := isSimpleGroup_of_isPSLEps3 hX
  have : Nontrivial (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [card_SL_five_two]; norm_num)
  have hinj := injective_of_simple f hf
  have hN : Nat.card X = 9999360 := by
    rw [Nat.card_congr (Equiv.ofBijective f ⟨hinj, hf⟩), card_SL_five_two]
  cases s
  · have h := card_mul_gcd_of_isPSU3 hX
    generalize r ^ e = q at h
    have hd1 : 1 ≤ Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hd3 : Nat.gcd 3 (q + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    rw [hN] at h
    obtain ⟨h1, h2⟩ := window_U hd1 hd3 h (a := 7) (b := 8) (by norm_num) (by norm_num)
    interval_cases q
    norm_num at h
  · have h := card_mul_gcd_of_isPSL3' hX
    generalize r ^ e = q at h
    have hd1 : 1 ≤ Nat.gcd 3 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hd3 : Nat.gcd 3 (q - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    rw [hN] at h
    obtain ⟨h1, h2⟩ := window_L hd1 hd3 h (a := 7) (b := 8) (by norm_num) (by norm_num)
    interval_cases q
    norm_num at h

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
