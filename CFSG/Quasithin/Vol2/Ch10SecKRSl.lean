module

public import CFSG.Quasithin.Vol2.Ch10SecKRSd
public import CFSG.Quasithin.Vol2.Ch10SecQ9H16

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open Matrix C10P4F

theorem eq_one_of_botH {g : ↥(stabStd 2 3)} (hb : botH 2 3 g = 1) (h7 : g ^ 7 = 1) : g = 1 := by
  have ht : topH 2 3 g = 1 := by
    have h1 : (topH 2 3 g) ^ 7 = 1 := by rw [← map_pow, h7, map_one]
    have key : ∀ a : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), a ^ 7 = 1 → a = 1 := by decide
    exact key _ h1
  have hsq : (g : Matrix.SpecialLinearGroup (Fin (2 + 3)) (ZMod 2)) *
      (g : Matrix.SpecialLinearGroup (Fin (2 + 3)) (ZMod 2)) = 1 :=
    sq_eq_one_of_blocks g.2 (congrArg Subtype.val ht) (congrArg Subtype.val hb)
  have hsq' : g * g = 1 := Subtype.ext hsq
  rw [show (7 : ℕ) = 2 * 3 + 1 by rfl, pow_succ, pow_mul, sq, hsq', one_pow, one_mul] at h7
  exact h7

@[expose] def r3 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  trvE 0 1 (by decide) * trvE 1 0 (by decide)

theorem r3_pow : r3 ^ 3 = 1 := by decide

theorem r3_ne : r3 ≠ 1 := by decide

theorem theta_SL3 : theta (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) = ⊤ := by
  have := CFSG.QuasithinUnique.Bridge.isSimple_sl_zmod2 3 (by norm_num)
  exact theta_eq_top_of_simple r3_ne r3_pow

theorem exists_seven_of_ne {a : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)} (ha : a ≠ 1) :
    ∃ x ∈ Subgroup.normalClosure ({a} : Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))),
      orderOf x = 7 := by
  have := CFSG.QuasithinUnique.Bridge.isSimple_sl_zmod2 3 (by norm_num)
  have htop : Subgroup.normalClosure ({a} : Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) =
      ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.normalClosure ({a} : Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))) with h | h
    · exact absurd (Subgroup.mem_bot.mp (h ▸ Subgroup.subset_normalClosure rfl)) ha
    · exact h
  refine ⟨trvE 0 1 (by decide) * trvE 1 2 (by decide) * trvE 2 0 (by decide), by rw [htop]; trivial,
    ?_⟩
  exact orderOf_eq_prime (by decide) (by decide)

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
