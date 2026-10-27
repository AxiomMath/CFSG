module

public import CFSG.Quasithin.EmptyFaithful.SBc17Out5
public import CFSG.Quasithin.Background.HL42Aut
public import CFSG.Quasithin.H13.VolIAutSLFive
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

namespace SBc17

theorem center_sl_zmodTwo_eq_bot (n : ℕ) [NeZero n] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hA'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  rw [Subgroup.mem_bot]
  have h01 : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  have hr1 : r = 1 := by
    rcases h01 r with rfl | rfl
    · rw [zero_pow (NeZero.ne n)] at hr
      exact absurd hr (by decide)
    · rfl
  ext i j
  rw [← hA', hr1]
  simp [Matrix.one_apply]

theorem out5Inner_sl_four : Out5Inner (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :=
  out5Inner_of_card_mulAut_le (center_sl_zmodTwo_eq_bot 4)
    (by have := CFSG.Quasithin.H.L4.card_mulAut_SL_four; omega)

theorem out5Inner_sl_five : Out5Inner (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :=
  out5Inner_of_card_mulAut_le (center_sl_zmodTwo_eq_bot 5)
    (by have := CFSG.Quasithin.H13.VolI.autSLFiveTwo_holds; omega)

theorem out5Inner_statedSL_four :
    Out5Inner ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) :=
  out5Inner_sl_four.of_mulEquiv (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 (ZMod 2))

theorem out5Inner_statedSL_five :
    Out5Inner ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)) :=
  out5Inner_sl_five.of_mulEquiv (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 5 (ZMod 2))

end SBc17

end CFSG.Quasithin
