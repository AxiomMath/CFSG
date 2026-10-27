module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.BorelTits.Kempf
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Tools
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

namespace SBc17

theorem card_sl_four : Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
  rw [Matrix.card_SL_field 4, ZMod.card]
  simp [Fin.prod_univ_succ]

theorem card_sl_five : Nat.card (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) = 9999360 := by
  rw [Matrix.card_SL_field 5, ZMod.card]
  simp [Fin.prod_univ_succ]

theorem not_seventeen_dvd_card_sl {d : ℕ} (hd : d = 4 ∨ d = 5) :
    ¬ 17 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) := by
  rcases hd with rfl | rfl
  · rw [card_sl_four]
    decide
  · rw [card_sl_five]
    decide

end SBc17

end CFSG.Quasithin
