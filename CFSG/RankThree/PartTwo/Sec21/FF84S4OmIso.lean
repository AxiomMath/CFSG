module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG.ComponentClassification.AS81

abbrev F6 := Fin 6 → ZMod 2

@[expose] def qNorm3 (v : Fin 3 → Fin 2 → ZMod 2) : ZMod 2 :=
  ∑ i, (v i 0 * v i 0 + v i 0 * v i 1 + v i 1 * v i 1)

@[expose] def omIsoFun (v : F6) : Fin 3 → Fin 2 → ZMod 2 :=
  ![![v 0 + v 1 + v 3, v 2 + v 3], ![v 0 + v 2 + v 3, v 1 + v 2 + v 3], ![v 4, v 5]]

@[expose] def omIsoLin : F6 →ₗ[ZMod 2] (Fin 3 → Fin 2 → ZMod 2) where
  toFun := omIsoFun
  map_add' x y := by
    funext i j
    fin_cases i <;> fin_cases j <;> simp [omIsoFun] <;> ring
  map_smul' c x := by
    funext i j
    fin_cases i <;> fin_cases j <;> simp [omIsoFun] <;> ring

private theorem omIsoFun_qNorm3 : ∀ v : F6, qNorm3 (omIsoFun v) = qMinus v := by
  decide

private theorem omIsoLin_injective : Function.Injective omIsoLin := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  revert hv
  revert v
  decide

theorem Om_iso_qNorm3 : ∃ φ : F6 ≃ₗ[ZMod 2] (Fin 3 → Fin 2 → ZMod 2),
    ∀ v, qNorm3 (φ v) = qMinus v := by
  have hbij : Function.Bijective omIsoLin :=
    (Fintype.bijective_iff_injective_and_card omIsoLin).mpr ⟨omIsoLin_injective, by simp⟩
  exact ⟨LinearEquiv.ofBijective omIsoLin hbij, fun v => omIsoFun_qNorm3 v⟩

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
