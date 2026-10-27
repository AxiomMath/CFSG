module

public import CFSG.LocalAnalysis.StandardType.GGExcSmallCompOrder
public import CFSG.LocalAnalysis.StandardType.GGExcToralSylowElem

public section

namespace CFSG.StandardType

section Reduction

@[expose] def GGLayerNotExcThreeRestNsNonToral : Prop :=
  GGExcCentCompNonToralNsInput .F4 ∧ GGExcCentCompNonToralNsInput .E7 ∧
    GGExcCentCompNonToralNsInput .E8 ∧ GGE6InndiagCompNonToralNsInput ∧
    GGTwE6InndiagCompInput

theorem ggLayerNotExcThreeRestSylow_of_nonSplit (hT : GGExcElemToralRest)
    (h : GGLayerNotExcThreeRestNsNonToral) : GGLayerNotExcThreeRestSylow :=
  ggLayerNotExcThreeRestSylow_of_rest
    (ggLayerNotExcThreeRest_of_ns hT
      ⟨ggExcSmallCompOrderInput_holds, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩)

end Reduction

section Arithmetic

theorem ggNotExcThreeOrder_of_sl2_dvd {n a : ℕ} (ha : 4 ≤ a)
    (hSL : 2 ^ a * ((2 ^ a) ^ 2 - 1) ∣ n) : GGNotExcThreeOrder n := by
  refine (ggNotExcThreeOrder_iff n).mpr fun N₀ hN₀ heq => ?_
  have hn : n = 174182400 ∨ n = 25920 ∨ n = 360 := by
    rcases hN₀ with rfl | rfl | rfl <;> simp [heq]
  have h2 : 2 ^ (a * 1) ∣ n := by
    rw [mul_one]
    exact (dvd_mul_right _ _).trans hSL
  rcases TagsExc.small_of_dvd (by omega) le_rfl h2 hSL hn with ⟨h, -⟩ | ⟨h, -⟩ <;> omega

end Arithmetic

end CFSG.StandardType
