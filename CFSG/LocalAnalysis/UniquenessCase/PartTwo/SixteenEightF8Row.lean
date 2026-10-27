module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowLin
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowOmega

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem S16gRowCtx.natural_eight_eq_omegaPlus_four (h : S16gRowCtx D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hc : ∃ n : ℕ,
      (IsSLn ↥(lBar V₀ V hV L) n 3 ∧
        BinaryNaturalSL (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
          (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) n 3) ∨
      (IsSpn ↥(lBar V₀ V hV L) n 3 ∧
        NatSpn (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
          (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) n 3) ∨
      (IsOmegaPlus ↥(lBar V₀ V hV L) n 3 ∧
        NatOmegaPlus (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
          (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) n 3) ∨
      (IsOmegaMinus ↥(lBar V₀ V hV L) n 3 ∧
        NatOmegaMinus (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
          (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) n 3)) :
    IsOmegaPlus ↥(lBar V₀ V hV L) 4 3 ∧
      NatOmegaPlus (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
        (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 4 3 := by
  obtain ⟨n, hn | hn | hn | hn⟩ := hc
  · exact (h.false_of_binaryNaturalSL hGA hn.1 hn.2).elim
  · exact (h.false_of_natSp hGA hn.1 hn.2).elim
  · by_cases h4 : n = 4
    · subst h4
      exact hn
    · exact (h.false_of_natOmegaPlus h4 hn.2).elim
  · exact (h.false_of_natOmegaMinus hGA hn.1 hn.2).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
