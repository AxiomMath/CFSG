module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.StatementB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineK
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SpLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.LineL2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.LineOmega4Minus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.LineOmega4Plus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem kAdj_of_lines
    (hSU4 : ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ),
      (∃ a : ℕ, n = 2 * a ∧ IsSUn ↥H 4 a ∧ NatSUn H ⊤ ⊥ 4 a) → 3 ≤ n → KAdjAt W H n)
    (hO6m : ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ),
      (IsOmegaMinus ↥H 6 n ∧ NatOmegaMinus H ⊤ ⊥ 6 n) → 3 ≤ n → KAdjAt W H n)
    (hO6p : ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ),
      (IsOmegaPlus ↥H 6 n ∧ NatOmegaPlus H ⊤ ⊥ 6 n) → 3 ≤ n → KAdjAt W H n)
    (hO8m : ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ),
      (IsOmega8m ↥H n ∧ NatOmegaMinus H ⊤ ⊥ 8 n) → 3 ≤ n → KAdjAt W H n) :
    KAdj := by
  intro W _ _ H n hnat hperf hn
  have hnat' := hnat
  rcases hnat' with h | h | h | h | h | h | h | h | h | h | h
  · intro S ℓ Pℓ Kstar hK
    exact absurd (KTabD.kTab23d_L2 H n hnat hperf hn S h) hK
  · intro S ℓ Pℓ Kstar hK
    exact absurd (KTabD.kTab23d_omegaMinusFour H n hnat hperf hn S h) hK
  · intro S ℓ Pℓ Kstar hK
    exact absurd (KTabD.kTab23d_omegaPlusFour H n hnat hperf hn S h) hK
  · exact kAdjAt_sp4 H h hn
  · exact kAdjAt_sl (k := 3) H (Or.inl rfl) h hn
  · exact hSU4 W H n h hn
  · exact hO6m W H n h hn
  · exact kAdjAt_sl (k := 4) H (Or.inr rfl) h hn
  · exact hO6p W H n h hn
  · exact kAdjAt_sp6 H h hn
  · exact hO8m W H n h hn

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
