module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.Arith
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.OrderOfX
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.NatOrderClass

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

open CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem kOrd_nontrivial {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {n : ℕ}
    (h : IsNaturalClassicalModule H n) : Nontrivial ↥H :=
  (natOrderClass_of_natural h).1

theorem kOrd_binaryNaturalSL {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {X : Type}
    [Group X] [Finite X] {n : ℕ} (h : IsNaturalClassicalModule H n) (hX : IsL2 X n)
    (hc : Nat.card ↥H = Nat.card X) : CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 2 n := by
  obtain ⟨hn2, hXc⟩ := isL2_two_le_and_card hX
  have hq : 2 ≤ 2 ^ n := by
    simpa using Nat.pow_le_pow_of_le (a := 2) (n := 1) (m := n) (by norm_num) (by omega)
  obtain ⟨-, hcls⟩ := natOrderClass_of_natural h
  rcases hcls with ⟨hb, -⟩ | ⟨-, hcard⟩ | ⟨-, hsq⟩ | hcube
  · exact hb
  · rw [hc, hXc] at hcard
    exact absurd hcard (ordL2_ne_ordOmegaMinusFour hq)
  · have h2 := hsq hn2
    rw [hc, hXc] at h2
    exact absurd h2 (not_sq_dvd_ordL2 hq)
  · rw [hc, hXc] at hcube
    exact absurd hcube (not_pow_three_dvd_ordL2 hq)

theorem kOrd_natOmegaMinus_four {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {X : Type}
    [Group X] [Finite X] {n : ℕ} (h : IsNaturalClassicalModule H n) (hX : IsOmegaMinus X 4 n)
    (hc : Nat.card ↥H = Nat.card X) : NatOmegaMinus H ⊤ ⊥ 4 n := by
  obtain ⟨hn1, hXc⟩ := isOmegaMinus_four_one_le_and_card hX
  have hq : 2 ≤ 2 ^ n := by
    simpa using Nat.pow_le_pow_of_le (a := 2) (n := 1) (m := n) (by norm_num) hn1
  obtain ⟨-, hcls⟩ := natOrderClass_of_natural h
  rcases hcls with ⟨-, hcard1⟩ | ⟨hN, -⟩ | ⟨hdvd, -⟩ | hcube
  · rw [hc, hXc] at hcard1
    exact absurd hcard1.symm (ordL2_ne_ordOmegaMinusFour hq)
  · exact hN
  · rw [hc, hXc] at hdvd
    exact absurd hdvd (not_ordOmegaMinusFour_dvd_ordOFourPlus hq)
  · rw [hc, hXc] at hcube
    exact absurd hcube (not_pow_three_dvd_ordOmegaMinusFour hq)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

end
