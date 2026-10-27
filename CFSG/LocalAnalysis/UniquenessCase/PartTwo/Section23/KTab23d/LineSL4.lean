module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.ReduceLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineSL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.StabSL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open CFSG.Open PartTwo

private lemma charP_two_of_card_D21 {K : Type} [Field K] [Finite K] {n : ℕ} (hn : n ≠ 0)
    (hK : Nat.card K = 2 ^ n) : CharP K 2 := by
  have h : Nat.card K • (1 : K) = 0 := card_nsmul_eq_zero'
  rw [hK, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat] at h
  exact CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero ((pow_eq_zero_iff hn).mp h)

theorem kTab23d_sl4 {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ)
    (hnat : IsNaturalClassicalModule H n) (hperf : ⁅H, H⁆ = H) (hn : 3 ≤ n) (S : Sylow 2 ↥H)
    (h : IsSLn ↥H 4 n ∧ CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 4 n) :
    IsSLn (Bar2 (Hinf (pointStab H S))) 3 n := by
  obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := h.2
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : CharP K 2 := charP_two_of_card_D21 (by omega) hKcard
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    exact pow_le_pow_right' (a := 2) (n := 2) (m := n) (by norm_num) (by omega)
  have hline : KTabC.SylowFixedLine (StatedSL 4 K) (Pi.single 0 1) :=
    sylowFixedLine_statedSL (K := K) (d := 4) (by norm_num)
  obtain ⟨⟨e1⟩, _, _⟩ := bar2_hinf_pointStab_equiv hreal hline S
  obtain ⟨e2⟩ := nonempty_bar2_hinf_lineStab_statedSL K hK4 3 (by norm_num)
  exact ⟨K, hKf, hKfin, hKcard, ⟨e1.trans e2⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
