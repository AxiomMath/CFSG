module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.ReduceLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineSp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.StabSp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Shapes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open CFSG.Open PartTwo

private lemma charP_two_D23 {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : n ≠ 0) : CharP K 2 := by
  have h : Nat.card K • (1 : K) = 0 := card_nsmul_eq_zero'
  rw [hK, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat] at h
  exact CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero ((pow_eq_zero_iff hn).mp h)

theorem kTab23d_sp6 {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ)
    (hnat : IsNaturalClassicalModule H n) (hperf : ⁅H, H⁆ = H) (hn : 3 ≤ n) (S : Sylow 2 ↥H)
    (h : IsSpn ↥H 6 n ∧ NatSpn H ⊤ ⊥ 6 n) : IsSp4 (Bar2 (Hinf (pointStab H S))) n := by
  obtain ⟨-, K, hKf, hKfin, hK, hreal⟩ := h.2
  letI := hKf
  letI := hKfin
  haveI : CharP K 2 := charP_two_D23 hK (by omega)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨e1⟩ := (bar2_hinf_pointStab_equiv hreal (sylowFixedLine_statedSp 3) S).1
  obtain ⟨e2⟩ := nonempty_bar2_hinf_lineStab_statedSp K hK4 2 (by norm_num)
  exact isSp4_of_mulEquiv_statedSp (by omega) hK (e1.trans e2)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
