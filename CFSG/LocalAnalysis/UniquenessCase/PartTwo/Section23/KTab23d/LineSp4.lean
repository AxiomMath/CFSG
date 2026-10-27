module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.Holds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.Transfer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FlagGeneric
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.LeviFactBridge
import CFSG.Quasithin.Vol2.KGNatSp4Levi

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

private lemma charP_two_D18 {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : n ≠ 0) : CharP K 2 := by
  have h : Nat.card K • (1 : K) = 0 := card_nsmul_eq_zero'
  rw [hK, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat] at h
  exact CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero ((pow_eq_zero_iff hn).mp h)

theorem kTab23d_sp4 {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ)
    (hnat : IsNaturalClassicalModule H n) (hperf : ⁅H, H⁆ = H) (hn : 3 ≤ n) (S : Sylow 2 ↥H)
    (h : IsSp4 ↥H n ∧ NatSpn H ⊤ ⊥ 4 n) : IsL2 (Bar2 (Hinf (pointStab H S))) n := by
  obtain ⟨-, -, K, hKf, hKfin, hK, π, hπ⟩ := h
  letI := hKf
  letI := hKfin
  haveI : CharP K 2 := charP_two_D18 hK (by omega)
  obtain ⟨-, e, -⟩ := KTabC.exists_natEquiv (K := K) ⟨π, hπ⟩
  have hW : ∀ w : W, w ^ 2 = 1 := fun w => pow_two_eq_one_of_natEquiv e w
  obtain ⟨hcard, -, -⟩ := kTab23a_holds W H n hnat hperf S
  have hflag := isFlagW_fixedPoint H S (2 ^ n) hcard
  have hsyl := isSylowTwoOf_map H S
  exact isL2_bar2_hinf_pointStab_of_levi H S (by omega) hK
    (CFSG.Quasithin.Vol2.KGNat.factLeviSp4_holds K n (by omega) hK W hW H ⊥ π hπ _
      hsyl 1 _ (Or.inl rfl) hflag)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
