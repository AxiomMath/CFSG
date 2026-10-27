module

public import CFSG.Assembly.GL83LieDefs
import CFSG.LieType.Steinberg.CentralExt.POmegaPlusMultiplier
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.Blueprint.MultiplierDefs
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect
import CFSG.LieType.Steinberg.CentralExt.PSL2Multiplier
import CFSG.LieType.Steinberg.G2

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem gds_generic_POmegaPlus_four_two_card {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (CFSG.Blueprint.Multiplier.generic .POmegaPlus 4 2 n) = 1 := by
  have heven : Even (2 ^ n) := (Nat.even_pow' (Nat.one_le_iff_ne_zero.mp hn)).mpr even_two
  have hord : CFSG.Blueprint.Multiplier.genericOrders .POmegaPlus 4 2 n = (1, 1) := by
    simp [CFSG.Blueprint.Multiplier.genericOrders, heven]
  have hmult (m : ℕ) : Nat.card (Multiplicative (ZMod m)) = m :=
    (Nat.card_congr (Multiplicative.ofAdd (α := ZMod m))).symm.trans (Nat.card_zmod m)
  simp only [CFSG.Blueprint.Multiplier.generic, hord, Nat.card_prod, Prod.fst, Prod.snd,
    hmult]

theorem ggD4_center_eq_bot {X : Type} [Group X] [Finite X] (hX : commutator X = ⊤)
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (θ : X ⧸ Subgroup.center X ≃* LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))) :
    Subgroup.center X = ⊥ := by
  have hperf : Group.IsPerfect X := ⟨hX⟩
  have hcard4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right' (by norm_num) hn
  obtain ⟨-, ⟨e⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.pomegaPlus_hopfMultiplier
      (K := K) (n := 4) (p := 2) (f := n) (by norm_num) hK hcard4
  have hdiv : Nat.card (Subgroup.center X) ∣
      Nat.card (CFSG.Open.griessHopfMultiplier
        (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)))) :=
    CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hperf θ
  have hgen : Nat.card (CFSG.Open.griessHopfMultiplier
      (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)))) = 1 :=
    (Nat.card_congr e.toEquiv).trans
      (gds_generic_POmegaPlus_four_two_card (le_trans (by norm_num : 1 ≤ 2) hn))
  rw [hgen] at hdiv
  exact Subgroup.eq_bot_of_card_le (Subgroup.center X) (Nat.le_of_dvd Nat.one_pos hdiv)

end CFSG.StandardType
