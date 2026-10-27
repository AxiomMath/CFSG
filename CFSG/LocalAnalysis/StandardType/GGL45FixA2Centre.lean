module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.LieType.Steinberg.CentralExt.PSLMultiplier
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOther

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem gffa2_card_center_dvd_linear {X : Type} [Group X] [Finite X] (hX : Group.IsPerfect X)
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n) (hK : Nat.card K = 2 ^ n)
    (θ : X ⧸ Subgroup.center X ≃* LargeEvenProj (LargeEvenSLGroup (Fin 3) K)) :
    Nat.card (Subgroup.center X) ∣ 3 := by
  letI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 2 ^ n := by rw [Fintype.card_eq_nat_card, hK]
  have hk : 3 ≤ Fintype.card K := by
    rw [hcardK]
    calc (3 : ℕ) ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h34 : ¬ (3 = 3 ∧ Fintype.card K = 4) := by
    rintro ⟨-, h4⟩
    rw [hcardK] at h4
    have h4' : 2 ^ n = 2 ^ 2 := by rw [h4]; norm_num
    have : n = 2 := Nat.pow_right_injective (by norm_num : 2 ≤ 2) h4'
    omega
  obtain ⟨-, ⟨φ⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_hopfMultiplier_of_three_le
    (k := K) (n := 3) le_rfl hk h34
  let e'' : X ⧸ Subgroup.center X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K :=
    θ.trans ((TypeA.recipeEquiv 3 K).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        3 K).symm)
  have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hX e''
  have hM : Nat.card (CFSG.Open.griessHopfMultiplier
      (Matrix.ProjectiveSpecialLinearGroup (Fin 3) K)) = Nat.gcd 3 (Fintype.card K - 1) := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [hM] at hdvd
  exact hdvd.trans (Nat.gcd_dvd_left _ _)

theorem gffa2_card_center_dvd_unitary
    {X : Type} [Group X] [Finite X] (hX : Group.IsPerfect X)
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (θ : X ⧸ Subgroup.center X ≃* LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n))) :
    Nat.card (Subgroup.center X) ∣ 3 := by
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := CFSG.LieType.Steinberg.charP_of_card_eq_sq_pow Nat.prime_two hK
  have hn1 : 1 ≤ n := by omega
  have ho : ¬ Even 3 := by decide
  have hq : (3, 2 ^ n) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ n = 2 := (Prod.mk.inj h).2
    have h2' : 2 ^ n = 2 ^ 1 := by rw [h2]; norm_num
    have : n = 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2'
    omega
  obtain ⟨-, ⟨φ⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SUOdd.psu_odd_hopfMultiplier
    (F := K) (p := 2) (f := n) hK hn1 (n := 3) (le_refl 3) ho hq
  let e'' : X ⧸ Subgroup.center X ≃* CFSG.Open.StatedProj
      (CFSG.Open.StatedSU 3 (2 ^ n) K) := θ
  have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hX e''
  have hM : Nat.card (CFSG.Open.griessHopfMultiplier
      (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) K))) =
      Nat.gcd 3 (2 ^ n + 1) := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [hM] at hdvd
  exact hdvd.trans (Nat.gcd_dvd_left _ _)

end CFSG.StandardType
