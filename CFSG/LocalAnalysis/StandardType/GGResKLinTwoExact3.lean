module

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeBLinearNs
public import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclicHolds
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1Holds
public import CFSG.LocalAnalysis.StandardType.GGResJTwA5Sylow
public import CFSG.LocalAnalysis.StandardType.GGResJTwE6Lagrange
public import CFSG.LocalAnalysis.StandardType.GGResNonsingularBase
public import CFSG.LocalAnalysis.StandardType.GGResJFusion
public import CFSG.LocalAnalysis.StandardType.GGResJOneReflCell
public import CFSG.LocalAnalysis.StandardType.GGResJOpenLabel
public import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsHolds
public import CFSG.LocalAnalysis.StandardType.GGTBE6
public import CFSG.LocalAnalysis.StandardType.GGTCJHolds
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceSchreier
public import CFSG.RankThree.PartOne.TCB.SchreierFinal
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthKSLOrder
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGResJThreeDvd
public import CFSG.LocalAnalysis.StandardType.GGPZWeylType
public import CFSG.LocalAnalysis.StandardType.GGPZWeylB
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySp
public import CFSG.LocalAnalysis.StandardType.GGTWLowStmt
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

theorem thirteen_dvd_ordTwistedE6_two_pow (m : ℕ) : 13 ∣ ordTwistedE6 (2 ^ m) := by
  unfold ordTwistedE6
  have h2 : (2 ^ m) ^ 2 = (2 ^ 2) ^ m := by rw [← pow_mul, ← pow_mul, mul_comm]
  have h12 : (2 ^ m) ^ 12 = (2 ^ 12) ^ m := by rw [← pow_mul, ← pow_mul, mul_comm]
  set q := 2 ^ m
  have h3 : 3 ∣ q ^ 2 - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow (2 ^ 2) 1 m
    rw [one_pow, ← h2] at h
    exact (show (3 : ℕ) ∣ 2 ^ 2 - 1 by norm_num).trans h
  have h13 : 13 ∣ q ^ 12 - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow (2 ^ 12) 1 m
    rw [one_pow, ← h12] at h
    exact (show (13 : ℕ) ∣ 2 ^ 12 - 1 by norm_num).trans h
  have hN3 : 3 ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
      (q ^ 2 - 1) :=
    h3.trans (dvd_mul_left _ _)
  have hN13 : 13 ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
      (q ^ 2 - 1) :=
    h13.trans
      ((((((dvd_mul_left _ _).mul_right _).mul_right _).mul_right _).mul_right _).mul_right _)
  have hN := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 13) hN3 hN13
  exact Nat.dvd_div_of_mul_dvd ((Nat.mul_dvd_mul_right (Nat.gcd_dvd_left 3 (q + 1)) 13).trans hN)

theorem not_thirteen_dvd_labOrd_linTwo {lab : LargeEvenLabel} (ht : lab.tag = .A)
    (hn : lab.n = 1) (hr : lab.rank ≤ 10) : ¬ 13 ∣ SporadicShape.labOrd lab := by
  obtain ⟨t, k, n⟩ := lab
  dsimp only at ht hn hr
  subst ht hn
  interval_cases k <;> decide +kernel

theorem ggTwE6_false_of_le_linTwo
    {G : Type} [Group G] [Finite G] {J K : Subgroup G} (hJK : J ≤ K)
    {labK labJ : LargeEvenLabel} (hlK : LargeEvenInLambda2 labK)
    (hhasK : GGHasLabel labK (↥K ⧸ Subgroup.center ↥K)) (htK : labK.tag = .A) (hnK : labK.n = 1)
    (hrK : labK.rank ≤ 10) (hlJ : LargeEvenInLambda2 labJ)
    (hhasJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) (htJ : labJ.tag = .twE6) : False := by
  have hdvd := ggKSL_labOrd_dvd hJK hlK hhasK hlJ hhasJ
  rw [labOrd_eq_ordTwistedE6 htJ] at hdvd
  exact not_thirteen_dvd_labOrd_linTwo htK hnK hrK
    ((thirteen_dvd_ordTwistedE6_two_pow _).trans hdvd)

section Cert

theorem GGResHyp.false_of_exact3_K_linTwo {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hp : p = 3)
    (hK : GGInnerDiagOnLabel (fun _ lab => lab.tag = .A ∧ lab.n = 1) p Bs K)
    (hD : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) : False := by
  subst hp
  have hT : GGTBTorAll := ggTBTorAll_of_remaining trivial
  have hLift : GGTBTorLiftRows := ggTBTorLiftRows_holds
  obtain ⟨k, labK, hk, ⟨e, -⟩, hΛK, ⟨htK, hnK⟩, hdK, hhasK⟩ :=
    ggWeylOfType_B_nbr_of_linearNs ggLabelCenterPCyclicInput_holds
      (S := fun _ lab => lab.tag = .A ∧ lab.n = 1) hH.1 hH.2.2.2.1 hH.2.2.2.2.1
      (fun lab h => ⟨h.1, by rw [h.2]; norm_num⟩) hK
  have hcardK : Nat.card ↥(ggAutomizer K Bs) = 2 ^ k * k.factorial :=
    (Nat.card_congr e.toEquiv).symm.trans (ggCoxeterB_card k (by omega))
  have hns : ¬ ggSingularWeylOrder 3 (Nat.card ↥(ggAutomizer K Bs)) := by
    rw [hcardK]
    exact not_ggSingularWeylOrder_two_pow_mul_factorial (by omega)
  have hJ0 : GGInnerDiagOn Bs J := ggBstarInnerDiagJInput_holds G 3 B Bs x L D J hH.1 hH.2.2.1.1
  have hJ : GGInnerDiagOnLabel (fun _ _ => True) 3 Bs J :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨trivial, h⟩) hJ0
  have hpJ : 3 ∣ Nat.card J := hH.1.dvd_card_J_of_eq_three rfl hJ0
  by_cases h3 : 3 ^ 3 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range
  · have hJE : GGInnerDiagOnLabel GGTableBTwE6ThreeLabel 3 Bs J :=
      (ggResExact3_twE6_of_nonsingular_K_of_tcj hT hLift TCJ.ggTCJKnown_holds
        ggLabelRigidInput_holds hH h3 hJ hns hD).mono_label fun _ h => h.2
    by_cases h5 : 3 ^ 5 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range
    · exact ggResExact3_false_of_card_K hH
        (hH.fix_mem_centralizer_J_of_twE6PlusThree_of_card hJE h5) hns hD
    obtain ⟨r, c, hr, hA⟩ := hH.weylType_automizer_of_exact3_nonsingular_K hns hD
      (hH.card_lt_of_twE6PlusThree_of_card_lt hJE (not_le.mp h5))
    have hB : GGWeylTypeData k (Nat.card ↥(ggAutomizer K Bs)) 2 :=
      Or.inr (Or.inl ⟨by omega, hcardK, rfl⟩)
    have hkr : k = r := ggWeylTypeData_rank_eq hB hA
    have h2 : (3 - 1 : ℕ) = 2 := rfl
    rw [h2] at hdK
    obtain ⟨labJ, hΛJ, hhasJ, _, _, _, _, _, ⟨htJ, -, -⟩, -⟩ := largeEvenMarking_exists_hasLabel hJE
    have hLB : GGLBalanceInput :=
      ggLBalanceInput_of_catalogueSchreier CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
    exact ggTwE6_false_of_le_linTwo (le_of_ggNbr hLB hH.1.1 hH.1.2.2 hpJ hH.2.2.2.2.1) hΛK hhasK
      htK hnK (by omega) hΛJ hhasJ htJ
  have h3' := not_le.mp h3
  rcases hH.automizer_J_bot_or_refl_of_exact3_nonsingular_K hns hD
      (hH.card_lt_of_card_gamma_J_lt h3') with hbot | ⟨h5, τ, hτ, hA⟩
  · exact hH.automizer_J_ne_bot_of_dvd hpJ hbot
  · exact hH.false_of_oneRefl hLift ggResJOneReflInput_holds h5 hJ0 hτ hA
      (hH.card_gamma_J_eq_sq_of_lt h3')

end Cert

end CFSG.StandardType

end
