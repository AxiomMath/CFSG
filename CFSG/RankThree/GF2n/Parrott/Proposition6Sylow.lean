module

public import CFSG.RankThree.GF2n.Parrott.Proposition6D8SquareOne
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K5PermA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS2a
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.OddStandard.SmallF3.HarrisU33
open CFSG.OddStandard.SmallF3.Omega
open CFSG.OddStandard.SmallF3.Omega.K5
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {z : G}

theorem card_inf_L1_L2 {L1 L2 : Subgroup G} (hL1 : Nonempty (↥L1 ≃* SL23))
    (hinf1 : L1 ⊓ L2 = (Subgroup.center L1).map L1.subtype) :
    Nat.card ((Subgroup.center L1).map L1.subtype) = 2 := by
  obtain ⟨e⟩ := hL1
  rw [Subgroup.card_subtype L1 (Subgroup.center L1)]
  exact (Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans card_center_sl23_p6

theorem card_core
    {L1 L2 : Subgroup G}
    (hL1 : Nonempty (↥L1 ≃* SL23))
    (hL2 : Nonempty (↥L2 ≃* SL23))
    (hcomm : ∀ x ∈ L1, ∀ y ∈ L2, x * y = y * x)
    (hinf1 : L1 ⊓ L2 = (Subgroup.center L1).map L1.subtype)
    (hsup : L1 ⊔ L2 = twoThreeCore (H z)) :
    Nat.card (twoThreeCore (H z)) = 288 := by
  classical
  have hcardL1 : Nat.card ↥L1 = 24 := by
    obtain ⟨e⟩ := hL1
    exact (Nat.card_congr e.toEquiv).trans card_sl23_p6
  have hcardL2 : Nat.card ↥L2 = 24 := by
    obtain ⟨e⟩ := hL2
    exact (Nat.card_congr e.toEquiv).trans card_sl23_p6
  have hcardZ : Nat.card ((Subgroup.center L1).map L1.subtype) = 2 :=
    card_inf_L1_L2 hL1 hinf1
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute L1 L2 hcomm).1
  rw [hsup, hinf1, hcardZ, hcardL1, hcardL2] at hprod
  omega

theorem mem_normalizer_zpowers_iff {Y : Type} [Group Y] (q x : Y) (hq3 : q ^ 3 = 1)
    (hq1 : q ≠ 1) :
    x ∈ Subgroup.normalizer (Subgroup.zpowers q : Set Y) ↔
      x * q * x⁻¹ = q ∨ x * q * x⁻¹ = q⁻¹ := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  have hq2 : q ^ 2 = q⁻¹ := by
    have h : q ^ 2 * q = 1 := by
      rw [← pow_succ]
      simpa using hq3
    exact eq_inv_of_mul_eq_one_left h
  constructor
  · intro h
    have hmem : x * q * x⁻¹ ∈ Subgroup.zpowers q := by
      rw [← h]
      exact Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk' : q ^ (k % 3) = x * q * x⁻¹ := by
      calc q ^ (k % 3) = q ^ (k % (3 : ℤ)) := by norm_num
        _ = q ^ k := (zpow_eq_zpow_emod' k hq3).symm
        _ = x * q * x⁻¹ := hk
    have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
    have hlt : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
    have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hcases with hc | hc | hc
    · exfalso
      rw [hc] at hk'
      simp only [zpow_zero] at hk'
      apply hq1
      calc q = x⁻¹ * (x * q * x⁻¹) * x := by group
        _ = x⁻¹ * 1 * x := by rw [hk']
        _ = 1 := by group
    · left
      rw [hc] at hk'
      simpa using hk'.symm
    · right
      rw [hc] at hk'
      simpa [hq2] using hk'.symm
  · rintro (h | h)
    · change Subgroup.zpowers (x * q * x⁻¹) = Subgroup.zpowers q
      rw [h]
    · change Subgroup.zpowers (x * q * x⁻¹) = Subgroup.zpowers q
      rw [h, Subgroup.zpowers_inv]

end CFSG.RankThree.GF2n.Parrott
