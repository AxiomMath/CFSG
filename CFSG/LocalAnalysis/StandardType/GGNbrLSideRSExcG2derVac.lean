module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcVac

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem ggNbrLSidePSL3_card_gt_12096 {F : Type} [Field F] [Finite F] (hF : 4 ≤ Nat.card F) :
    12096 < Nat.card (projectiveSL 3 F) := by
  obtain ⟨a, ha⟩ : ∃ a, Nat.card F = a + 1 := ⟨Nat.card F - 1, by omega⟩
  have ha3 : 3 ≤ a := by omega
  have hSL := card_SL_eq (K := F) (n := 3) (by norm_num)
  have hz := card_scalars_dvd (K := F) (n := 3) (by norm_num)
  have hmul : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) =
      Nat.card (projectiveSL 3 F) * Nat.card (scalars 3 F) :=
    (scalars 3 F).card_eq_card_quotient_mul_card_subgroup
  have hprod : ∏ j ∈ Finset.Icc 2 3, (Nat.card F ^ j - 1) =
      (Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  have h2 : Nat.card F ^ 2 - 1 = a * (a + 2) := by
    rw [ha]
    apply Nat.sub_eq_of_eq_add
    ring
  have h3 : Nat.card F ^ 3 - 1 = a * (a ^ 2 + 3 * a + 3) := by
    rw [ha]
    apply Nat.sub_eq_of_eq_add
    ring
  have hSL' : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) =
      (a + 1) ^ 3 * (a * (a + 2) * (a * (a ^ 2 + 3 * a + 3))) := by
    rw [hSL, hprod, h2, h3, ha]
  have hza : Nat.card (scalars 3 F) ≤ a := by
    refine Nat.le_of_dvd (by omega) ?_
    simpa [ha] using hz
  by_contra hcon
  have hP : Nat.card (projectiveSL 3 F) ≤ 12096 := not_lt.mp hcon
  have hle : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) ≤ 12096 * a := by
    rw [hmul]
    exact Nat.mul_le_mul hP hza
  have hlow : 12097 ≤ (a + 1) ^ 3 * (a + 2) * (a * (a ^ 2 + 3 * a + 3)) := by
    have h1 : 64 ≤ (a + 1) ^ 3 := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ (a + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h2' : 5 ≤ a + 2 := by omega
    have h3' : 63 ≤ a * (a ^ 2 + 3 * a + 3) := by
      calc 63 = 3 * (3 ^ 2 + 3 * 3 + 3) := by norm_num
        _ ≤ a * (a ^ 2 + 3 * a + 3) :=
          Nat.mul_le_mul ha3 (by nlinarith [ha3])
    calc 12097 ≤ 64 * 5 * 63 := by norm_num
      _ ≤ (a + 1) ^ 3 * (a + 2) * (a * (a ^ 2 + 3 * a + 3)) :=
        Nat.mul_le_mul (Nat.mul_le_mul h1 h2') h3'
  have hS : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) =
      a * ((a + 1) ^ 3 * (a + 2) * (a * (a ^ 2 + 3 * a + 3))) := by
    rw [hSL']
    ring
  rw [hS] at hle
  nlinarith [hlow, hle, ha3]

theorem ggNbrLSideNoPSL3_g2der
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    GGNbrLSideNoPSL3 (LargeEvenChevIDImage LargeEvenCartanG2 K
      (LargeEvenChevH LargeEvenCartanG2 K true)) := by
  intro φ _ _ _ J hJ F _ _ hF4
  refine ⟨fun e => ?_⟩
  have hcardC : Nat.card ↥(LargeEvenChevGroup LargeEvenCartanG2 K) = 12096 := by
    obtain ⟨T⟩ := InnerDiagE6.exists_largeEvenChevEquiv .G2 (K := K)
    exact (Nat.card_congr T.toEquiv).symm.trans
      (CFSG.ComponentClassification.ExcSelector.card_adjointGroup_G2_two (k := K) hK)
  haveI : Finite ↥(LargeEvenChevGroup LargeEvenCartanG2 K) :=
    Nat.finite_of_card_ne_zero (by rw [hcardC]; norm_num)
  have hHC : LargeEvenChevH LargeEvenCartanG2 K true ≤
      LargeEvenChevGroup LargeEvenCartanG2 K := by
    show ⁅LargeEvenChevGroup LargeEvenCartanG2 K, LargeEvenChevGroup LargeEvenCartanG2 K⁆ ≤
      LargeEvenChevGroup LargeEvenCartanG2 K
    exact Subgroup.commutator_le_self _
  haveI : Finite ↥(LargeEvenChevH LargeEvenCartanG2 K true) :=
    Finite.of_injective (Subgroup.inclusion hHC) (Subgroup.inclusion_injective hHC)
  have hcardH : Nat.card ↥(LargeEvenChevH LargeEvenCartanG2 K true) ≤
      Nat.card ↥(LargeEvenChevGroup LargeEvenCartanG2 K) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hHC) (Subgroup.inclusion_injective hHC)
  have hcardR : Nat.card (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true)) ≤
      Nat.card ↥(LargeEvenChevH LargeEvenCartanG2 K true) :=
    Nat.card_le_card_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  haveI : Finite (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true)) :=
    Finite.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hcardJ : Nat.card ↥J ≤
      Nat.card (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true)) :=
    Subgroup.card_le_card_group J
  have hcardQ : Nat.card (↥J ⧸ Subgroup.center ↥J) ≤ Nat.card ↥J :=
    Nat.card_le_card_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have heq : Nat.card (projectiveSL 3 F) = Nat.card (↥J ⧸ Subgroup.center ↥J) :=
    (Nat.card_congr e.toEquiv).symm
  have hgt := ggNbrLSidePSL3_card_gt_12096 (F := F) hF4
  omega

end CFSG.StandardType

end
