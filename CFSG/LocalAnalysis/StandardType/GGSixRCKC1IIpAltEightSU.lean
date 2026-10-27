module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpAltEightTwo
import CFSG.LocalAnalysis.StandardType.SUCenterOdd
import CFSG.LieType.SemisimpleCentralizers.HeldLangU64Ord
import CFSG.RankThree.PartOne.KFOUT3.KtySUSmall
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
import CFSG.RankThree.PartOne.KF.UnitaryModel
import CFSG.RankThree.PartOne.KFOUT3.KtyD8
import CFSG.RankThree.PartOne.KFOUT3.KtyWCtx
import CFSG.RankThree.PartOne.S12.InputsKF2
import CFSG.RankThree.PartOne.S12.Sec1322Inputs
import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary

public section

namespace CFSG.StandardType.RCKC1

open CFSG.StandardType

theorem rckIIp_false_of_alt_eight_PSU
    {X : Type} [Group X] {r h : ℕ} (hh : 1 ≤ h) (π : (ggU .PSU r h).K →* X)
    (hker : π.ker ≤ Subgroup.center (ggU .PSU r h).K)
    (hodd : Odd (Nat.card (Subgroup.center ↥π.range)))
    (hA8 : Nonempty ((↥π.range ⧸ Subgroup.center ↥π.range) ≃* alternatingGroup (Fin 8))) :
    False := by
  classical
  obtain ⟨g, rfl⟩ : ∃ g, h = g + 1 := ⟨h - 1, by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := GaloisField 2 (2 * (g + 1))
  let σ : F ≃+* F := CFSG.LieType.BorelTits.unitaryInvolution F 2 (g + 1)
  let J := ↥π.range
  let ZJ := Subgroup.center J
  have hGcard : Nat.card (ggU .PSU r (g + 1)).K =
      Nat.card ↥(CFSG.LieType.Universal.Unitary.SU σ r) := rfl
  have hfinSU : Finite ↥(CFSG.LieType.Universal.Unitary.SU σ r) := inferInstance
  have : Finite (ggU .PSU r (g + 1)).K := hfinSU
  have : Finite J :=
    Finite.of_surjective π.rangeRestrict π.rangeRestrict_surjective
  have : Finite ZJ := inferInstance
  have hc : Nat.card F = (2 ^ (g + 1)) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)
  have hGker : Nat.card (ggU .PSU r (g + 1)).K = Nat.card J * Nat.card π.ker := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
    rw [h, Nat.card_congr (QuotientGroup.quotientKerEquivRange π).toEquiv]
  have hcardJ : Nat.card J = 20160 * Nat.card ZJ := rckIIp_card_range_of_alt_eight π hA8
  let H : Subgroup ↥(CFSG.LieType.Universal.Unitary.SU σ r) := π.ker
  have hHker : H ≤ Subgroup.center ↥(CFSG.LieType.Universal.Unitary.SU σ r) := hker
  have hkerodd : Odd (Nat.card π.ker) :=
    CFSG.StandardType.odd_natCard_of_le_center_SU σ hHker
  have hZJodd : Odd (Nat.card ZJ) := hodd
  have hvalG : padicValNat 2 (Nat.card (ggU .PSU r (g + 1)).K) = 6 := by
    have hZJ0 : Nat.card ZJ ≠ 0 := Nat.card_pos.ne'
    have hker0 : Nat.card π.ker ≠ 0 := Nat.card_pos.ne'
    have h20160 : padicValNat 2 20160 = 6 := by
      rw [show 20160 = 2 ^ 6 * 315 by norm_num,
        padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (by norm_num), add_zero]
    rw [hGker, hcardJ, padicValNat.mul (mul_ne_zero (by norm_num) hZJ0) hker0,
      padicValNat.mul (by norm_num) hZJ0, h20160,
      padicValNat.eq_zero_of_not_dvd hZJodd.not_two_dvd_nat,
      padicValNat.eq_zero_of_not_dvd hkerodd.not_two_dvd_nat, add_zero, add_zero]
  rcases Nat.eq_zero_or_pos r with h0 | hr
  ·
    subst r
    have hsubSU : Subsingleton ↥(CFSG.LieType.Universal.Unitary.SU σ 0) := by
      constructor
      intro a b
      apply Subtype.ext
      apply Units.ext
      ext i j
      exact Fin.elim0 i
    have hG1 : Nat.card (ggU .PSU 0 (g + 1)).K = 1 := by
      rw [hGcard]
      exact Nat.card_eq_one_iff_unique.mpr ⟨hsubSU, ⟨1⟩⟩
    have hJle : Nat.card J ≤ Nat.card (ggU .PSU 0 (g + 1)).K :=
      Nat.card_le_card_of_surjective π.rangeRestrict π.rangeRestrict_surjective
    have hJge : 20160 ≤ Nat.card J := by
      rw [hcardJ]
      calc 20160 = 20160 * 1 := (mul_one _).symm
        _ ≤ 20160 * Nat.card ZJ := Nat.mul_le_mul_left _ (Nat.card_pos (α := ZJ))
    omega
  ·
    have hpadG : padicValNat 2 (Nat.card (ggU .PSU r (g + 1)).K) =
        (g + 1) * (r * (r - 1) / 2) := by
      rw [hGcard, Nat.card_congr (CFSG.LieType.Universal.Unitary.equivStatedSU
        (p := 2) (f := g + 1) hc r).toEquiv]
      exact CFSG.LieType.SemisimpleCentralizers.HeldLang.padicValNat_card_statedSU
        (K := F) (a := g + 1) (d := r) (by omega) hr hc
    have hMul : (g + 1) * (r * (r - 1) / 2) = 6 := hpadG.symm.trans hvalG
    have hrle : r ≤ 4 := by
      have hle : r * (r - 1) / 2 ≤ 6 := by
        calc r * (r - 1) / 2 = 1 * (r * (r - 1) / 2) := (one_mul _).symm
          _ ≤ (g + 1) * (r * (r - 1) / 2) := Nat.mul_le_mul_right _ (by omega)
          _ = 6 := hMul
      by_contra h
      have h5 : 5 ≤ r := by omega
      have h4 : 4 ≤ r - 1 := by omega
      have h20 : 20 ≤ r * (r - 1) := by
        calc 20 = 5 * 4 := by norm_num
          _ ≤ r * (r - 1) := Nat.mul_le_mul h5 h4
      have h2 : r * (r - 1) = 2 * (r * (r - 1) / 2) :=
        (Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_pred_self r))).symm
      omega
    have h7J : 7 ∣ Nat.card J := by
      rw [hcardJ]
      exact dvd_mul_of_dvd_left (by norm_num) _
    have h7G : 7 ∣ Nat.card (ggU .PSU r (g + 1)).K := by
      rw [hGker]
      exact dvd_mul_of_dvd_left h7J _
    rcases Nat.lt_or_ge r 2 with hr2 | hr2
    ·
      obtain rfl : r = 1 := by omega
      norm_num at hMul
    rcases Nat.lt_or_ge r 3 with hr3 | hr3
    ·
      obtain rfl : r = 2 := by omega
      obtain rfl : g = 5 := by omega
      let ψ : ↥(CFSG.LieType.Universal.Unitary.SU σ 2) →* X := π
      have : Finite ↥(CFSG.LieType.Universal.Unitary.SU σ 2) := inferInstance
      exact rckIIp_false_of_alt_eight_of_GL_two
        (G := ↥(CFSG.LieType.Universal.Unitary.SU σ 2)) (X := X) (F := F) (ι := Fin 2)
        (by norm_num) (CFSG.LieType.Universal.Unitary.SU σ 2).subtype
        (Subgroup.subtype_injective _) ψ hA8
    rcases Nat.lt_or_ge r 4 with hr4 | hr4
    ·
      obtain rfl : r = 3 := by omega
      obtain rfl : g = 1 := by omega
      have hcardG : Nat.card (ggU .PSU 3 (1 + 1)).K = 62400 := by
        rw [hGcard]
        have h := CFSG.RankThree.PartOne.KFOUT3.card_suAnti_three (K := F) (f := 2)
          hc (by norm_num)
        norm_num at h
        exact h
      rw [hcardG] at h7G
      norm_num at h7G
    ·
      obtain rfl : r = 4 := by omega
      obtain rfl : g = 0 := by omega
      have hcardG : Nat.card (ggU .PSU 4 (0 + 1)).K = 25920 := by
        rw [hGcard]
        have h := CFSG.RankThree.PartOne.KFOUT3.card_suAnti (K := F) (f := 1)
          hc (by norm_num) (k := 4) (by norm_num)
        rw [Finset.prod_Icc_succ_top (a := 2) (b := 3) (by norm_num),
          Finset.prod_Icc_succ_top (a := 2) (b := 2) (by norm_num)] at h
        simp only [Finset.Icc_self, Finset.prod_singleton] at h
        norm_num at h
        exact_mod_cast h
      rw [hcardG] at h7G
      norm_num at h7G

end CFSG.StandardType.RCKC1
