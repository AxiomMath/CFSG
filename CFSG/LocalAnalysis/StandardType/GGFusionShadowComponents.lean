module

public import CFSG.Assembly.Subnormal
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic
import CFSG.GroupTheory.ComponentFStarProd
import CFSG.GroupTheory.LocalCores.Components
import CFSG.CharacterTheory.Burnside
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
import CFSG.GroupTheory.OrderBelowSixtySolvable
import CFSG.Assembly.OrderReductions.OutsideAuxiliary
import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
import CFSG.LocalAnalysis.ComponentInitial.FixedComponentCorrespondence
public import CFSG.RankThree.PartOne.S10.ComponentOrbitSemisimpleLocalRankWitness
public import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18

public section

namespace CFSG.StandardType

open CFSG.Assembly
open scoped MatrixGroups

theorem largeEvenProj_su_three_two_isSolvable {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) : Group.IsSolvable (LargeEvenProj (LargeEvenSUGroup (Fin 3) F 2)) := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := by
    haveI : CharP F (ringChar F) := ringChar.charP F
    obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
    have h4 : Fintype.card F = 4 := by
      rw [← Nat.card_eq_fintype_card]; exact hF
    have hpow : ringChar F ^ (n : ℕ) = 4 := by rw [← hcard, h4]
    have hdvd2 : ringChar F ∣ 2 := by
      apply hp.dvd_of_dvd_pow (n := 2)
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hpow]
      exact dvd_pow_self _ n.ne_zero
    exact (ringChar.eq_iff).mp ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd2)
  have hSU : Nat.card (LargeEvenSUGroup (Fin 3) F 2) = 216 := by
    have h := CFSG.SectionRank.OddCover.card_statedSU_three (K := F) (p := 2) (f := 1)
      (by rw [hF]; norm_num)
    rw [pow_one] at h
    rw [show LargeEvenSUGroup (Fin 3) F 2 = CFSG.Open.StatedSU 3 2 F from
      CFSG.Assembly.largeEvenSUGroup_eq_statedSU 3 2, h]
    norm_num
  have hdvd : Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin 3) F 2)) ∣ 216 := by
    have h := Subgroup.card_quotient_dvd_card
      ((LargeEvenScalars (Fin 3) F).subgroupOf (LargeEvenSUGroup (Fin 3) F 2))
    have h2 : Nat.card ↥(LargeEvenSUGroup (Fin 3) F 2) = 216 := hSU
    rwa [h2] at h
  obtain ⟨y, z, hy, hz, hyz⟩ := Nat.dvd_mul.mp (show
    Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin 3) F 2)) ∣ 2 ^ 3 * 3 ^ 3 by
      rw [show (2 : ℕ) ^ 3 * 3 ^ 3 = 216 by norm_num]
      exact hdvd)
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hy
  obtain ⟨b, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hz
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    Nat.prime_two Nat.prime_three (by norm_num)
    (by rw [← Nat.card_eq_fintype_card]; exact hyz.symm)

end CFSG.StandardType
