module

public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619Contracts
public import CFSG.RankThree.PartOne.KFOUT3.L12Levi
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Card
public import CFSG.LocalAnalysis.GLTheoremA.PComp
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace S2MathAs3_1619Final

open CFSG CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag

theorem su3NoA1Eight_holds (f : ℕ) : SU3NoA1Eight f := by
  intro hf3 K hKfield hKfinite hKchar hU C hcomp
  have hf2 : 2 ≤ f := by omega
  have hQ : CFSG.IsQuasisimple ↥(unitarySU 2 f K 3) :=
    CFSG.RankThree.PartOne.KFOUT3.isQuasisimple_unitarySU_three hU hf2
  have hCtop : C = ⊤ :=
    CFSG.LocalAnalysis.GLTheoremA.eq_top_of_isComponentOf_of_isQuasisimple
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native
        ↥(unitarySU 2 f K 3)).2 hQ)
      ((CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open C ⊤).mp hcomp)
  subst hCtop
  intro hX
  have hbound :
      Nat.card (↥(⊤ : Subgroup ↥(unitarySU 2 f K 3)) ⧸
          Subgroup.center ↥(⊤ : Subgroup ↥(unitarySU 2 f K 3))) ≤ 504 := by
    unfold GGHasLabel at hX
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, CFSG.Assembly.LargeEvenRecipeLinear] at hX
    obtain ⟨F, hFfield, hFfinite, hFcard, hQF⟩ := hX
    letI : Field F := hFfield
    letI : Finite F := hFfinite
    obtain ⟨e₀⟩ := hQF
    have hF8 : Nat.card F = 8 := by
      rw [hFcard]
      norm_num
    have hsurj : Function.Surjective (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) F)) :=
      QuotientGroup.mk'_surjective _
    have hle : Nat.card (LargeEvenProj (LargeEvenSLGroup (Fin 2) F)) ≤
        Nat.card ↥(LargeEvenSLGroup (Fin 2) F) :=
      Nat.card_le_card_of_surjective _ hsurj
    have hSL : Nat.card ↥(LargeEvenSLGroup (Fin 2) F) = 504 := by
      have hcard : Nat.card ↥(LargeEvenSLGroup (Fin 2) F) =
          Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
        rw [CFSG.Assembly.largeEvenSLGroup_eq_statedSL 2]
        exact (Nat.card_congr
          (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).toEquiv).symm
      rw [hcard, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F, hF8]
      norm_num
    calc
      Nat.card (↥(⊤ : Subgroup ↥(unitarySU 2 f K 3)) ⧸
            Subgroup.center ↥(⊤ : Subgroup ↥(unitarySU 2 f K 3)))
          = Nat.card (LargeEvenProj (LargeEvenSLGroup (Fin 2) F)) :=
            Nat.card_congr e₀.toEquiv
      _ ≤ Nat.card ↥(LargeEvenSLGroup (Fin 2) F) := hle
      _ = 504 := hSL
  have hM : Nat.card ↥(unitarySU 2 f K 3) =
      (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) :=
    CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_unitarySU_three hU
  have hp : ((2 : ℕ) ^ f) ^ 3 = 2 ^ (3 * f) := by
    rw [← pow_mul]
    congr 1
    omega
  have hM_dvd : 2 ^ (3 * f) ∣ Nat.card ↥(unitarySU 2 f K 3) := by
    refine ⟨((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1), ?_⟩
    rw [hM, hp]
    ring
  have hZ : Nat.card (Subgroup.center ↥(unitarySU 2 f K 3)) = Nat.gcd 3 (2 ^ f + 1) :=
    CFSG.RankThree.PartOne.KFOUT3.card_center_unitarySU_three hU hf2
  have hZ_dvd : Nat.card (Subgroup.center ↥(unitarySU 2 f K 3)) ∣ 3 := by
    rw [hZ]
    exact Nat.gcd_dvd_left 3 _
  have hqcongr :
      Nat.card (↥(⊤ : Subgroup ↥(unitarySU 2 f K 3)) ⧸
          Subgroup.center ↥(⊤ : Subgroup ↥(unitarySU 2 f K 3)))
        = Nat.card (↥(unitarySU 2 f K 3) ⧸ Subgroup.center ↥(unitarySU 2 f K 3)) :=
    Nat.card_congr (QuotientGroup.congr _ _
      (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥(unitarySU 2 f K 3)) ≃* ↥(unitarySU 2 f K 3))
      (Subgroup.map_center_eq (Subgroup.topEquiv :
        ↥(⊤ : Subgroup ↥(unitarySU 2 f K 3)) ≃* ↥(unitarySU 2 f K 3)))).toEquiv
  have hprod :
      Nat.card (↥(unitarySU 2 f K 3) ⧸ Subgroup.center ↥(unitarySU 2 f K 3)) *
          Nat.card (Subgroup.center ↥(unitarySU 2 f K 3)) =
        Nat.card ↥(unitarySU 2 f K 3) :=
    (Subgroup.center ↥(unitarySU 2 f K 3)).card_eq_card_quotient_mul_card_subgroup.symm
  have hdiv :
      2 ^ (3 * f) ∣
        Nat.card (↥(unitarySU 2 f K 3) ⧸ Subgroup.center ↥(unitarySU 2 f K 3)) := by
    have hcop : Nat.Coprime (2 ^ (3 * f)) (Nat.card (Subgroup.center ↥(unitarySU 2 f K 3))) := by
      have hcop3 : Nat.Coprime (2 ^ (3 * f)) 3 := by
        rw [Nat.coprime_comm]
        rw [Nat.prime_three.coprime_iff_not_dvd]
        intro h3
        have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
        norm_num at h32
      exact hcop3.coprime_dvd_right hZ_dvd
    refine hcop.dvd_of_dvd_mul_right ?_
    rw [hprod]
    exact hM_dvd
  have hdivTop :
      2 ^ (3 * f) ∣ Nat.card (↥(⊤ : Subgroup ↥(unitarySU 2 f K 3)) ⧸
          Subgroup.center ↥(⊤ : Subgroup ↥(unitarySU 2 f K 3))) := by
    rw [hqcongr]
    exact hdiv
  have h512 :
      2 ^ 9 ∣ Nat.card (↥(⊤ : Subgroup ↥(unitarySU 2 f K 3)) ⧸
          Subgroup.center ↥(⊤ : Subgroup ↥(unitarySU 2 f K 3))) :=
    (pow_dvd_pow 2 (by omega : 9 ≤ 3 * f)).trans hdivTop
  have h512le :
      512 ≤ Nat.card (↥(⊤ : Subgroup ↥(unitarySU 2 f K 3)) ⧸
          Subgroup.center ↥(⊤ : Subgroup ↥(unitarySU 2 f K 3))) := by
    haveI : Nonempty (↥(⊤ : Subgroup ↥(unitarySU 2 f K 3)) ⧸
        Subgroup.center ↥(⊤ : Subgroup ↥(unitarySU 2 f K 3))) := ⟨1⟩
    have hpos : 0 < Nat.card (↥(⊤ : Subgroup ↥(unitarySU 2 f K 3)) ⧸
        Subgroup.center ↥(⊤ : Subgroup ↥(unitarySU 2 f K 3))) := Nat.card_pos
    have hle := Nat.le_of_dvd hpos h512
    norm_num at hle ⊢
    exact hle
  omega

end S2MathAs3_1619Final

end
