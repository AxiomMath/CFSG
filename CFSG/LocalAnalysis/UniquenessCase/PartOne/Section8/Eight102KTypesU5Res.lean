module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.RankThree.PartOne.KF.R6LeviA
public import CFSG.RankThree.PartOne.KF.R56Final
import CFSG.RankThree.PartTwo.Sec21.Item222ProofStar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes

open Matrix Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSU)
open CFSG.RankThree.PartOne (suQ isCentralPQuot_suQ)
open CFSG.RankThree.PartOne.KFU (bA6 b6)
open CFSG.RankThree.PartOne.KFU (dvec5 diagU diagU_pow diagU_one diagU_val coe_bA6 coe_b6 gu5 su3Emb
  su3Emb_injective suBlock6 suBlock6_injective perfectResidual_centralizer_bA6
  perfectResidual_centralizer_b6 card_center_SU_three card_center_SL_two card_center_mulEquiv
  IsCentralPQuot)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem derInf8_centralizer_suQ (hK : Nat.card K = (2 ^ 2) ^ 2)
    {x : ↥(SU (unitaryInvolution K 2 2) 5)} (hx3 : x ^ 3 = 1)
    (hc : Nat.card (Subgroup.center (inSubgroup perfectResidual
      (Subgroup.centralizer ({x} : Set ↥(SU (unitaryInvolution K 2 2) 5))))) = 1) :
    Nonempty (F08.DerInf8 ((⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) ⊓
      Subgroup.centralizer (Subgroup.zpowers (suQ 5 hK x) :
        Set (StatedProj (StatedSU 5 (2 ^ 2) K)))) ≃*
      inSubgroup perfectResidual (Subgroup.centralizer
        ({x} : Set ↥(SU (unitaryInvolution K 2 2) 5)))) := by
  have hq : IsCentralPQuot 3 (suQ 5 hK) :=
    isCentralPQuot_suQ Nat.prime_three (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hK
  have hC : (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) ⊓
      Subgroup.centralizer (Subgroup.zpowers (suQ 5 hK x) :
        Set (StatedProj (StatedSU 5 (2 ^ 2) K))) =
      Subgroup.centralizer ({suQ 5 hK x} :
        Set (StatedProj (StatedSU 5 (2 ^ 2) K))) := by
    rw [top_inf_eq, CFSG.RankThree.PartTwo.Sec21.Item222Proof.centralizer_zpowers_eq]
  set H := inSubgroup perfectResidual (Subgroup.centralizer
    ({x} : Set ↥(SU (unitaryInvolution K 2 2) 5))) with hH
  have hmap : inSubgroup perfectResidual (Subgroup.centralizer
      ({suQ 5 hK x} : Set (StatedProj (StatedSU 5 (2 ^ 2) K)))) = H.map (suQ 5 hK) := by
    rw [hH, CFSG.RankThree.PartOne.KFU.map_inSubgroup_perfectResidual,
      hq.map_centralizer hx3]
  have hiso : Nonempty (inSubgroup perfectResidual (Subgroup.centralizer
      ({suQ 5 hK x} : Set (StatedProj (StatedSU 5 (2 ^ 2) K)))) ≃* H) := by
    have hbot : Subgroup.center H = ⊥ := Subgroup.card_eq_one.mp hc
    have hinj : Function.Injective ((suQ 5 hK).subgroupMap H) := by
      rw [injective_iff_map_eq_one]
      intro z hz
      have hz' : (z : ↥(SU (unitaryInvolution K 2 2) 5)) ∈ (suQ 5 hK).ker :=
        MonoidHom.mem_ker.mpr (congrArg Subtype.val hz)
      have hzc : (z : ↥(SU (unitaryInvolution K 2 2) 5)) ∈
          Subgroup.center ↥(SU (unitaryInvolution K 2 2) 5) := hq.central hz'
      have hzH : z ∈ Subgroup.center H := by
        rw [Subgroup.mem_center_iff]
        intro w
        exact Subtype.ext (Subgroup.mem_center_iff.mp hzc w)
      rw [hbot] at hzH
      exact hzH
    exact ⟨(MulEquiv.subgroupCongr hmap).trans
      (MulEquiv.ofBijective _ ⟨hinj, (suQ 5 hK).subgroupMap_surjective H⟩).symm⟩
  change Nonempty (inSubgroup perfectResidual ((⊤ : Subgroup
    (StatedProj (StatedSU 5 (2 ^ 2) K))) ⊓
      Subgroup.centralizer (Subgroup.zpowers (suQ 5 hK x) :
        Set (StatedProj (StatedSU 5 (2 ^ 2) K)))) ≃* H)
  rw [hC]
  exact hiso

theorem nonempty_derInf8_bA6 (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ) (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1) :
    Nonempty (F08.DerInf8 ((⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) ⊓
      centralizer (zpowers (suQ 5 hK (bA6 (unitaryInvolution K 2 2) ζ hζ)) :
        Set (StatedProj (StatedSU 5 (2 ^ 2) K)))) ≃* SU (unitaryInvolution K 2 2) 3) := by
  have h2 : ζ ^ 2 ≠ 1 := by
    intro h
    apply h1
    calc ζ = ζ ^ 3 * (ζ ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h, inv_one, one_mul]
  have hx3 : bA6 (unitaryInvolution K 2 2) ζ hζ ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, coe_bA6, diagU_pow]
    have hd : dvec5 (1 : Kˣ) ζ ^ 3 = 1 := by
      funext i
      fin_cases i <;> simp [dvec5, h3]
    rw [hd, diagU_one]
    rfl
  have hx1 : bA6 (unitaryInvolution K 2 2) ζ hζ ≠ 1 := by
    intro h
    refine h1 (Units.ext ?_)
    have h11 := congrArg (fun g : ↥(SU (unitaryInvolution K 2 2) 5) => gu5 g 1 1) h
    simpa [gu5, coe_bA6, diagU_val, dvec5] using h11
  have hH : inSubgroup perfectResidual (Subgroup.centralizer
      ({bA6 (unitaryInvolution K 2 2) ζ hζ} :
        Set ↥(SU (unitaryInvolution K 2 2) 5))) =
      (su3Emb (unitaryInvolution K 2 2)).range :=
    perfectResidual_centralizer_bA6 hK le_rfl hζ h1 h2
  have hc : Nat.card (Subgroup.center (inSubgroup perfectResidual
      (Subgroup.centralizer ({bA6 (unitaryInvolution K 2 2) ζ hζ} :
        Set ↥(SU (unitaryInvolution K 2 2) 5))))) = 1 := by
    rw [hH, card_center_mulEquiv
      (MonoidHom.ofInjective (su3Emb_injective (unitaryInvolution K 2 2))).symm,
      card_center_SU_three hK le_rfl]
    norm_num
  obtain ⟨e⟩ := derInf8_centralizer_suQ hK hx3 hc
  rw [hH] at e
  exact ⟨e.trans (MonoidHom.ofInjective
    (su3Emb_injective (unitaryInvolution K 2 2))).symm⟩

theorem nonempty_derInf8_b6 (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ) (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1) :
    Nonempty (F08.DerInf8 ((⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) ⊓
      centralizer (zpowers (suQ 5 hK (b6 (unitaryInvolution K 2 2) ζ hζ)) :
        Set (StatedProj (StatedSU 5 (2 ^ 2) K)))) ≃* SpecialLinearGroup (Fin 2) K) := by
  have h2 : ζ ^ 2 ≠ 1 := by
    intro h
    apply h1
    calc ζ = ζ ^ 3 * (ζ ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h, inv_one, one_mul]
  have hσσ : ∀ c, unitaryInvolution K 2 2 (unitaryInvolution K 2 2 c) = c :=
    unitaryInvolution_involutive (p := 2) (f := 2) hK
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  have hx3 : b6 (unitaryInvolution K 2 2) ζ hζ ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, coe_b6, diagU_pow]
    have hd : dvec5 ζ ζ ^ 3 = 1 := by
      funext i
      fin_cases i <;> simp [dvec5, h3]
    rw [hd, diagU_one]
    rfl
  have hx1 : b6 (unitaryInvolution K 2 2) ζ hζ ≠ 1 := by
    intro h
    refine h1 (Units.ext ?_)
    have h00 := congrArg (fun g : ↥(SU (unitaryInvolution K 2 2) 5) => gu5 g 0 0) h
    simpa [gu5, coe_b6, diagU_val, dvec5] using h00
  have hH : inSubgroup perfectResidual (Subgroup.centralizer
      ({b6 (unitaryInvolution K 2 2) ζ hζ} :
        Set ↥(SU (unitaryInvolution K 2 2) 5))) =
      (suBlock6 (unitaryInvolution K 2 2) hσσ).range :=
    perfectResidual_centralizer_b6 (unitaryInvolution K 2 2) hσσ hK4 hζ h1 h2
  have hc : Nat.card (Subgroup.center (inSubgroup perfectResidual
      (Subgroup.centralizer ({b6 (unitaryInvolution K 2 2) ζ hζ} :
        Set ↥(SU (unitaryInvolution K 2 2) 5))))) = 1 := by
    rw [hH, card_center_mulEquiv
      (MonoidHom.ofInjective (suBlock6_injective (unitaryInvolution K 2 2) hσσ)).symm,
      card_center_SL_two]
  obtain ⟨e⟩ := derInf8_centralizer_suQ hK hx3 hc
  rw [hH] at e
  exact ⟨e.trans (MonoidHom.ofInjective
    (suBlock6_injective (unitaryInvolution K 2 2) hσσ)).symm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes
