module

public import CFSG.RankThree.PartOne.KF.R6LeviA
public import CFSG.RankThree.PartOne.KF.R56Final
import CFSG.RankThree.PartTwo.KFacts.KS222U5
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
import CFSG.RankThree.PartOne.KF.LayerModelRow
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.CentralizerSup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes

open CFSG.Open Subgroup
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSU)
open CFSG.RankThree.PartOne (suQ isCentralPQuot_suQ)
open CFSG.RankThree.PartOne.KFU (IsCentralPQuot bA6 coe_bA6 phiA6 ker_phiA6 su3Emb su3Emb_injective
  su3Emb_mem_centralizer dvec5 diagU_pow diagU_one)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem bA6_pow_three {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ) (h3 : ζ ^ 3 = 1) :
    bA6 (unitaryInvolution K 2 2) ζ hζ ^ 3 = 1 := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_pow, coe_bA6]
  have hd : (dvec5 (1 : Kˣ) ζ) ^ 3 = 1 := by
    funext i
    fin_cases i <;> simp [dvec5, h3]
  rw [diagU_pow, hd, diagU_one]
  rfl

omit [Finite K] [CharP K 2] in
private theorem zeta_sq_ne_one {ζ : Kˣ} (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1) : ζ ^ 2 ≠ 1 := by
  intro h
  apply h1
  have h4 : ζ ^ 3 = ζ ^ 2 * ζ := pow_succ ζ 2
  rw [h3, h, one_mul] at h4
  exact h4.symm

private theorem card_ker_suQ_five (hK : Nat.card K = (2 ^ 2) ^ 2) :
    Nat.card (suQ 5 hK).ker = 5 := by
  have hker : (suQ 5 hK).ker =
      ((StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ 2) K)).comap
        (CFSG.LieType.Universal.Unitary.equivStatedSU hK 5).toMonoidHom := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    exact QuotientGroup.eq_one_iff _
  rw [hker, Subgroup.comap_equiv_eq_map_symm',
    Subgroup.card_map_of_injective
      (CFSG.LieType.Universal.Unitary.equivStatedSU hK 5).symm.injective,
    (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (by norm_num : 1 ≤ 5)).2.2]
  norm_num

private theorem card_centralizer_bA6_dvd (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ) (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1) :
    Nat.card (Subgroup.centralizer ({bA6 (unitaryInvolution K 2 2) ζ hζ} :
      Set ↥(SU (unitaryInvolution K 2 2) 5))) ∣ 936000 := by
  let C : Subgroup ↥(SU (unitaryInvolution K 2 2) 5) :=
    Subgroup.centralizer ({bA6 (unitaryInvolution K 2 2) ζ hζ} :
      Set ↥(SU (unitaryInvolution K 2 2) 5))
  let φ : C →* Kˣ := phiA6 (unitaryInvolution K 2 2) hζ h1 h2
  have hcard : Nat.card C = Nat.card φ.range * Nat.card φ.ker := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (φ.ker)
    have h2 : Nat.card (C ⧸ φ.ker) = Nat.card φ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    rwa [h2] at h
  have hker : Nat.card φ.ker = 62400 := by
    rw [ker_phiA6 (unitaryInvolution K 2 2) hζ h1 h2]
    have hle : (su3Emb (unitaryInvolution K 2 2)).range ≤ C := by
      rintro _ ⟨u, rfl⟩
      exact su3Emb_mem_centralizer (unitaryInvolution K 2 2) hζ u
    have h1' : Nat.card ((su3Emb (unitaryInvolution K 2 2)).range.subgroupOf C) =
        Nat.card (su3Emb (unitaryInvolution K 2 2)).range :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle)
    have h2' : Nat.card (su3Emb (unitaryInvolution K 2 2)).range =
        Nat.card ↥(SU (unitaryInvolution K 2 2) 3) :=
      (Nat.card_congr (MonoidHom.ofInjective
        (su3Emb_injective (unitaryInvolution K 2 2))).toEquiv).symm
    rw [h1', h2']
    have hc := CFSG.LocalAnalysis.EvenBN.GMSK.card_of_lieModel_PSU3
      (CFSG.RankThree.PartOne.lieModel_of_scm_psu
        (CFSG.RankThree.PartTwo.Sec21.U5Lines.statedClassicalModel_SU_three hK))
    norm_num at hc ⊢
    exact hc
  have hrange : Nat.card φ.range ∣ 15 := by
    have hK15 : Nat.card Kˣ = 15 := by
      rw [Nat.card_units, hK]
      norm_num
    rw [← hK15]
    exact Subgroup.card_subgroup_dvd_card φ.range
  have h936 : (936000 : ℕ) = 62400 * 15 := by norm_num
  rw [hcard, hker, h936]
  simpa [Nat.mul_comm] using Nat.mul_dvd_mul_left 62400 hrange

private theorem card_map_centralizer_bA6_dvd (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ) (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1) :
    Nat.card ((Subgroup.centralizer ({bA6 (unitaryInvolution K 2 2) ζ hζ} :
      Set ↥(SU (unitaryInvolution K 2 2) 5))).map (suQ 5 hK)) ∣ 187200 := by
  let C : Subgroup ↥(SU (unitaryInvolution K 2 2) 5) :=
    Subgroup.centralizer ({bA6 (unitaryInvolution K 2 2) ζ hζ} :
      Set ↥(SU (unitaryInvolution K 2 2) 5))
  let ε : ↥(SU (unitaryInvolution K 2 2) 5) →*
      StatedProj (StatedSU 5 (2 ^ 2) K) := suQ 5 hK
  have hq : IsCentralPQuot 3 ε :=
    isCentralPQuot_suQ Nat.prime_three (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hK
  have hcardC : Nat.card C ∣ 936000 := card_centralizer_bA6_dvd hK hζ h1 h2
  have hker5 : Nat.card ε.ker = 5 := card_ker_suQ_five hK
  have hkerle : ε.ker ≤ C := hq.central.trans (Subgroup.center_le_centralizer _)
  have hkerC : Nat.card (ε.ker.subgroupOf C) = 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerle).toEquiv, hker5]
  have hcardmap : Nat.card (C.map ε) * Nat.card (ε.ker.subgroupOf C) = Nat.card C := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ((ε.subgroupMap C).ker)
    have hq1 : Nat.card (C ⧸ (ε.subgroupMap C).ker) = Nat.card (C.map ε) := by
      have h2 : Nat.card (C ⧸ (ε.subgroupMap C).ker) =
          Nat.card ((ε.subgroupMap C).range) :=
        Nat.card_congr (QuotientGroup.quotientKerEquivRange (ε.subgroupMap C)).toEquiv
      rwa [MonoidHom.range_eq_top.mpr (MonoidHom.subgroupMap_surjective ε C),
        Subgroup.card_top] at h2
    have hq2 : Nat.card ((ε.subgroupMap C).ker) = Nat.card (ε.ker.subgroupOf C) := by
      rw [Subgroup.ker_subgroupMap]
    rw [hq1, hq2] at h
    exact h.symm
  have h5map : 5 * Nat.card (C.map ε) ∣ Nat.card C := by
    rw [← hcardmap, hkerC, Nat.mul_comm]
  have h5dvd : 5 * Nat.card (C.map ε) ∣ 936000 := h5map.trans hcardC
  have h936 : (936000 : ℕ) = 5 * 187200 := by norm_num
  rw [h936] at h5dvd
  exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 5)).mp h5dvd

theorem pRank_five_centralizer_bA6_le (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ) (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1) :
    Open.pRank 5 ((⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) ⊓
      centralizer (zpowers (suQ 5 hK (bA6 (unitaryInvolution K 2 2) ζ hζ)) :
        Set (StatedProj (StatedSU 5 (2 ^ 2) K)))) ≤ 2 := by
  have h2 : ζ ^ 2 ≠ 1 := zeta_sq_ne_one h1 h3
  have hx3 : bA6 (unitaryInvolution K 2 2) ζ hζ ^ 3 = 1 := bA6_pow_three hζ h3
  have hq : IsCentralPQuot 3 (suQ 5 hK) :=
    isCentralPQuot_suQ Nat.prime_three (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hK
  have htop : (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) ⊓
      centralizer (zpowers (suQ 5 hK (bA6 (unitaryInvolution K 2 2) ζ hζ)) :
        Set (StatedProj (StatedSU 5 (2 ^ 2) K))) =
      (Subgroup.centralizer ({bA6 (unitaryInvolution K 2 2) ζ hζ} :
        Set ↥(SU (unitaryInvolution K 2 2) 5))).map (suQ 5 hK) := by
    rw [top_inf_eq, CFSG.centralizer_zpowers_eq_centralizer_singleton,
      ← hq.map_centralizer hx3]
  rw [htop]
  have hdvd := card_map_centralizer_bA6_dvd hK hζ h1 h2
  refine CFSG.SectionRank.pRank_le (by norm_num : 1 < 5) (fun E hEH hE => ?_)
  have hEdvd : Nat.card E ∣ 187200 := by
    have h1' : Nat.card (E.subgroupOf ((Subgroup.centralizer
        ({bA6 (unitaryInvolution K 2 2) ζ hζ} :
          Set ↥(SU (unitaryInvolution K 2 2) 5))).map (suQ 5 hK))) = Nat.card E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv
    rw [← h1']
    exact (Subgroup.card_subgroup_dvd_card _).trans hdvd
  obtain ⟨n, hn⟩ := CFSG.Open.IsElemAbelian.isPGroup hE |>.exists_card_dvd_pow
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 hn
  have h5k : 5 ^ k ∣ 187200 := hk ▸ hEdvd
  have hk2 : k ≤ 2 := by
    by_contra h
    have h3' : 3 ≤ k := by omega
    exact (by norm_num : ¬ 5 ^ 3 ∣ 187200) ((pow_dvd_pow 5 h3').trans h5k)
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num : 0 < 5) hk2

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes
