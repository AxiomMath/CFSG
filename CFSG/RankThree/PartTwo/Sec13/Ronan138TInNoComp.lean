module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138TInCent
public import CFSG.RankThree.PartTwo.Sec13.Ronan138TInHJ
public import CFSG.RankThree.PartTwo.Sec13.Ronan138TInCase
import CFSG.RankThree.PartTwo.Sec13.Item13Prod
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec4.Item424ProofInner

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138T

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem noComp
    (hspor : SporadicModels131) (h415 : Sec4.Item4_15) (h48 : Sec4.Item4_8)
    (hsetAt : Item13SetupAt) (h133 : Item133) (h131 : Item131)
    {A L E F : Subgroup G} {c x y t : G} (hfr : Ronan138S.Frame138Base A L E F c x y t)
    (hdΩ : Subgroup.zpowers ⁅x, y⁆ ∉ omegaA E)
    {n : G} (hnC : n ∈ Subgroup.centralizer (E : Set G)) (hnk : ∃ k : ℕ, n ^ 3 ^ k = 1)
    (hn3 : n ^ 3 ∈ Subgroup.zpowers ⁅x, y⁆) (hn31 : n ^ 3 ≠ 1)
    {e : G} {K : Subgroup G} (heΩ : Subgroup.zpowers e ∈ omegaA E) (hK : K ∈ lA E e)
    (heF : e ∉ F) :
    thetaComponents 3 ↥(K ⊓ Subgroup.centralizer ({c} : Set G)) = ∅ := by
  have hH := hfr.hH
  have hcΩ := Ronan138S.zpowers_not_mem_omegaA hsetAt hH hfr.hdE hfr.hdL hfr.hdc
  have hdK := comm_mem_of_not_mem h48 hfr heΩ hK heF
  have hH' := hH
  obtain ⟨h, -, hcE, hE3, -, -, -, hST, -⟩ := hH'
  have hXF := Ronan138S.mem_partTwoF_of_hyp138 hfr.hH
  have hD : Sec13Data G E e K :=
    { h.toPartTwoStanding with
      partTwoS_eq := h.partTwoS_eq
      mem_partTwoF := hXF.1
      not_mem_partTwoT := hXF.2
      zpowers_mem_omegaA := heΩ
      mem_lA := hK }
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := hK.2.1 hcE
  have hc3 : c ^ 3 = 1 := hE3.2 c hcE
  refine Ronan138S.thetaComponents_eq_empty_of_isSolvable hcN hc3 ?_
  have hτ3 : Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨c, hcN⟩) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow]
    have : (⟨c, hcN⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hc3)
    rw [this, map_one, map_one]
  have hτ1 : Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨c, hcN⟩) ≠ 1 := by
    intro h1
    have hcC : c ∈ Sec4.thetaQuotCentralizer K :=
      Sec4.Item424Proof.mem_thetaQuotCentralizer_iff_eq_one.mpr ⟨hcN, h1⟩
    have hCE := sectionCentralizer_eq_inf hK.2.1
    rw [hK.2.2.1] at hCE
    have hc' : c ∈ ((E ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨hcE, hcC⟩
    rw [← hCE] at hc'
    have heE : e ∈ E := (zpowers_mem_omegaA_iff.mp heΩ).1
    have he1 : e ≠ 1 := hD.ne_one
    have heq := Ronan138S.zpowers_eq_of_mem hc3 hfr.hc1 (hfr.hE3 e heE) he1 hc'
    apply heF
    have he : e ∈ Subgroup.zpowers c := heq ▸ Subgroup.mem_zpowers e
    exact Subgroup.zpowers_le.mpr hfr.hcF he
  rcases h133 G E e K hD hST with h1 | ⟨-, hφ, -⟩ | ⟨hirr, -, -, -, -, -, -, hφ3, hK3⟩ |
      hPGLK | hφ | hHJ
  · exact (false_of_case1 hfr hcΩ hdΩ heΩ h1).elim
  · obtain ⟨φ⟩ := hφ
    obtain ⟨ψ⟩ := nonempty_thetaQuot_equiv hD isPerfect_center_alt7.1 φ
    exact Ronan138S.isSolvable_eqLocus_alt7 ψ hτ3 hτ1
  · rcases hK3 with hL3 | hψ | hψ
    · exact centL3 h48 hfr heΩ hK heF hL3 hφ3 hirr hcN
    · obtain ⟨ψ⟩ := hψ
      exact Ronan138S.isSolvable_eqLocus_alt7 ψ hτ3 hτ1
    · obtain ⟨ψ⟩ := hψ
      exact Ronan138S.isSolvable_eqLocus_m22 ψ hτ3 hτ1
  · exact centPGL h131 hspor hfr heΩ hK heF hdK hPGLK hcN
  · obtain ⟨φ⟩ := hφ
    obtain ⟨ψ⟩ := nonempty_thetaQuot_equiv hD hspor.2.1.1 φ
    exact Ronan138S.isSolvable_eqLocus_m12 ψ hτ3 hτ1
  · exact (false_of_hj_torus hspor h415 hD hHJ hdΩ hfr.hd3 hfr.hd1 hfr.hdE hnC hnk hn3
      hn31).elim

end CFSG.RankThree.PartTwo.Sec13.Ronan138T
