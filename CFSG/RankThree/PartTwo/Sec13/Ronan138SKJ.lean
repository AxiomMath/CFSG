module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138SKSetup
import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofBalTools
import CFSG.RankThree.PartTwo.Sec8.Item87ProofTools
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.GroupTheory.ConjugatePairSubnormality
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SKIn

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_of_mem_omegaA (h48 : Sec4.Item4_8) (hNC : Step138NoCompF) (hKF : KF138TypeTwo)
    {A L E F : Subgroup G} {c x y t : G} (hfr : Frame138 A L E F c x y t) {e : G}
    {K : Subgroup G} (heΩ : Subgroup.zpowers e ∈ omegaA E) (hK : K ∈ lA E e) : e ∈ F := by
  by_contra heF
  have hH := hfr.hH
  have hD := hH.1
  have heE : e ∈ E := (zpowers_mem_omegaA_iff.mp heΩ).1
  have he3 : e ^ 3 = 1 := hfr.hE3 e heE
  have he1 : e ≠ 1 := by
    rintro rfl
    have := (zpowers_mem_omegaA_iff.mp heΩ).2.1
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at this
    norm_num at this
  have hcLF : Subgroup.zpowers c ⊔ (E ⊓ L) ≤ F := by
    refine sup_le (Subgroup.zpowers_le.mpr hfr.hcF) ?_
    rw [hfr.hEL]
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mp hfr.hdZ).2
  obtain ⟨hdJ, hJq⟩ := hKF G A c L E hH hfr.hPGL e heE (fun h => heF (hcLF h))
  set J := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({e} : Set G)) with hJdef
  have hdJ' : ⁅x, y⁆ ∈ J := hdJ (hfr.hEL ▸ Subgroup.mem_zpowers _)
  have hL := hD.mem_thetaComponentsAt
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({e} : Set G)) :=
    hD.toPartTwoStanding.toTheoremFourHyp.sectionFourHyp
      (Sec6.centralizer_ne_top_of_ne_one hD.toPartTwoStanding.toTheoremFourHyp he1)
  have hE27' : Late.IsE27 E := ⟨hH.2.2.2.1, hfr.hE27⟩
  obtain ⟨K', hK', hJK'⟩ := Sec14.exists_mem_thetaComponentsAt_le_residual h48 hG4 hE27' hfr.hcE
    heE hfr.hc1 hL hJq
  have hKK' : K' = K := by
    by_contra hne
    have hK'K : K' ≤ Sec4.thetaQuotCentralizer K := by
      rw [thetaComponentsAt_eq_thetaComponentsIn] at hK'
      have hK1 := hK.1
      rw [thetaComponentsAt_eq_thetaComponentsIn] at hK1
      exact Sec14.BalTools.le_thetaQuotCentralizer_of_ne_in hK' hK1 hne
    have hdC : ⁅x, y⁆ ∈ Sec4.thetaQuotCentralizer K := hK'K (hJK' hdJ')
    have hCE := sectionCentralizer_eq_inf hK.2.1
    rw [hK.2.2.1] at hCE
    have hd' : ⁅x, y⁆ ∈ ((E ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨hfr.hdE, hdC⟩
    rw [← hCE] at hd'
    have heq := zpowers_eq_of_mem hfr.hd3 hfr.hd1 he3 he1 hd'
    apply heF
    have he : e ∈ Subgroup.zpowers ⁅x, y⁆ := heq ▸ Subgroup.mem_zpowers e
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mp hfr.hdZ).2 he
  subst hKK'
  have hJL : J ≤ L ⊓ Subgroup.centralizer ({e} : Set G) := Subgroup.map_subtype_le _
  have hJc : J ≤ Subgroup.centralizer ({c} : Set G) :=
    hJL.trans (inf_le_left.trans (Sec6.le_centralizer_of_mem_thetaComponentsAt hL))
  have hJKc : J ≤ K' ⊓ Subgroup.centralizer ({c} : Set G) := le_inf hJK' hJc
  have hKe : K' ⊓ Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({e} : Set G) :=
    le_inf inf_le_right (inf_le_left.trans (Sec6.le_centralizer_of_mem_thetaComponentsAt hK.1))
  have hsn := CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hKe
    (Sec8.Item87Proof.isSubnormal_residual (y := e) hL)
  have hJmem : J ∈ thetaComponentsIn (K' ⊓ Subgroup.centralizer ({c} : Set G)) :=
    Sec6.mem_thetaComponentsIn_of hJKc (Sec6.isPerfect_inSubgroup_perfectResidual _) hsn hJq
  obtain ⟨T, hT, -⟩ := hJmem
  have hempty := hNC G A c L E hH hfr.hPGL F hfr.hF e K' heΩ hK heF
  rw [hempty] at hT
  exact hT

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
