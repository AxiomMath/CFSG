module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvable
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Strong
import CFSG.LocalAnalysis.UniquenessCase.UC22S213PrimeRank
import CFSG.LocalAnalysis.UniquenessCase.UC22S213PrimeSylow
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Inner
import CFSG.LocalAnalysis.UniquenessCase.UC22P21d
import CFSG.LocalAnalysis.UniquenessCase.UC22P20a
import CFSG.LocalAnalysis.UniquenessCase.UC22Sec7Three
import CFSG.LocalAnalysis.UniquenessCase.UC6R869MConj
import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizingRank
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Setup
import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt SigmaOne4)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (Conclusion76 StronglyEmbeddedFive StronglyEmbeddedSolvable StronglyEmbeddedThree
    BadNoStrongThree)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

theorem uc22s213_not_centralizesBar_of_prime (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (hσ : S.InMSigma) (hPart : PartIAt S.M) (hSE : StronglyEmbeddedFive)
    (hSS : StronglyEmbeddedSolvable) (hK3 : StronglyEmbeddedThree) (hB : BadNoStrongThree)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic) (Ch : Choice2011 G)
    (hH : H1930 (UC6.dataOfSetup4 hS hU S)) (c : Ctx21 (UC6.dataOfSetup4 hS hU S) Ch)
    {L : Subgroup G} (hL : L ∈ calC S.M) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hZ : ¬ r ∣ Nat.card (center (Bar2 L)))
    (h2 : 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (BarInf L)))
    (hab : ∀ P : Sylow r (BarInf L), IsMulCommutative (P : Subgroup (BarInf L)))
    (hout : ¬ r ∣ Nat.card (Outer (BarInf L))) (h3600 : 3600 < Nat.card (BarInf L))
    {a : G} (ha : a ∈ c.B) (hpr : (orderOf a).Prime)
    (hN : ∀ p ∈ uniqueFourSigma S.M,
      CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ S.M) ≤ 1) :
    ¬ CentralizesBar a L := by
  intro haL
  have hr2 : r ≠ 2 := by omega
  have : Fact r.Prime := ⟨hr⟩
  have hodd := uc22p21d_odd_orderOf_of_mem_calB1 c.hB ha
  have hLM : L ≤ S.M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hrL : 2 ≤ CFSG.Open.pRank r L := uc22s213_pRank_barInf_of_prime hL.2.2 hr hr2 hZ ▸ h2
  have hrσ : r ∉ uniqueFourSigma S.M := fun h => by
    have := uc22s213_pRank_le_one_of_centralizesBar hLM hodd hpr haL hr hr2 (hN r h)
    omega
  have hMN := uc22s213_le_normalizer_of_not_mem_sigma hU S.maxLocal hL hr hr2 hrL hZ hrσ
  obtain ⟨E, hEL, hEel, hEcard⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hr hrL
  obtain ⟨R, hR, hER⟩ := uc22s213_exists_sylow_le_centralizer_of_prime hLM hMN hL.2.2 hr hr2 hZ
    hab hout hEL hEel.isPGroup
  have hpp : S.p.Prime := S.hp.1.1
  have hp2 : S.p ≠ 2 := S.hp.1.2.1
  have : Fact S.p.Prime := ⟨hpp⟩
  have hsp := PartOne.Section8.isStronglyPEmbedded_of_mem_sigma_of_calC hS hU S hL S.hp
  have h76 : Conclusion76 S.M S.p := by
    by_cases h3 : 3 ∈ uniqueFourBeta G
    · exact PartOne.Section7.c76Three_of_inputs hSE hK3 hB hS hU S hσ h3 S.p S.hp hsp
    · exact UC6.conclusion76_dataOfSetup4 hSE hS hU S h3 S.hp hsp
  obtain ⟨Bp, hBM, hBel, hBc⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hpp (UC6.four_le_pRank_of_sigma S.hp)
  have hLtop : L ≠ ⊤ :=
    ne_top_of_le_ne_top (uc22p20a_M_ne_top (UC6.dataOfSetup4 hS hU S)) hLM
  have hF := UC6.R869S.two_le_pRank_centralizer_of_pRank_mulAut hLM hpp hp2
    (UC6.R869S.pRank_mulAut_bar2_le_two hOut (hS.kProper.isKGroup L hLtop) hL.2.2 hpp hp2
      (uc22s213_pRank_le_one_of_centralizesBar hLM hodd hpr haL hpp hp2 (hN S.p S.hp)))
    hBM (hBM.trans hMN) hBel hBc hr hr2 hEL hEel.isPGroup
  have hΓ : CFSG.Open.rankThreeGamma 1 r E ≤ S.M :=
    PartOne.Section7.rankThreeGamma_le_of_two_le_pRank_inf_centralizer hsp h76 (hEL.trans hLM)
      hEel.isPGroup (CFSG.SectionRank.le_pRank hr.one_lt le_rfl hEel hEcard) hF
  have hsub : uniqueFourSigma S.M ⊆ SigmaOne4 G := fun q hq =>
    ⟨hq.1, S.M, S.maxLocal, hq,
      PartOne.Section8.isStronglyPEmbedded_of_mem_sigma_of_calC hS hU S hL hq⟩
  have hspr : IsStronglyPEmbedded r S.M :=
    hPart.2.1 hsub r hr hr2 hrσ R hR E hER hEel hEcard hΓ
  have hrB : r ∣ Nat.card (BarInf L) := by
    have h1 := CFSG.GroupTheory.dvd_card_of_one_le_pRank hr
      (H := (⊤ : Subgroup (BarInf L))) (by omega)
    rwa [Subgroup.card_top] at h1
  exact uc22s213_not_centralizesBar_of_strong hS hU S hσ hPart hSE hSS hB Ch hH c hL hr hr5 hspr
    hrL hrB h3600 ha hpr haL

end CFSG.LocalAnalysis.UniquenessCase.UC22
