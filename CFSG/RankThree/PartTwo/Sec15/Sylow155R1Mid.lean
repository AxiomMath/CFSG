module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Defs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1MidDefs
public import CFSG.RankThree.PartTwo.Sec17.RouteWire14
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Setup
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cor141
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1SzCent
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1MidGrp
import CFSG.RankThree.PartTwo.Sec15.Sylow155F1Z
import CFSG.RankThree.PartTwo.Sec14.Concl143Std
public import CFSG.RankThree.PartTwo.Sec15.Gagen155Y1Defs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155F1
public import CFSG.RankThree.PartTwo.Sec4.Census.Open46
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem res1_layerOddPreimage_le_centralizer {A : Subgroup G} {c : G} {L : Subgroup G}
    (h1444 : Item1444 A (lB A)) (hSz : KFacts.KPSz)
    (hSz3 : CFSG.LocalAnalysis.UniquenessCase.UCK.SzOrder3Aut)
    (hS : Sec14Std G A c L) (h146 : Item146 A (lB A))
    {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T) (hE : End155N A X K Y M T P)
    (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G)) :
    layerOddPreimage (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      Subgroup.centralizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAM : A ≤ M := fun a ha => hC.mem_m.2 (Subgroup.mem_sup_left ha)
  set H := delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X)) with hHdef
  obtain ⟨hHQ, hRH, -, -⟩ := Sylow155B1.delta_host_facts hS h146 hC hE hRP
    (Sylow155S.sup_mem_invariant hC hE hRP) (Sylow155S.sup_le_u155 hE hRP)
    (Sylow155S.p_le_normalizer_sup hE) le_sup_left
  have hHI : H ≤ delta A (lB A) M :=
    (delta_le _).trans ((Sylow155S.sup_le_u155 hE hRP).trans inf_le_left)
  have hHM : H ≤ M := hHI.trans (delta_le M)
  obtain ⟨-, hIZ⟩ := Sylow155B1.delta_pCore_facts hS h146 hC
  have hZH : delta A (lB A) (CFSG.Open.pCoreOf 2 M) ≤ H :=
    (Sylow155B1.delta_pCore_le_r hS h146 hC hE hIX).trans hRH
  have hZ2 : IsPGroup 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 M)) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le (delta_le _)
  have hEZ := layerOddPreimage_le_centralizer hZ2 hZH (hHI.trans hIZ)
  have hAH : A ≤ Subgroup.normalizer (H : Set G) := hHQ.1.2.2
  have hH3 : ¬ 3 ∣ Nat.card H := (isPiSubgroup_piCompl_iff Nat.prime_three H).mp hHQ.1.2.1
  have hAV : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
    hAM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have hC0 : ∀ S : Subgroup G, S ≤ layerOddPreimage H → Odd (Nat.card S) →
      A ≤ Subgroup.normalizer (S : Set G) → S ≤ Subgroup.centralizer (A : Set G) :=
    fun S hSE hSodd hAS =>
      Sylow155F1.le_centralizer_of_le_centralizer_delta hS.isE27' h1444
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) hAV hHQ
        (hHM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
        (fun g hg hgV hodd => Sylow155F1.eq_one_of_mem_centralizer_pCoreOf hS hC (hHM hg) hgV hodd)
        (hSE.trans (layerOddPreimage_le_self H)) (hSE.trans hEZ) hSodd hAS
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hS.mem_partTwoF.1.2
  exact layerOddPreimage_le_centralizer_of_szSections hA3 hAH
    (hAH.trans (normalizer_le_normalizer_pPrimeCoreOf_two H))
    (hAH.trans (normalizer_le_normalizer_layerOddPreimage H)) hH3
    (hS.toTheoremFourHyp.szSections hSz hH3) hSz3 hC0

theorem step155HostE0WRes1Type_of_autSolv_autFix (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46)
    (h143 : Y1SecondFormExcl) (h142 : Concl142S14) (h1444 : Item1444S14) (hSz : KFacts.KPSz)
    (hSz3 : CFSG.LocalAnalysis.UniquenessCase.UCK.SzOrder3Aut)
    {P : ∀ (Y : Type) [Group Y], Prop}
    (hP : ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup Y → P Y →
      Res1AutSolv Y ∧ Res1AutFix Y) :
    Step155HostE0WRes1Type P := by
  intro G _ _ A c L hR hN hS X K Y M T P' hC _ _ hE h146 hRP hIX Yc hY hsimple hPY
  obtain ⟨hsolv, hfix⟩ := hP ↥Yc hsimple hPY
  exact res1_layerOddPreimage_le_of_le_centralizer h1 h2 h43 hin h143 hR hN (h142 G A c L hS) hC
    hE h146 hRP hIX hY hsimple hsolv hfix
    (res1_layerOddPreimage_le_centralizer (h1444 G A c L hS) hSz hSz3 hS h146 hC hE hRP hIX)
end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
