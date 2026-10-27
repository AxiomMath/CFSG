module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Inner
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest15Rank
import CFSG.LocalAnalysis.UniquenessCase.UC6R869MConj
import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizingRank
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Setup
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddChain
import CFSG.LocalAnalysis.UniquenessCase.UC6R869NS
import CFSG.GroupTheory.PRankLeOfSylowLe
import CFSG.LocalAnalysis.AGL81TheoremC.CoprimeGamma
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69Setup
import CFSG.CGT.Foote82.D1Steps
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69R875
import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
public import CFSG.Blueprint.LieModelAPI



public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive)

variable {G : Type} [Group G] [Finite G]

theorem rankThreeGamma_le_of_small_sigma_rank
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (hSE : StronglyEmbeddedFive) (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (h3 : 3 ∉ uniqueFourBeta G) {L : Subgroup G}
    (hL : L ∈ calC S.M) (hML : S.M ≤ normalizer (L : Set G))
    (hpL : CFSG.Open.pRank S.p L ≤ 1) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {Q : Subgroup G} (hQL : Q ≤ L) (hQ : IsPGroup r Q)
    (hQr : 2 ≤ CFSG.Open.pRank r Q) : rankThreeGamma 1 r Q ≤ S.M := by
  have : Fact S.p.Prime := ⟨S.hp.1.1⟩
  have : Fact r.Prime := ⟨hr⟩
  have hp := S.hp.1.1
  have hp2 := S.hp.1.2.1
  have hLM : L ≤ S.M := hL.1.le
  have hLtop : L ≠ ⊤ := ne_top_of_le_ne_top
    (uc22p20a_M_ne_top (UC6.dataOfSetup4 hS hU S)) hLM
  have hAut := UC6.R869S.pRank_mulAut_bar2_le_two hOut
    (hS.kProper.isKGroup L hLtop) hL.2.2 hp hp2 hpL
  obtain ⟨B, hBM, hBel, hBc⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hp (UC6.four_le_pRank_of_sigma S.hp)
  have hcent := UC6.R869S.two_le_pRank_centralizer_of_pRank_mulAut hLM hp hp2 hAut
    hBM (hBM.trans hML) hBel hBc hr hr2 hQL hQ
  have hsp := UC6S846.sp_of_mem_sig (UC6S846.sigmaStd_dataOfSetup4 hS hU S)
    (UC6S846.not_solvable_of_mem_calC hL) S.hp
  exact PartOne.Section7.rankThreeGamma_le_of_two_le_pRank_inf_centralizer hsp
    (UC6.conclusion76_dataOfSetup4 hSE hS hU S h3 S.hp hsp)
    (hQL.trans hLM) hQ hQr hcent

theorem rest15_rankThreeGamma_le_of_centralizesBar
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (hSE : StronglyEmbeddedFive) (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (h3 : 3 ∉ uniqueFourBeta G) {L : Subgroup G}
    (hL : L ∈ calC S.M) (hML : S.M ≤ normalizer (L : Set G))
    {a : G} (hodd : Odd (orderOf a)) (hpr : (orderOf a).Prime)
    (haL : CentralizesBar a L)
    (hN : CFSG.Open.pRank S.p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ S.M) ≤ 1)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {Q : Subgroup G}
    (hQL : Q ≤ L) (hQ : IsPGroup r Q) (hQr : 2 ≤ CFSG.Open.pRank r Q) :
    rankThreeGamma 1 r Q ≤ S.M :=
  rankThreeGamma_le_of_small_sigma_rank hOut hSE hS hU S h3 hL hML
    (uc22s213_pRank_le_one_of_centralizesBar hL.1.le hodd hpr haL S.hp.1.1 S.hp.1.2.1 hN)
    hr hr2 hQL hQ hQr

theorem rest15_rankThreeGamma_le_of_exclusions
    (hGA : GriessAllModelsStatement)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (hSE : StronglyEmbeddedFive) (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (hMS : S.InMSigma) {L : Subgroup G} (hL : L ∈ calC S.M)
    (hML : S.M ≤ normalizer (L : Set G))
    (hC2 : ¬ S21_3Closed2 L) (hL2 : ¬ S21_3ClosedL2 L)
    (hTL : ¬ S21_3ClosedTorusL3 L) (hU3 : ¬ S21_3ClosedU3 L)
    (hCh : ¬ S21_3ClosedChar S.M L) (hSmall : ¬ S21_3ClosedSmall S.M L)
    (hY : ¬ S21_3ClosedCharY S.M L) (hlist : S21_3List L)
    (hstrong : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M →
      CFSG.Open.pRank 3 L ≤ 1)
    {a : G} (hodd : Odd (orderOf a)) (hpr : (orderOf a).Prime)
    (haL : CentralizesBar a L)
    (hN : CFSG.Open.pRank S.p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ S.M) ≤ 1)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {Q : Subgroup G}
    (hQL : Q ≤ L) (hQ : IsPGroup r Q) (hQr : 2 ≤ CFSG.Open.pRank r Q) :
    rankThreeGamma 1 r Q ≤ S.M := by
  have h2 := rest15_two_le_pRank_three hGA hL hC2 hL2 hTL hU3 hCh hSmall hY hlist
  have h3 : 3 ∉ uniqueFourBeta G := fun h3 => by
    have := hstrong (isStronglyPEmbedded_three_of_mem_uniqueFourBeta hU S hMS h3)
    omega
  exact rest15_rankThreeGamma_le_of_centralizesBar hOut hSE hS hU S h3 hL hML
    hodd hpr haL hN hr hr2 hQL hQ hQr

theorem pRank_le_of_mem_uniqueSet_of_le
    {M E H : Subgroup G} (hM : CFSG.Open.rankThreeIsMaxTwoLocal M) {p : ℕ}
    (hp : p.Prime) (hE : E ∈ uniqueSet M) (hEp : IsPGroup p E) (hEH : E ≤ H) :
    CFSG.Open.pRank p H ≤ CFSG.Open.pRank p M := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hES⟩ := (hEp.comap_subtype (K := H)).exists_le_sylow
  let P : Subgroup G := (S : Subgroup H).map H.subtype
  have hP : CFSG.ABGLocalTools.IsSylowOf p P H := ⟨S, rfl⟩
  have hEP : E ≤ P := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hEH]
    exact Subgroup.map_mono hES
  have hPM : P ≤ M :=
    PartOne.Section9.le_of_mem_uniqueSet_of_isPGroup hM hE hEP hP.isPGroup
  exact CFSG.pRank_le_of_isSylowOf_le hp hP.le hP hPM

theorem rest15_exists_e9_mem_uniqueSet_of_centralizesBar
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hC : CFSG.Yardstones.Mf4cdcdf2e013.TheoremCAt S.M)
    {L : Subgroup G} (hL : L ≤ S.M) (hL3 : 2 ≤ CFSG.Open.pRank 3 L)
    {a : G} (hodd : Odd (orderOf a)) (hpr : (orderOf a).Prime)
    (haL : CentralizesBar a L)
    (hGamma : ∀ Q : Subgroup G, Q ≤ L → IsPGroup 3 Q →
      2 ≤ CFSG.Open.pRank 3 Q → rankThreeGamma 1 3 Q ≤ S.M) :
    ∃ E : Subgroup G, E ≤ L ⊓ centralizer ((zpowers a : Subgroup G) : Set G) ∧
      IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ E ∈ uniqueSet S.M := by
  have hr2 : orderOf a ≠ 2 := fun h => Nat.not_odd_iff_even.mpr even_two (h ▸ hodd)
  have hcov := uc22p21d_sup_pCore_eq hpr hr2 (Nat.card_zpowers a)
    (fun _ h => uc22p21d_centralizesBar_of_mem_zpowers haL h)
  have hX3 : 2 ≤ CFSG.Open.pRank 3 (L ⊓ centralizer ((zpowers a : Subgroup G) : Set G)) :=
    hL3.trans (UC6.R869S.pRank_le_of_sup_pCore inf_le_left hcov Nat.prime_three (by norm_num))
  obtain ⟨E, hEX, hEe, hEc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank Nat.prime_three hX3
  have hEL : E ≤ L := hEX.trans inf_le_left
  have hEM : E ≤ S.M := hEL.trans hL
  have hEr : 2 ≤ CFSG.Open.pRank 3 E :=
    CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_rfl hEe hEc
  have hΓ : rankThreeGamma 1 3 E ≤ S.M := hGamma E hEL hEe.isPGroup hEr
  have hUnique := UC6.r6_3_dataOfSetup4 hS hU S hC 3 Nat.prime_three (by norm_num)
    E hEM hEe hEc hΓ
  have hEU : E ∈ uniqueSet S.M :=
    CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_forall S.maxLocal hEM (fun N hN hEN => by
      have hmem : N ∈ calMOf E := ⟨hN, hEN⟩
      rw [hUnique] at hmem
      exact Set.mem_singleton_iff.mp hmem)
  exact ⟨E, hEX, hEe, by norm_num at hEc ⊢; exact hEc, hEU⟩

theorem rest15_pRank_three_le_three_of_centralizer_le
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma)
    (hC : CFSG.Yardstones.Mf4cdcdf2e013.TheoremCAt S.M)
    {L : Subgroup G} (hL : L ≤ S.M) (hL3 : 2 ≤ CFSG.Open.pRank 3 L)
    (hNot : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M)
    {a : G} (hodd : Odd (orderOf a)) (hpr : (orderOf a).Prime) (haL : CentralizesBar a L)
    (hGamma : ∀ Q : Subgroup G, Q ≤ L → IsPGroup 3 Q →
      2 ≤ CFSG.Open.pRank 3 Q → rankThreeGamma 1 3 Q ≤ S.M)
    {H : Subgroup G} (hH : L ⊓ centralizer ((zpowers a : Subgroup G) : Set G) ≤ H) :
    CFSG.Open.pRank 3 H ≤ 3 := by
  obtain ⟨E, hEX, hEe, -, hEU⟩ :=
    rest15_exists_e9_mem_uniqueSet_of_centralizesBar hS hU S hC hL hL3 hodd hpr haL hGamma
  exact (pRank_le_of_mem_uniqueSet_of_le S.maxLocal Nat.prime_three hEU hEe.isPGroup
    (hEX.trans hH)).trans (PartOne.Section8.pRank_three_le_three_of_not_strong hS hU S hMS hNot)

theorem rest15_overgroup_rank_of_local_inputs
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma)
    (hPart : PartIAt S.M) {L : Subgroup G} (hLM : L ≤ S.M)
    (hL3 : CFSG.Open.pRank 3 L = 2)
    (hstrong : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M → CFSG.Open.pRank 3 L ≤ 1)
    {a : G} (hodd : Odd (orderOf a)) (hpr : (orderOf a).Prime)
    (hGamma : ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ Q : Subgroup G, Q ≤ L → IsPGroup r Q →
      2 ≤ CFSG.Open.pRank r Q → rankThreeGamma 1 r Q ≤ S.M)
    (haL : CentralizesBar a L) :
    ∀ H : Subgroup G, L ⊓ centralizer ((zpowers a : Subgroup G) : Set G) ≤ H →
      CFSG.Open.pRank 3 H ≤ 3 := by
  have hnot : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M := fun h => by
    have := hstrong h
    omega
  exact fun H hH => rest15_pRank_three_le_three_of_centralizer_le hS hU S hMS hPart.1 hLM
    (by omega) hnot hodd hpr haL (hGamma 3 Nat.prime_three (by norm_num)) hH

theorem rest15_pCore_two_eq_bot_of_centralizer_le
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hC : CFSG.Yardstones.Mf4cdcdf2e013.TheoremCAt S.M)
    {L : Subgroup G} (hL : L ≤ S.M) (hL3 : 2 ≤ CFSG.Open.pRank 3 L)
    {a : G} (hodd : Odd (orderOf a)) (hpr : (orderOf a).Prime)
    (haL : CentralizesBar a L)
    (hGamma : ∀ Q : Subgroup G, Q ≤ L → IsPGroup 3 Q →
      2 ≤ CFSG.Open.pRank 3 Q → rankThreeGamma 1 3 Q ≤ S.M)
    {H : Subgroup G} (hH : L ⊓ centralizer ((zpowers a : Subgroup G) : Set G) ≤ H)
    (hHM : ¬ H ≤ S.M) : pCoreOf 2 H = ⊥ := by
  obtain ⟨E, hEX, hEe, hEc, -⟩ :=
    rest15_exists_e9_mem_uniqueSet_of_centralizesBar hS hU S hC hL hL3 hodd hpr haL hGamma
  have hEM : E ≤ S.M := hEX.trans (inf_le_left.trans hL)
  have hEr : 2 ≤ CFSG.Open.pRank 3 E :=
    CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_rfl hEe (by norm_num; exact hEc)
  have hΓ : rankThreeGamma 1 3 E ≤ S.M := hGamma E (hEX.trans inf_le_left) hEe.isPGroup hEr
  by_contra hO
  have hloc : IsTwoLocal (normalizer ((pCoreOf 2 H : Subgroup G) : Set G)) :=
    ⟨pCoreOf 2 H, hO, CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H, rfl⟩
  have hHN : H ≤ normalizer ((pCoreOf 2 H : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  exact hHM (hHN.trans (hC 3 Nat.prime_three (by norm_num) E hEM hEe.isPGroup hEr hΓ
    _ hloc (hEX.trans (hH.trans hHN))))

theorem rest15_overgroup_core_le_of_centralizesBar
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hC : CFSG.Yardstones.Mf4cdcdf2e013.TheoremCAt S.M)
    {L : Subgroup G} (hL : L ≤ S.M) (hL3 : 2 ≤ CFSG.Open.pRank 3 L)
    {a : G} (hodd : Odd (orderOf a)) (hpr : (orderOf a).Prime)
    (haL : CentralizesBar a L)
    (hGamma : ∀ Q : Subgroup G, Q ≤ L → IsPGroup 3 Q →
      2 ≤ CFSG.Open.pRank 3 Q → rankThreeGamma 1 3 Q ≤ S.M)
    {H : Subgroup G} (hH : L ⊓ centralizer ((zpowers a : Subgroup G) : Set G) ≤ H) :
    relPPrimeCore 3 H ≤ S.M ∧ CFSG.fittingSubgroupOf H ≤ S.M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEX, hEe, hEc, hEU⟩ :=
    rest15_exists_e9_mem_uniqueSet_of_centralizesBar hS hU S hC hL hL3 hodd hpr haL hGamma
  have hEH : E ≤ H := hEX.trans hH
  have hEr : 2 ≤ CFSG.Open.pRank 3 E :=
    CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_rfl hEe (by norm_num; exact hEc)
  have hΓ : rankThreeGamma 1 3 E ≤ S.M := hGamma E (hEX.trans inf_le_left) hEe.isPGroup hEr
  have hO3' : relPPrimeCore 3 H ≤ S.M :=
    CFSG.LocalAnalysis.AGL81TheoremC.relPPrimeCore_le_of_glbCore_le hEe
      (by norm_num [hEc] : 3 ^ (1 + 1) ≤ Nat.card E) hEH hΓ
  obtain ⟨P, hEP⟩ := (hEe.isPGroup.comap_subtype (K := H)).exists_le_sylow
  let Q : Subgroup G := (P : Subgroup H).map H.subtype
  have hEQ : E ≤ Q := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hEH]
    exact Subgroup.map_mono hEP
  have hQM : Q ≤ S.M :=
    PartOne.Section9.le_of_mem_uniqueSet_of_isPGroup S.maxLocal hEU hEQ
      (P.isPGroup'.map H.subtype)
  have hO3 : (CFSG.pCore 3 H).map H.subtype ≤ S.M :=
    (Subgroup.map_mono (CFSG.fitting_pCore_le_sylow P)).trans hQM
  have hO3map : (CFSG.pPrimeCore 3 H).map H.subtype ≤ S.M := by
    rwa [CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
      Nat.prime_three H] at hO3'
  have hF := Subgroup.map_mono (f := H.subtype)
    (CFSG.section9_fitting_le_pCore_sup_pPrimeCore (G := H) (p := 3))
  rw [Subgroup.map_sup] at hF
  exact ⟨hO3', hF.trans (sup_le hO3 hO3map)⟩

theorem rest15_perfectCore_centralizer_spec {M L : Subgroup G}
    (hL : L ∈ calC M) {a : G}
    (hodd : Odd (orderOf a)) (hpr : (orderOf a).Prime)
    (haL : CentralizesBar a L) :
    let X := CFSG.Quasithin.perfectCore
      (L ⊓ centralizer ((zpowers a : Subgroup G) : Set G))
    X ≤ L ⊓ centralizer ((zpowers a : Subgroup G) : Set G) ∧
      ⁅X, X⁆ = X ∧ X ⊔ pCoreOf 2 L = L ∧
      CFSG.Open.IsQuasisimple (Bar2 X) := by
  dsimp only
  let C := L ⊓ centralizer ((zpowers a : Subgroup G) : Set G)
  let X := CFSG.Quasithin.perfectCore C
  have hCL : C ≤ L := inf_le_left
  have hXC : X ≤ C := CFSG.Quasithin.perfectCore_le C
  have hr2 : orderOf a ≠ 2 := fun h =>
    Nat.not_odd_iff_even.mpr even_two (h ▸ hodd)
  have hCov : C ⊔ pCoreOf 2 L = L := uc22p21d_sup_pCore_eq hpr hr2
    (Nat.card_zpowers a) (fun _ h => uc22p21d_centralizesBar_of_mem_zpowers haL h)
  have hCm : (C.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 L)) = ⊤ :=
    UC6.R869S.map_subgroupOf_eq_top hCL hCov
  have : Group.IsPerfect (Bar2 L) := ⟨hL.2.2.1⟩
  have hPerfTop : CFSG.Quasithin.perfectCore (⊤ : Subgroup (Bar2 L)) = ⊤ :=
    CFSG.Quasithin.perfectCore_eq_self_of_perfect
      (Subgroup.isPerfect_iff.mp (Group.IsPerfect.top_iff.mpr inferInstance))
  have hXm : (X.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 L)) = ⊤ := by
    have hsub : CFSG.Quasithin.perfectCore (C.subgroupOf L) = X.subgroupOf L := by
      apply Subgroup.map_injective L.subtype_injective
      rw [CFSG.Quasithin.map_perfectCore L.subtype, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr hCL, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr (hXC.trans hCL)]
    rw [← hsub, CFSG.Quasithin.map_perfectCore, hCm, hPerfTop]
  have hsupL : X.subgroupOf L ⊔ CFSG.pCore 2 L = ⊤ := by
    have hpre := congrArg (Subgroup.comap (QuotientGroup.mk' (CFSG.pCore 2 L))) hXm
    simpa only [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] using hpre
  have hsup : X ⊔ pCoreOf 2 L = L := by
    have h := congrArg (Subgroup.map L.subtype) hsupL
    simpa only [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (hXC.trans hCL), Subgroup.map_top, Subgroup.range_subtype,
      CFSG.Open.pCoreOf] using h
  obtain ⟨e⟩ := PartOne.Section8.nonempty_bar2_equiv_of_sup_pCore L X hsup
  exact ⟨hXC, CFSG.Quasithin.perfectCore_perfect C, hsup,
    CFSG.Open.IsQuasisimple.of_mulEquiv e hL.2.2⟩

theorem isComponentOf_inf_of_sup_pCore_of_pCore_eq_bot
    {M L X H : Subgroup G} (hL : L ∈ calC M) (hXL : X ≤ L)
    (hXH : X ≤ H) (hsup : X ⊔ pCoreOf 2 L = L)
    (hXq : CFSG.Open.IsQuasisimple (Bar2 X))
    (hO2 : pCoreOf 2 (H ⊓ M) = ⊥) :
    CFSG.Open.IsComponentOf X (H ⊓ M) := by
  have hsub : IsSubnormal (L ⊓ H) (H ⊓ M) := by
    have h := hL.1.inf H
    simpa only [inf_comm M H] using h
  have hOinf : pCoreOf 2 L ⊓ H ≤ pCoreOf 2 (L ⊓ H) := by
    have h := CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2
      (inf_le_left : L ⊓ H ≤ L)
    have he : (L ⊓ H) ⊓ pCoreOf 2 L = pCoreOf 2 L ⊓ H := by
      rw [inf_comm (L ⊓ H), ← inf_assoc,
        inf_eq_left.mpr (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L)]
    rwa [he] at h
  have hbot : pCoreOf 2 L ⊓ H = ⊥ := by
    have h := hOinf.trans (CFSG.CGT.Foote82.pCoreOf_le_pCoreOf_of_isSubnormal hsub)
    rw [hO2] at h
    exact le_bot_iff.mp h
  have heq : L ⊓ H = X := by
    apply le_antisymm ?_ (le_inf hXL hXH)
    intro l hl
    have hnorm : X ≤ normalizer (pCoreOf 2 L : Set G) :=
      hXL.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L)
    have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right X (pCoreOf 2 L) hnorm
    have hl' : l ∈ (↑(X ⊔ pCoreOf 2 L) : Set G) := hsup.symm ▸ hl.1
    rw [hcoe, Set.mem_mul] at hl'
    obtain ⟨x, hx, o, ho, hxo⟩ := hl'
    have ho_eq : o = x⁻¹ * l := by rw [← hxo]; group
    have hoH : o ∈ H := by rw [ho_eq]; exact H.mul_mem (H.inv_mem (hXH hx)) hl.2
    have ho1 : o = 1 := Subgroup.mem_bot.mp (hbot ▸ (show o ∈ pCoreOf 2 L ⊓ H from ⟨ho, hoH⟩))
    rw [← hxo, ho1, mul_one]
    exact hx
  have hXsub : IsSubnormal X (H ⊓ M) := heq ▸ hsub
  have hX2 : pCoreOf 2 X = ⊥ := by
    have h := CFSG.CGT.Foote82.pCoreOf_le_pCoreOf_of_isSubnormal hXsub
    rw [hO2] at h
    exact le_bot_iff.mp h
  have h2 : CFSG.pCore 2 X = ⊥ := by
    apply Subgroup.map_injective X.subtype_injective
    change pCoreOf 2 X = (⊥ : Subgroup X).map X.subtype
    simpa using hX2
  have hq : CFSG.Open.IsQuasisimple X := by
    have e : X ≃* Bar2 X := (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq h2.symm))
    exact CFSG.Open.IsQuasisimple.of_mulEquiv e hXq
  exact ⟨le_inf hXH (hXL.trans hL.1.le), hXsub, hq⟩

theorem rest15_perfectCore_bar2_models_of_barInf_models
    {M L : Subgroup G} (hL : L ∈ calC M) {a : G}
    (hodd : Odd (orderOf a)) (hpr : (orderOf a).Prime) (haL : CentralizesBar a L)
    (hmod : CFSG.Blueprint.LieModel (BarInf L) .PSL 3 2 2 ∨ CFSG.Blueprint.LieModel (BarInf L) .PSU 3 2 3) :
    let X := CFSG.Quasithin.perfectCore
      (L ⊓ centralizer ((zpowers a : Subgroup G) : Set G));
    IsSL3 (Bar2 X) 2 ∨ IsSU3 (Bar2 X) 3 := by
  dsimp only
  let X := CFSG.Quasithin.perfectCore
    (L ⊓ centralizer ((zpowers a : Subgroup G) : Set G))
  have hspec := rest15_perfectCore_centralizer_spec hL hodd hpr haL
  obtain ⟨e⟩ := PartOne.Section8.nonempty_bar2_equiv_of_sup_pCore L X hspec.2.2.1
  have hmodL := rest15_bar2_models_of_barInf_models hL hmod
  rcases hmodL with ⟨_, hm⟩ | ⟨_, hm⟩
  · exact Or.inl ⟨hspec.2.2.2, CFSG.Blueprint.LieModel.of_mulEquiv
      (QuotientGroup.congr (center (Bar2 L)) (center (Bar2 X)) e.symm
        (Subgroup.map_center_eq e.symm)) hm⟩
  · exact Or.inr ⟨hspec.2.2.2, CFSG.Blueprint.LieModel.of_mulEquiv
      (QuotientGroup.congr (center (Bar2 L)) (center (Bar2 X)) e.symm
        (Subgroup.map_center_eq e.symm)) hm⟩

omit [Finite G] in
theorem rest15_models_of_bar2_models_of_pCoreOf_eq_bot {X : Subgroup G}
    (hO2 : pCoreOf 2 X = ⊥)
    (hmodel : IsSL3 (Bar2 X) 2 ∨ IsSU3 (Bar2 X) 3) :
    IsSL3 X 2 ∨ IsSU3 X 3 := by
  have hpc : CFSG.pCore 2 X = ⊥ := by
    rw [CFSG.Open.pCoreOf] at hO2
    exact (Subgroup.map_eq_bot_iff_of_injective (CFSG.pCore 2 X) X.subtype_injective).1 hO2
  let e : Bar2 X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hpc).trans QuotientGroup.quotientBot
  rcases hmodel with ⟨hq, hm⟩ | ⟨hq, hm⟩
  · exact Or.inl ⟨CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hq,
      CFSG.Blueprint.LieModel.quotient_center_of_mulEquiv e hm⟩
  · exact Or.inr ⟨CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hq,
      CFSG.Blueprint.LieModel.quotient_center_of_mulEquiv e hm⟩

theorem rest15_center_eq_bot_or_card_eq_three
    (hGA : GriessAllModelsStatement) {X : Subgroup G}
    (hO2 : pCoreOf 2 X = ⊥) (hmodel : IsSL3 X 2 ∨ IsSU3 X 3) :
    center X = ⊥ ∨ Nat.card (center X) = 3 := by
  have hpc : CFSG.pCore 2 X = ⊥ := by
    rw [CFSG.Open.pCoreOf] at hO2
    exact (Subgroup.map_eq_bot_iff_of_injective (CFSG.pCore 2 X) X.subtype_injective).1 hO2
  let e : Bar2 X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hpc).trans QuotientGroup.quotientBot
  have hodd : Odd (Nat.card (center X)) := by
    rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]
    exact uc22p20p_odd_center_bar2 X
  have hdvd := PartOne.Section8.card_center_dvd_of_isSL3_or_isSU3 hGA hmodel
  have hcop : (Nat.card (center X)).Coprime (2 ^ 4) :=
    (Nat.coprime_pow_right_iff (by norm_num) _ 2).mpr (Nat.coprime_two_right.mpr hodd)
  have h3 : Nat.card (center X) ∣ 3 := by
    apply hcop.dvd_of_dvd_mul_left
    simpa using hdvd
  rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h1 | h3
  · exact Or.inl (Subgroup.eq_bot_of_card_eq _ h1)
  · exact Or.inr h3

end CFSG.LocalAnalysis.UniquenessCase.UC22
