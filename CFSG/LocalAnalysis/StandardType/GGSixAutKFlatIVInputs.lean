module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVAutK
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVRootCentMain
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatStepTwo
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMarkingE6TwRankOne
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneSchreier
public import CFSG.RankThree.PartOne.TCB.SchreierFinal
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import Certificates.Certificate9124

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Inputs

theorem ggIVFlatData_of_ctx {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) :
    IsSimpleGroup ↥(ggG0 p B x L D J) ∧
      (∀ P : Subgroup G, P ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) → ⁅P, P⁆ = P →
        P ≤ ggG0 p B x L D J) ∧
      LargeEvenMarking ↥(ggG0 p B x L D J) fun _ _ _ I _ θ => ∀ c ∈ Bs,
        ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ := by
  obtain ⟨-, -, ⟨hadm, hrk⟩, ⟨hrange, hker⟩, ⟨hperf0, hmodel⟩, ⟨hBsN, hVI⟩, -, -⟩ := hctx.2
  have hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ :=
    ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, hperf0, hmodel⟩
  have hMkE6 : ∀ t, (t = .E6 ∨ t = .twistedE6) → GGInnerDiagMarkingAt t := by
    intro t ht
    rcases ht with rfl | rfl
    exacts [ggInnerDiagMarkingAt_E6, ggInnerDiagMarkingAt_twistedE6]
  have hmk0 := ggInnerDiagMarkingInput_of_E6 hMkE6 t G n f ψ (ggG0 p B x L D J) hpres
  have hmk : LargeEvenMarking ↥(ggG0 p B x L D J) fun _ _ _ I _ θ => ∀ c ∈ Bs,
      ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h c hc => h c (hBsN hc) (hVI c hc)) hmk0
  have hodd : Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))) := by
    rw [s1.1, Subgroup.card_bot]
    exact odd_one
  have hSP : GGSchreierPerfectInput := ggSchreierPerfectInput_of_lieSchreier
    (ggLieSchreierInput_of_schreierFor CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds)
  exact ⟨ggIsSimpleGroup_of_marking hmk s1.1,
    fun P hP hPP => hSP G t n f ψ _ hpres hodd P hP hPP, hmk⟩

theorem ggAutKCanonIVCompInput_of_sOne (hS1 : GGStructSOne) : GGAutKCanonIVCompInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 b L₁ K m hcfg hN
  obtain ⟨hb, hb1, hL₁, hK, hLK, hKM, hm, hEC⟩ := hcfg
  have : IsSimpleGroup G := hctx.1.1
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  obtain ⟨⟨hBBs, hBsEl, -, -⟩, ⟨⟨hDB, hDel, hDcard, -⟩, -⟩, -, -, -, ⟨hBsN, -⟩, -, -⟩ := hctx.2
  obtain ⟨hsimple, hperf, hmk⟩ := ggIVFlatData_of_ctx hctx s1
  have hfusE : GGControlsStrongFusion (ggM p B x L D J) (D.map (MulAut.conj m⁻¹).toMonoidHom) := by
    refine s1.2.1.of_map_conj_le ((ggM p B x L D J).inv_mem hm) ?_
    rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hd
  have hE0el : IsElemAbelian p (D.map (MulAut.conj m⁻¹).toMonoidHom) :=
    isElemAbelian_map_hom hDel _
  have hE0card : Nat.card (D.map (MulAut.conj m⁻¹).toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective, hDcard]
  have hnorm : D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.normalizer (K : Set G) :=
    ggLemmaThreeThirteenInput_holds G p hp hp2 (Subgroup.centralizer {b})
      (ggM p B x L D J ⊓ Subgroup.centralizer {b}) _
      (ggStepTwo_kGroup_of_ne_top hctx.1.2.2.1 (ggStepTwo_centralizer_ne_top hctx.1.2.1 hb1))
      hE0el hE0card (hfusE.inf_in hEC) K hK (fun h => hKM (h.trans inf_le_left))
  have hraw : GGRawInnSubgroupInput := ggRawInnSubgroupInput_of_rawInnField ggRawInnFieldInput_holds
  exact ggItem2_main hS1 hp hp2 hsimple hBsEl hDel (hDB.trans hBBs) hBsN
    (fun {n'} hn' {b' d'} hb' hd' =>
      ggMarking_closure_pair hraw ggInndiagNormalInput_holds hBsN hmk hn' hb' hd')
    hperf hfusE hnorm hb hK.2.1 hm hEC

theorem ggRootCentAutKIVFlatInput_of_sOnePrimeRoot (hS1' : GGStructSOnePrimeRoot) :
    GGRootCentAutKIVFlatInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 s2 E r hch K S hset hN
  have : IsSimpleGroup G := hctx.1.1
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  obtain ⟨-, -, ⟨hadm, hrk⟩, ⟨hrange, hker⟩, -, ⟨hBsN, -⟩, -, -⟩ := hctx.2
  obtain ⟨hsimple, hperf, hmk⟩ := ggIVFlatData_of_ctx hctx s1
  obtain ⟨γ, hγ, u, -, hru⟩ := hch.2.2.2.2.2
  have hroot : GGIsRootInvolution (ggG0 p B x L D J) r :=
    ⟨t, n, f, ψ, hrange, hadm, hrk, hker, hch.2.2.2.2.1, γ, hγ, u, hru⟩
  exact ggItem5_main hS1' hp hp2 hsimple hBsN hmk hperf hch.1 hch.2.1 hch.2.2.2.1
    (hch.mem_ggG0 hctx) hch.2.2.2.2.1 hroot hch.le_centralizer hset.1 hset.2.2.1

end Inputs

end CFSG.StandardType
