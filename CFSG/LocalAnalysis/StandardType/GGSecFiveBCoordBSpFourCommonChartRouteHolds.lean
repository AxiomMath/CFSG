module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBRestLeafDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneBlocks
import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneConjSplit
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKFrame
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightModel
import CFSG.LocalAnalysis.StandardType.GGSecFiveBSpCoordFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBSpCoordFrameFacts
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpFour
import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc
import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTGlobal
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR7iii
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR8Field
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2FieldAlign
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (sl2Diag coe_sl2Diag)
open scoped MatrixGroups

private theorem exists_succ_indices {u v : Fin 4} {π : Fin 4 ≃ Fin 4}
    (hu : u ≠ π 0) (hv : v ≠ π 0) (huv : u ≠ v) :
    ∃ iu iv : Fin 3, π iu.succ = u ∧ π iv.succ = v ∧ iu ≠ iv := by
  have hpu : π.symm u ≠ 0 := fun h => hu (by rw [← π.apply_symm_apply u, h])
  have hpv : π.symm v ≠ 0 := fun h => hv (by rw [← π.apply_symm_apply v, h])
  have hru : π.symm u ∈ Set.range (Fin.succ : Fin 3 → Fin 4) := by
    rw [Fin.range_succ]
    exact hpu
  have hrv : π.symm v ∈ Set.range (Fin.succ : Fin 3 → Fin 4) := by
    rw [Fin.range_succ]
    exact hpv
  obtain ⟨iu, hiu⟩ := hru
  obtain ⟨iv, hiv⟩ := hrv
  have hπu : π iu.succ = u := by rw [hiu, π.apply_symm_apply]
  have hπv : π iv.succ = v := by rw [hiv, π.apply_symm_apply]
  refine ⟨iu, iv, hπu, hπv, ?_⟩
  intro h
  apply huv
  rw [← hπu, ← hπv, h]

private theorem range_succ_pairMap {u v : Fin 4} {π : Fin 4 ≃ Fin 4} {iu iv : Fin 3}
    (hπu : π iu.succ = u) (hπv : π iv.succ = v) :
    Set.range (fun l : Fin 2 => π (pairMap iu iv l).succ) = ({u, v} : Set (Fin 4)) := by
  ext w
  constructor
  · rintro ⟨l, rfl⟩
    fin_cases l <;> simp [hπu, hπv]
  · intro hw
    rcases hw with hw | hw
    · exact ⟨0, by change π iu.succ = w; rw [hπu, hw]⟩
    · exact ⟨1, by change π iv.succ = w; rw [hπv, hw]⟩

private theorem comp_spEmbed_longBlock {K G : Type} [Field K] [Group G] {m n : ℕ}
    {σ : Fin m → Fin n} (hσ : Function.Injective σ) (κ : StatedSp n K →* G) (l : Fin m) :
    (κ.comp (spEmbed σ hσ)).comp (longBlock K m l) = κ.comp (longBlock K n (σ l)) := by
  ext A
  change κ (spEmbed σ hσ (longBlock K m l A)) = κ (longBlock K n (σ l) A)
  rw [spEmbed_longBlock]

theorem GGSecFiveBPermSpKFrame.exists_ordered_commonChart
    {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hf : 2 ≤ f)
    {B Bs L D J : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))} {π : Fin 4 ≃ Fin 4}
    {κ : StatedSp 3 (GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hFL : GGSecFiveBPermSpKFrame Bs L eta π κ χ) {u v : Fin 4}
    (hu : u ≠ π 0) (hv : v ≠ π 0) (huv : u ≠ v) :
    ∃ (iu iv : Fin 3) (hiuv : iu ≠ iv), π iu.succ = u ∧ π iv.succ = v ∧
      let ψ : StatedSp 2 (GaloisField 2 f) →* G :=
        κ.comp (spEmbed (pairMap iu iv) (pairMap_injective hiuv))
      Function.Injective ψ ∧ ψ.range = ggBlockComm Bs eta {u, v} ∧
      (ψ.comp (longBlock (GaloisField 2 f) 2 0)).range =
        ⁅Subgroup.centralizer (ggBsCoordZero Bs eta u : Set G), Bs⁆ ∧
      (ψ.comp (longBlock (GaloisField 2 f) 2 1)).range =
        ⁅Subgroup.centralizer (ggBsCoordZero Bs eta v : Set G), Bs⁆ := by
  have hF : 4 ≤ Nat.card (GaloisField 2 f) := ggSecFiveBFour_le_card_galois hf
  obtain ⟨iu, iv, hπu, hπv, hiuv⟩ := exists_succ_indices hu hv huv
  let σ : Fin 2 → Fin 3 := pairMap iu iv
  have hσ : Function.Injective σ := pairMap_injective hiuv
  have hS : Set.range (fun l : Fin 2 => π (σ l).succ) = ({u, v} : Set (Fin 4)) := by
    simpa [σ] using range_succ_pairMap hπu hπv
  have hσs : ¬ Function.Surjective σ := by
    intro h
    have hcard := Fintype.card_le_of_surjective σ h
    norm_num at hcard
  let ψ : StatedSp 2 (GaloisField 2 f) →* G := κ.comp (spEmbed σ hσ)
  have hψ : Function.Injective ψ := by
    intro a b h
    apply spEmbed_injective hσ
    exact hFL.1 h
  obtain ⟨hp, hBs, hxBs, -, -⟩ := hR.1.1.tableB_facts
  have hBC : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a :=
    fun a ha b hb => CFSG.Open.IsElemAbelian.comm hBs ha hb
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hR.1.1.2.1.2.2.2
  have hLcomp : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hR.1.1.1.2.2.2.2.2.2.1.2.2.2.1
  have hPL : LargeEvenPComponent p (Subgroup.centralizer ({x} : Set G)) L :=
    hR.largeEvenPComponent_L (GGSecFiveBPermSpKFrame.prime_dvd_card hp hFL)
  have hFP := hFL.toPlaneFrame
  have hpair := ggSecFiveBPermZeta_commutator_centralizer_eq hp2 hF hSC hxBs hLcomp hFP σ hσ hσs
  rw [hS] at hpair
  have huEq := ggSecFiveBPermSp_singletonComm_K (r := 2) hp2 hf le_rfl hBC hSC hxBs hPL hFL iu
  have hvEq := ggSecFiveBPermSp_singletonComm_K (r := 2) hp2 hf le_rfl hBC hSC hxBs hPL hFL iv
  rw [hπu] at huEq
  rw [hπv] at hvEq
  have h0 : ψ.comp (longBlock (GaloisField 2 f) 2 0) =
      κ.comp (longBlock (GaloisField 2 f) 3 iu) := by
    simpa [ψ, σ] using comp_spEmbed_longBlock (K := GaloisField 2 f) hσ κ (0 : Fin 2)
  have h1 : ψ.comp (longBlock (GaloisField 2 f) 2 1) =
      κ.comp (longBlock (GaloisField 2 f) 3 iv) := by
    simpa [ψ, σ] using comp_spEmbed_longBlock (K := GaloisField 2 f) hσ κ (1 : Fin 2)
  exact ⟨iu, iv, hiuv, hπu, hπv, hψ, hpair.symm,
    (congrArg MonoidHom.range h0).trans huEq.symm,
    (congrArg MonoidHom.range h1).trans hvEq.symm⟩




theorem ggSecFiveBCoordBSpFourCommonChartRouteInput_holds :
    GGSecFiveBCoordBSpFourCommonChartRouteInput := by
  intro hMp _ _ _ _ hRig _ _ _ _ _ _
  have hfr : GGSecFiveBSpCoordFrameInput := ggSecFiveBSpCoordFrameInput_of_mp hMp
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hpres h4 eta i0 hBfull hLeta hLab hBB hnbr hG0 f K
    hcell j hj hKeta u v hju hjv huv hui hvi
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ 2 ^ f - 1 := hcell.dvd_two_pow_sub_one hLab hRig
  obtain ⟨hf, hn4, -, ⟨eL⟩, -⟩ := hcell
  subst hn4
  obtain ⟨πL, κL, χL, hπL, hFL⟩ := hfr G p hp hp2 2 f le_rfl hf hdvd B Bs L hR.1.1.2.1
    hR.1.2.2.1.1 ⟨eL⟩ eta i0 hLeta
  obtain ⟨iu, iv, hiuv, -, -, hψ, hRψ, hQ₀, hQ₁⟩ := hFL.exists_ordered_commonChart hp2 hf hR
    (by rw [hπL]; exact hui) (by rw [hπL]; exact hvi) huv
  exact ⟨κL.comp (spEmbed (pairMap iu iv) (pairMap_injective hiuv)), hψ, hRψ, hQ₀, hQ₁⟩

end CFSG.StandardType

end
