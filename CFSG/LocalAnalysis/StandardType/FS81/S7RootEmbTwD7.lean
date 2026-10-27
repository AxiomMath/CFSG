module

public import CFSG.LocalAnalysis.StandardType.FS81.RootE8Defs
public import CFSG.LocalAnalysis.StandardType.FS81.S7Model
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotMainLift
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.FS81.Realized
import CFSG.LocalAnalysis.StandardType.FS81.RootD6ModelDefs
import CFSG.LocalAnalysis.StandardType.FS81.S7AutAt
import CFSG.LocalAnalysis.StandardType.FS81.S7ModelIdent
import CFSG.LocalAnalysis.StandardType.FS81.S7R120
import CFSG.LocalAnalysis.StandardType.FS81.S7RadicalTwD7
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction CFSG.QuasithinUnique

local notation "GF₂" => GaloisField 2 1
local notation "sθ" => rootThree Tag.E8 (GaloisField 2 1) (highRoot Tag.E8)
local notation "Dθ" => EPilot.perpLevi Tag.E8 (GaloisField 2 1)

section Row


theorem exists_rootEmbedding_twD7 {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    {B : Basis3 G ((Row.twD7).n + 1)} {Y : Subgroup G} (h : RootSetting Row.twD7 b₀ K E B Y) :
    ∃ ι : adjointGroup .E8 GF₂ →* G, Function.Injective ι ∧ ι.range = Y ∧
      ι sθ = rowRootElt Row.twD7 B b₀ ∧ s79A Row.twD7 B ≤ (Dθ).map ι := by
  have hK2 : Nat.card (GaloisField 2 1) = 2 := natCard_galoisField_two_one
  have hA : E8AutAt Row.twD7 := e8AutAt_twD7
  obtain ⟨ι, hι_inj, hι_range⟩ := exists_injective_hom_range_eq_of_isEm_eight h.isEm
  have hβE : b₀ * B.b 1 ∈ E := by
    have h0 : b₀ ∈ E := by rw [← h.adapted.2.1]; exact h.adapted.1 ▸ B.b_mem_span 0
    exact E.mul_mem h0 (h.adapted.1 ▸ B.b_mem_span 1)
  have hordβ : orderOf (b₀ * B.b 1) = 3 := by
    have hvec : B.vec ((Pi.single 0 1 : Coords (Row.twD7.n + 1)) + Pi.single 1 1) =
        b₀ * B.b 1 := by
      rw [B.vec_add, B.vec_single, B.vec_single, h.adapted.2.1]
    refine orderOf_eq_prime ?_ ?_
    · rw [← hvec]
      exact h.std.2.1.2.1.2.1.2 _ (h.adapted.1 ▸ B.vec_mem_span _)
    · intro h1
      have h1' : B.vec ((Pi.single 0 1 : Coords (Row.twD7.n + 1)) + Pi.single 1 1) = 1 := by
        rw [hvec, h1]
      have he0 := B.indep _ h1'
      have h0 := congrFun he0 0
      simp only [Pi.add_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne (by decide : (0 : Fin (Row.twD7.n + 1)) ≠ 1),
        Pi.zero_apply, add_zero] at h0
      exact one_ne_zero h0
  have hβ1 : b₀ * B.b 1 ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hordβ
    norm_num at hordβ
  have h120 : (normalizerLines ι.range E (b₀ * B.b 1)).ncard = 120 := by
    rw [hι_range]
    exact ncard_normalizerLines_eq_120_twD7 h (hA G b₀ K E B Y h)
  have hEY : E ≤ ι.range := by rw [hι_range]; exact h.torus_le
  have hEab : IsElemAbelian 3 E := h.std.2.1.2.1.2.1
  have hEcard : 3 ^ 8 ≤ Nat.card E := by
    rw [h.std.2.1.2.2.2.1]
    norm_num [Row.m, Row.n]
  obtain ⟨ι', hι'_inj, hι'_range, hι'_sθ⟩ :=
    exists_hom_range_eq_apply_rootThree_eq hK2 ι hι_inj hEY hEab hEcard hβE hβ1 h120
  have hι'_rangeY : ι'.range = Y := hι'_range.trans hι_range
  have hLt₀ : (Dθ).map ι' ≤ Subgroup.centralizer
      ({ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GaloisField 2 1))} : Set G) :=
    (map_le_centralizer_map_pinnedElt_highRoot (K := GaloisField 2 1) ι').2
  have hs79 : s79A Row.twD7 B ≤ (Dθ).map ι' :=
    radTwD7_s79A_le h hK2 ι' hι'_inj hι'_rangeY hι'_sθ hordβ hLt₀
  exact ⟨ι', hι'_inj, hι'_rangeY, hι'_sθ, hs79⟩

end Row

end CFSG.StandardType.FrameRoute.FS81

end
