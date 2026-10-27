module

public import CFSG.LocalAnalysis.StandardType.FS81.RootE8Defs
public import CFSG.LocalAnalysis.StandardType.FS81.S7Model
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotMainLift
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.FS81.S7R120
import CFSG.LocalAnalysis.StandardType.FS81.S7AutAt
import CFSG.LocalAnalysis.StandardType.FS81.S7ModelIdent
import CFSG.LocalAnalysis.StandardType.FS81.RootD6ModelDefs
import CFSG.LocalAnalysis.StandardType.GGFrameRouteE7Models
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


theorem exists_rootEmbedding_E7 {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    {B : Basis3 G ((Row.E7).n + 1)} {Y : Subgroup G} (h : RootSetting Row.E7 b₀ K E B Y) :
    ∃ ι : adjointGroup .E8 GF₂ →* G, Function.Injective ι ∧ ι.range = Y ∧
      ι sθ = rowRootElt Row.E7 B b₀ ∧ s79A Row.E7 B ≤ (Dθ).map ι := by
  let F := GaloisField 2 1
  have hK2 : Nat.card F = 2 := natCard_galoisField_two_one
  have hA : E8AutAt Row.E7 := e8AutAt_E7
  obtain ⟨ι, hι_inj, hι_range⟩ := exists_injective_hom_range_eq_of_isEm_eight h.isEm
  have h120 : (normalizerLines ι.range E b₀).ncard = 120 := by
    rw [hι_range]
    exact ncard_normalizerLines_eq_120_E7 h (hA G b₀ K E B Y h)
  have hEY : E ≤ ι.range := by
    rw [hι_range]
    exact RootSetting.torus_le h
  have hEab : IsElemAbelian 3 E := h.std.2.1.2.1.2.1
  have hEcard : 3 ^ 8 ≤ Nat.card E := by
    rw [h.std.2.1.2.2.2.1]
    norm_num [Row.m, Row.n]
  have hb₀E : b₀ ∈ E := h.std.2.1.2.2.1
  have hb₀1 : b₀ ≠ 1 := by
    have hord : orderOf b₀ = 3 := by
      rw [← h.adapted.2.1]
      exact B.ord 0
    intro h1
    rw [h1, orderOf_one] at hord
    norm_num at hord
  obtain ⟨ι', hι'_inj, hι'_range, hι'_sθ⟩ :=
    exists_hom_range_eq_apply_rootThree_eq hK2 ι hι_inj hEY hEab hEcard hb₀E hb₀1 h120
  have hι'_rangeY : ι'.range = Y := hι'_range.trans hι_range
  have hKcard : Nat.card K = Nat.card (adjointGroup .E7 F) := by
    obtain ⟨lab, hlabP, hlab⟩ := exists_glaLabel h.std.2.2.1
    obtain ⟨t, r, n⟩ := lab
    have hn1 : n = 1 := hlabP.1
    subst hn1
    have ht : t = .E7 := by
      obtain ⟨-, hcases⟩ := hlabP
      rcases hcases with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact h
    obtain ⟨φ⟩ := exists_mulEquiv_adjointGroup_of_isLabel_E7' (lab := ⟨t, r, 1⟩) hlab ht
      h.std.2.1.1.2.2.2.1
    exact Nat.card_congr φ.toEquiv
  have hDle : (EPilot.perpLevi .E8 F).map ι' ≤ Subgroup.zpowers b₀ ⊔ K := by
    have hs : EPilot.perpLevi .E8 F ≤ Subgroup.centralizer
        ({rootThree .E8 F (highRoot .E8)} : Set (adjointGroup .E8 F)) :=
      perpLevi_le_centralizer_rootThree (K := F)
    have h1 : (EPilot.perpLevi .E8 F).map ι' ≤ Subgroup.centralizer ({b₀} : Set G) :=
      (Subgroup.map_mono hs).trans (by
        simpa [Set.image_singleton, hι'_sθ] using
          Subgroup.map_centralizer_le_centralizer_image
            ({rootThree .E8 F (highRoot .E8)} : Set (adjointGroup .E8 F)) ι')
    have h2 : (EPilot.perpLevi .E8 F).map ι' ≤ Y :=
      (Subgroup.map_le_range ι' _).trans_eq hι'_rangeY
    exact (le_inf h1 h2).trans_eq h.cap
  have hDperf : ⁅(EPilot.perpLevi .E8 F).map ι', (EPilot.perpLevi .E8 F).map ι'⁆ =
      (EPilot.perpLevi .E8 F).map ι' := by
    have hDD : ⁅EPilot.perpLevi .E8 F, EPilot.perpLevi .E8 F⁆ = EPilot.perpLevi .E8 F := by
      rw [← Subgroup.map_subtype_commutator (EPilot.perpLevi .E8 F),
        commutator_perpLevi_E8_eq_top, Subgroup.map_top, Subgroup.range_subtype]
    rw [← Subgroup.map_commutator (EPilot.perpLevi .E8 F) (EPilot.perpLevi .E8 F) ι', hDD]
  have hDcard : Nat.card ((EPilot.perpLevi .E8 F).map ι') = Nat.card K := by
    rw [Subgroup.card_map_of_injective hι'_inj]
    obtain ⟨e⟩ := nonempty_mulEquiv_perpLevi_E8 (K := F)
    exact (Nat.card_congr e.toEquiv).trans hKcard.symm
  have hDmap_eq_K : (EPilot.perpLevi .E8 F).map ι' = K :=
    eq_of_le_sup_zpowers_of_card_eq h.std.2.1.1.2.1 hDle hDperf hDcard
  have hs79 : s79A Row.E7 B ≤ K := by
    change Subgroup.closure
      ({B.b 1 * B.b 2 * B.b 3, B.b 4 * B.b 5, B.b 6 * B.b 7} : Set G) ≤ K
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact K.mul_mem (K.mul_mem (h.adapted.2.2 1 (by decide))
        (h.adapted.2.2 2 (by decide))) (h.adapted.2.2 3 (by decide))
    · exact K.mul_mem (h.adapted.2.2 4 (by decide)) (h.adapted.2.2 5 (by decide))
    · exact K.mul_mem (h.adapted.2.2 6 (by decide)) (h.adapted.2.2 7 (by decide))
  refine ⟨ι', hι'_inj, hι'_rangeY, ?_, ?_⟩
  · simpa [rowRootElt] using hι'_sθ
  · rw [hDmap_eq_K]
    exact hs79

end Row

end CFSG.StandardType.FrameRoute.FS81

end
