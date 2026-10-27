module

public import CFSG.LocalAnalysis.StandardType.FS81.RootE8Defs
public import CFSG.LocalAnalysis.StandardType.FS81.S7Model
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotMainLift
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.FS81.S79Radical
import CFSG.LocalAnalysis.StandardType.FS81.RootE8Setting
import CFSG.LocalAnalysis.StandardType.FS81.RootE8A
import CFSG.LocalAnalysis.StandardType.FS81.S7Fusion
import CFSG.LocalAnalysis.StandardType.FS81.S7AutAt
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
local notation "tθ" => EPilot.pinnedElt Tag.E8 (highRoot Tag.E8) (1 : GaloisField 2 1)
local notation "Qθ" => EPilot.highRadical Tag.E8 (GaloisField 2 1)
local notation "Dθ" => EPilot.perpLevi Tag.E8 (GaloisField 2 1)

section Row


theorem pCoreOf_centralizer_eq_of_embedding {G : Type} [Group G] [Finite G] {r : Row}
    (hr : r = Row.E7 ∨ r = Row.twD7) {b₀ : G} {K E : Subgroup G} {B : Basis3 G (r.n + 1)}
    {Y : Subgroup G} (h : RootSetting r b₀ K E B Y)
    (hC : Subgroup.centralizer ({b₀} : Set G) ≤ Y) (ι : adjointGroup .E8 GF₂ →* G)
    (hι : Function.Injective ι) (hrange : ι.range = Y) (hA : s79A r B ≤ (Dθ).map ι) :
    pCoreOf 2 (Subgroup.centralizer ({ι tθ} : Set G)) = (Qθ).map ι := by
  have hr' : r ≠ Row.D6 := by rcases hr with rfl | rfl <;> decide
  have hAut : E8AutAt r := by
    rcases hr with rfl | rfl
    · exact e8AutAt_E7
    · exact e8AutAt_twD7
  let t₀ : G := ι tθ
  let U : Subgroup G := (Qθ).map ι
  let L : Subgroup G := (Dθ).map ι
  have hK2 : Nat.card GF₂ = 2 := natCard_galoisField_two_one
  have ht₀ : orderOf t₀ = 2 := by
    rw [orderOf_injective ι hι]
    exact orderOf_pinnedElt_one (τ := .E8) (K := GF₂) (highRoot .E8)
  have hLY : L ≤ Y := (Subgroup.map_le_range ι _).trans_eq hrange
  have hUY : U ≤ Y := (Subgroup.map_le_range ι _).trans_eq hrange
  have hmapcent := map_le_centralizer_map_pinnedElt_highRoot (K := GF₂) ι
  have hLt₀ : L ≤ Subgroup.centralizer ({t₀} : Set G) := hmapcent.2
  have hUt₀ : U ≤ Subgroup.centralizer ({t₀} : Set G) := hmapcent.1
  have hU2 : IsPGroup 2 U := by
    obtain ⟨-, -, -, hQ, -⟩ := centralizer_pinnedElt_highRoot_E8 (K := GF₂)
    exact hQ.map ι
  have ht₀U : t₀ ∈ U :=
    Subgroup.mem_map_of_mem ι (pinnedElt_highRoot_mem_highRadical (K := GF₂))
  have hUmax : ∀ P : Subgroup G, IsPGroup 2 P →
      P ≤ Subgroup.centralizer ({t₀} : Set G) ⊓ Y →
      Subgroup.centralizer ({t₀} : Set G) ⊓ Y ≤ Subgroup.normalizer (P : Set G) → P ≤ U := by
    intro P hP hPC hN
    exact hUmax_E8_range (K := GF₂) ι hι P hP (by simpa [hrange] using hPC)
      (by simpa [hrange] using hN)
  have hirr : ∀ V : Subgroup G, Subgroup.zpowers t₀ ≤ V → V ≤ U →
      L ≤ Subgroup.normalizer (V : Set G) → V = Subgroup.zpowers t₀ ∨ V = U :=
    hirr_E8_range (K := GF₂) hK2 ι hι (L := L) le_rfl
  have hC' : Subgroup.centralizer ({b₀} : Set G) =
      (⊥ : Subgroup G) ⊔ (Subgroup.centralizer ({b₀} : Set G) ⊓ Y) := by
    rw [inf_eq_left.mpr hC, bot_sup_eq]
  have hRY : (⊥ : Subgroup G) ≤ Subgroup.centralizer (Y : Set G) := bot_le
  exact (s79_radical (R := ⊥) (A := s79A r B) (L := L) (U := U) (t₀ := t₀)
    (b₀ := b₀) h.centralizer_inf_eq_bot hC' hRY
    (fun P hP h1 h2 => h.eq_bot_of_isPGroup_two hP h1 h2)
    ht₀ hLY hLt₀ hU2 ht₀U hUY hUt₀ hUmax hirr
    (isElemAbelian_s79A B) (card_s79A hr' B) hA
    (fun F hF h9 => h.exists_conj_mem_of_le_s79A hr' (hAut G b₀ K E B Y h) hF h9)
    (fun t ht _ => centralizer_inf_le_pCoreOf_of_isCharTwoType h.charTwo ht)).2


end Row

end CFSG.StandardType.FrameRoute.FS81

end
