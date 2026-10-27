module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.CGT.Timmesfeld75 CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace ElevenNine

theorem c118_of_hyp11 (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (D : Data G)
    {V₀ V : Subgroup G} (hV : F11.Hyp11 D V₀ V) (h116 : C116 D V₀ V) (h117 : C117 D V₀ V) :
    C118 D V₀ V := by
  obtain ⟨hn, hO, hXM⟩ := hyp11_ctilde D hV
  have h116V := h116.2
  unfold C117 at h117
  unfold C118
  generalize F11.CTilde D.M V₀ V = X at hn hO hXM h116V h117 ⊢
  haveI hNn : (barImage D.M X).Normal := uc22p22u_barImage_normal hn
  refine uc22p22u_sub_le_cent_layer (barImage D.M X) _ h116V ?_
  intro C hC y hy
  obtain ⟨K, hK, hKbar⟩ :=
    uc22p21c_exists_calC_of_component D.M (uc22p22u_isComponent_map_subtype _ hC)
  have hKM : K ≤ D.M := s13_le_of_mem_calC hK
  have hbarle : barImage D.M K ≤ barImage D.M X := hKbar ▸ Subgroup.map_subtype_le C
  have hKX : K ≤ X := by
    intro k hk
    refine uc22p22u_barPreimage_le hO hbarle (uc22p21c_mem_barPreimage.2 ⟨hKM hk, ?_⟩)
    exact uc22p21c_mem_barImage.2 ⟨⟨k, hKM hk⟩, hk, rfl⟩
  obtain ⟨hMK, hthin⟩ := h117 K (uc22p22u_calC_of_le hK hKX hXM)
  haveI hKn : (barImage D.M K).Normal := uc22p22u_barImage_normal hMK
  obtain ⟨c, hcK, hc⟩ := uc22p22u_acts_inner (barImage D.M K) ⊤
    (le_of_eq (Subgroup.normalizer_eq_top_iff.2 hKn).symm)
    (uc22p22u_outAbelian_thin hThin hCyc D hK hthin) y hy
  rw [hKbar] at hcK
  obtain ⟨c', hc', rfl⟩ := hcK
  exact ⟨c', hc', fun x hx => hc x (hKbar ▸ ⟨x, hx, rfl⟩)⟩

end ElevenNine

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
