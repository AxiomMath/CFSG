module

public import CFSG.Quasithin.Background.SimsD1TransBlock
public import CFSG.Quasithin.Background.SimsD1Transport
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.SimsD1.FourBlocksGen

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.SimsD1.Transport

section Img

variable {G F : Type} [Group G] [Group F] {H : Subgroup G} {ι : ↥H →* F}

theorem prodA3_img_iff (hι : Function.Injective ι) {K Y : Subgroup G} (hK : K ≤ H)
    (hY : Y ≤ H) :
    (∃ S : Finset (Subgroup F), (∀ L ∈ S, IsBlock2 (img ι K) L ∧ IsAltType L 3) ∧
      img ι Y = ⨆ L ∈ S, L) ↔
    (∃ S : Finset (Subgroup G), (∀ L ∈ S, IsBlock2 K L ∧ IsAltType L 3) ∧ Y = ⨆ L ∈ S, L) := by
  obtain ⟨K, rfl⟩ := exists_map_subtype hK
  obtain ⟨Y, rfl⟩ := exists_map_subtype hY
  rw [img_map_subtype, img_map_subtype, TransBlock.prodA3_map_iff _ hι,
    TransBlock.prodA3_map_iff _ H.subtype_injective]

end Img

variable {G : Type} [Group G] {G₁ G₂ T V M₂ : Subgroup G}

end CFSG.Quasithin.SimsD1.FourBlocksGen
