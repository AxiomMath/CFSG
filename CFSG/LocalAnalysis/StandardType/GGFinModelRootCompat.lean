module

public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs
public import CFSG.LocalAnalysis.StandardType.GGFinModelBCAdj
public import CFSG.LocalAnalysis.StandardType.GGFinModelBCMin
public import CFSG.LocalAnalysis.StandardType.GGFinModelBCTw

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.StandardType CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors

section RootCompat

private theorem ggReidx_F4_aux
    (n f : ℕ) (β : Fin (ggU .F4 n f).D.rank → ℤ) :
    ggLangReidx (ggRank_untw (Or.inl rfl) n f) β = β :=
  rfl

private theorem ggReidx_E6_aux
    (n f : ℕ) (β : Fin (ggU .E6 n f).D.rank → ℤ) :
    ggLangReidx (ggRank_untw (Or.inr (Or.inl rfl)) n f) β = β :=
  rfl

private theorem ggReidx_E7_aux
    (n f : ℕ) (β : Fin (ggU .E7 n f).D.rank → ℤ) :
    ggLangReidx (ggRank_untw (Or.inr (Or.inr (Or.inl rfl))) n f) β = β :=
  rfl

private theorem ggReidx_E8_aux
    (n f : ℕ) (β : Fin (ggU .E8 n f).D.rank → ℤ) :
    ggLangReidx (ggRank_untw (Or.inr (Or.inr (Or.inr rfl))) n f) β = β :=
  rfl

private theorem ggIsRoot_reidx_F4_aux
    (n f : ℕ) (β : Fin (ggU .F4 n f).D.rank → ℤ)
    (hβ : β ∈ (ggU .F4 n f).D.roots) :
    IsRoot (langTag .F4) (ggLangReidx (ggRank_untw (Or.inl rfl) n f) β) := by
  have hroot : IsRoot Tag.F4 β :=
    (mem_rootFinset (τ := Tag.F4)).mp ((mem_roots_F4 n f β).mp hβ)
  rw [ggReidx_F4_aux n f β]
  exact hroot

private theorem ggIsRoot_reidx_E6_aux
    (n f : ℕ) (β : Fin (ggU .E6 n f).D.rank → ℤ)
    (hβ : β ∈ (ggU .E6 n f).D.roots) :
    IsRoot (langTag .E6) (ggLangReidx (ggRank_untw (Or.inr (Or.inl rfl)) n f) β) := by
  have hroot : IsRoot Tag.E6 β :=
    (mem_rootFinset (τ := Tag.E6)).mp ((mem_roots_E6 n f β).mp hβ)
  rw [ggReidx_E6_aux n f β]
  exact hroot

private theorem ggIsRoot_reidx_E7_aux
    (n f : ℕ) (β : Fin (ggU .E7 n f).D.rank → ℤ)
    (hβ : β ∈ (ggU .E7 n f).D.roots) :
    IsRoot (langTag .E7) (ggLangReidx (ggRank_untw (Or.inr (Or.inr (Or.inl rfl))) n f) β) := by
  have hroot : IsRoot Tag.E7 β :=
    (mem_rootFinset (τ := Tag.E7)).mp ((mem_roots_E7 n f β).mp hβ)
  rw [ggReidx_E7_aux n f β]
  exact hroot

private theorem ggIsRoot_reidx_E8_aux
    (n f : ℕ) (β : Fin (ggU .E8 n f).D.rank → ℤ)
    (hβ : β ∈ (ggU .E8 n f).D.roots) :
    IsRoot (langTag .E8) (ggLangReidx (ggRank_untw (Or.inr (Or.inr (Or.inr rfl))) n f) β) := by
  have hroot : IsRoot Tag.E8 β :=
    (mem_rootFinset (τ := Tag.E8)).mp ((mem_roots_E8 n f β).mp hβ)
  rw [ggReidx_E8_aux n f β]
  exact hroot

theorem ggBC_untw_param
    {t : StatedLieTag} (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (n f : ℕ) (hf : 1 ≤ f) (β : Fin (ggU t n f).D.rank → ℤ) (hβ : β ∈ (ggU t n f).D.roots) :
    (((ggU t n f).D.rootGroup β).map (ggIotaK t n f hf) : Set (ModGL (langTag t) GGL)) =
      Set.range (fun c : GaloisField 2 f =>
        pinnedX (langTag t) GGL (ggLangReidx (ggRank_untw ht n f) β) (ggRatEmb f c)) := by
  rcases ht with rfl | rfl | rfl | rfl
  · exact ggBC_param_F4 n f hf β hβ
  · exact ggBC_param_E6 n f hf β hβ
  · exact ggBC_param_E7 n f hf β hβ
  · exact ggBC_param_E8 n f hf β hβ

theorem ggBC_untw
    {t : StatedLieTag} (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) (n f : ℕ)
    (hf : 1 ≤ f) (β : Fin (ggU t n f).D.rank → ℤ) (hβ : β ∈ (ggU t n f).D.roots) :
    ((ggU t n f).D.rootGroup β).map (ggIotaK t n f hf) =
      ggFixGp t f ⊓ CFSG.Blueprint.Chevalley.rootSubgroup (langTag t) GGL
        (ggLangReidx (ggRank_untw ht n f) β) := by
  rcases ht with rfl | rfl | rfl | rfl
  · apply SetLike.coe_injective
    rw [ggBC_untw_param (Or.inl rfl) n f hf β hβ,
      ggFixGp_inf_rootSubgroup_untw (Or.inl rfl) hf (ggIsRoot_reidx_F4_aux n f β hβ)]
  · apply SetLike.coe_injective
    rw [ggBC_untw_param (Or.inr (Or.inl rfl)) n f hf β hβ,
      ggFixGp_inf_rootSubgroup_untw (Or.inr (Or.inl rfl)) hf (ggIsRoot_reidx_E6_aux n f β hβ)]
  · apply SetLike.coe_injective
    rw [ggBC_untw_param (Or.inr (Or.inr (Or.inl rfl))) n f hf β hβ,
      ggFixGp_inf_rootSubgroup_untw (Or.inr (Or.inr (Or.inl rfl))) hf
        (ggIsRoot_reidx_E7_aux n f β hβ)]
  · apply SetLike.coe_injective
    rw [ggBC_untw_param (Or.inr (Or.inr (Or.inr rfl))) n f hf β hβ,
      ggFixGp_inf_rootSubgroup_untw (Or.inr (Or.inr (Or.inr rfl))) hf
        (ggIsRoot_reidx_E8_aux n f β hβ)]

end RootCompat

end CFSG.StandardType.GGFinModel
