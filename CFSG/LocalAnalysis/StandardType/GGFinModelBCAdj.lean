module

public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.StandardType CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus

section Adj

private theorem eltElement_eq_pinnedX
    (τ : Tag) (f : ℕ) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (c : GaloisField 2 f) :
    ((rootOperatorFamily τ).eltElement (K := GaloisField 2 f) ⟨β, hβ⟩ c :
        ModGL τ (GaloisField 2 f)) = pinnedX τ (GaloisField 2 f) β c := by
  have h2 : (2 : GaloisField 2 f) = 0 := CharP.cast_eq_zero (GaloisField 2 f) 2
  have hs : (((rootOperatorFamily τ).pinnedFamilySign β : ℤ) : GaloisField 2 f) = 1 := by
    rcases (rootOperatorFamily τ).pinnedFamilySign_eq β with h | h <;> rw [h]
    · exact Int.cast_one
    · rw [Int.cast_neg, Int.cast_one]
      linear_combination -h2
  rw [(rootOperatorFamily τ).coe_eltElement,
    (rootOperatorFamily τ).pinnedX_eq_eltUnit (GaloisField 2 f) hβ c, hs, one_mul]

private theorem ggIotaK_F4_apply
    (n f : ℕ) (hf : 1 ≤ f)
    (g : ↥(adjointGroup Tag.F4 (GaloisField 2 f))) :
    ggIotaK .F4 n f hf g =
      baseChangeGL (ggRatEmb f) (g : ModGL Tag.F4 (GaloisField 2 f)) := by
  rfl

private theorem ggIotaK_E8_apply
    (n f : ℕ) (hf : 1 ≤ f)
    (g : ↥(adjointGroup Tag.E8 (GaloisField 2 f))) :
    ggIotaK .E8 n f hf g =
      baseChangeGL (ggRatEmb f) (g : ModGL Tag.E8 (GaloisField 2 f)) := by
  rfl

theorem ggBC_param_F4
    (n f : ℕ) (hf : 1 ≤ f) (β : Fin (ggU .F4 n f).D.rank → ℤ)
    (hβ : β ∈ (ggU .F4 n f).D.roots) :
    (((ggU .F4 n f).D.rootGroup β).map (ggIotaK .F4 n f hf) :
        Set (ModGL (langTag .F4) GGL)) =
      Set.range (fun c : GaloisField 2 f =>
        pinnedX (langTag .F4) GGL (ggLangReidx (ggRank_untw (Or.inl rfl) n f) β)
          (ggRatEmb f c)) := by
  have hβ' : β ∈ (adjDatum (rootOperatorFamily Tag.F4) (GaloisField 2 f)).roots := hβ
  have hroot : IsRoot Tag.F4 β := mem_adjDatum_roots.1 hβ'
  have hreidx : ggLangReidx (ggRank_untw (Or.inl rfl) n f) β = β := rfl
  rw [hreidx]
  ext x
  constructor
  · intro hx
    rw [SetLike.mem_coe, Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨c, hc⟩ := (mem_rootGroup_iff hroot y).1 hy
    refine ⟨c, ?_⟩
    rw [← hc, ggIotaK_F4_apply n f hf, xPar_of_isRoot hroot c,
      eltElement_eq_pinnedX Tag.F4 f hroot c]
    exact (baseChangeGL_pinnedX (τ := Tag.F4) (ggRatEmb f) β c).symm
  · rintro ⟨c, rfl⟩
    refine ⟨xPar (rootOperatorFamily Tag.F4) β c, xPar_mem hroot c, ?_⟩
    rw [ggIotaK_F4_apply n f hf, xPar_of_isRoot hroot c,
      eltElement_eq_pinnedX Tag.F4 f hroot c]
    exact baseChangeGL_pinnedX (τ := Tag.F4) (ggRatEmb f) β c

theorem ggBC_param_E8
    (n f : ℕ) (hf : 1 ≤ f) (β : Fin (ggU .E8 n f).D.rank → ℤ)
    (hβ : β ∈ (ggU .E8 n f).D.roots) :
    (((ggU .E8 n f).D.rootGroup β).map (ggIotaK .E8 n f hf) :
        Set (ModGL (langTag .E8) GGL)) =
      Set.range (fun c : GaloisField 2 f =>
        pinnedX (langTag .E8) GGL (ggLangReidx (ggRank_untw (Or.inr (Or.inr (Or.inr rfl))) n f) β)
          (ggRatEmb f c)) := by
  have hβ' : β ∈ (adjDatum (rootOperatorFamily Tag.E8) (GaloisField 2 f)).roots := hβ
  have hroot : IsRoot Tag.E8 β := mem_adjDatum_roots.1 hβ'
  have hreidx : ggLangReidx (ggRank_untw (Or.inr (Or.inr (Or.inr rfl))) n f) β = β := rfl
  rw [hreidx]
  ext x
  constructor
  · intro hx
    rw [SetLike.mem_coe, Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨c, hc⟩ := (mem_rootGroup_iff hroot y).1 hy
    refine ⟨c, ?_⟩
    rw [← hc, ggIotaK_E8_apply n f hf, xPar_of_isRoot hroot c,
      eltElement_eq_pinnedX Tag.E8 f hroot c]
    exact (baseChangeGL_pinnedX (τ := Tag.E8) (ggRatEmb f) β c).symm
  · rintro ⟨c, rfl⟩
    refine ⟨xPar (rootOperatorFamily Tag.E8) β c, xPar_mem hroot c, ?_⟩
    rw [ggIotaK_E8_apply n f hf, xPar_of_isRoot hroot c,
      eltElement_eq_pinnedX Tag.E8 f hroot c]
    exact baseChangeGL_pinnedX (τ := Tag.E8) (ggRatEmb f) β c

end Adj

end CFSG.StandardType.GGFinModel
