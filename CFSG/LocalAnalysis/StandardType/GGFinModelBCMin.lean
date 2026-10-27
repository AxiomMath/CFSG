module

public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs
public import CFSG.LocalAnalysis.StandardType.GGFinModelBCIso

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.StandardType CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.HardMathSupport.Timmesfeld.LangTorus

section Min

private noncomputable abbrev ggIotaK_E6_min_aux
    (n f : ℕ) (hf : 1 ≤ f) :
    ↥(e6Data_valid.minGroup (GaloisField 2 f)) →* ModGL (langTag .E6) GGL :=
  ggIotaK .E6 n f hf

private noncomputable abbrev ggIotaK_E7_min_aux
    (n f : ℕ) (hf : 1 ≤ f) :
    ↥(e7Data_valid.minGroup (GaloisField 2 f)) →* ModGL (langTag .E7) GGL :=
  ggIotaK .E7 n f hf

private theorem ggIotaK_E6_min_apply_aux
    (n f : ℕ) (hf : 1 ≤ f)
    (x : ↥(e6Data_valid.minGroup (GaloisField 2 f))) :
    ggIotaK_E6_min_aux n f hf x =
      baseChangeGL (ggRatEmb f)
        (e6Isogeny (GaloisField 2 f) x : ModGL Tag.E6 (GaloisField 2 f)) := by
  change ggIota .E6 n f hf (QuotientGroup.mk x) = _
  exact ggIota_E6_mk n f hf x

private theorem ggIotaK_E7_min_apply_aux
    (n f : ℕ) (hf : 1 ≤ f)
    (x : ↥(e7Data_valid.minGroup (GaloisField 2 f))) :
    ggIotaK_E7_min_aux n f hf x =
      baseChangeGL (ggRatEmb f)
        ((e7Isogeny (GaloisField 2 f) x : ↥(adjointGroup .E7 (GaloisField 2 f))) :
          ModGL Tag.E7 (GaloisField 2 f)) := by
  change ggIota .E7 n f hf (QuotientGroup.mk x) = _
  exact ggIota_E7_mk n f hf x

private theorem ggIsRoot_E6_aux
    (n f : ℕ) (β : Fin (ggU .E6 n f).D.rank → ℤ)
    (hβ : β ∈ (ggU .E6 n f).D.roots) : IsRoot Tag.E6 β := by
  have h := hβ
  change β ∈ (e6Data_valid.minDatum isFiniteType_cartan_E6 (GaloisField 2 f)).roots at h
  exact (e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 (GaloisField 2 f)).1 h

private theorem ggIsRoot_E7_aux
    (n f : ℕ) (β : Fin (ggU .E7 n f).D.rank → ℤ)
    (hβ : β ∈ (ggU .E7 n f).D.roots) : IsRoot Tag.E7 β := by
  have h := hβ
  change β ∈ (e7Data_valid.minDatum isFiniteType_cartan_E7 (GaloisField 2 f)).roots at h
  exact (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField 2 f)).1 h

private theorem ggReidx_E6_aux
    (n f : ℕ) (β : Fin (ggU .E6 n f).D.rank → ℤ) :
    ggLangReidx (ggRank_untw (Or.inr (Or.inl rfl)) n f) β = β :=
  rfl

private theorem ggReidx_E7_aux
    (n f : ℕ) (β : Fin (ggU .E7 n f).D.rank → ℤ) :
    ggLangReidx (ggRank_untw (Or.inr (Or.inr (Or.inl rfl))) n f) β = β :=
  rfl

private theorem ggBC_param_E6_clean
    (n f : ℕ) (hf : 1 ≤ f) (β : Fin Tag.E6.rank → ℤ)
    (hβ : IsRoot Tag.E6 β) :
    ((e6Data_valid.rootGroup (GaloisField 2 f) β).map (ggIotaK_E6_min_aux n f hf) :
        Set (ModGL (langTag .E6) GGL)) =
      Set.range (fun c : GaloisField 2 f =>
        pinnedX (langTag .E6) GGL β (ggRatEmb f c)) := by
  ext y
  constructor
  · rintro ⟨x, hx, hy⟩
    obtain ⟨c, hc⟩ := (e6Data_valid.mem_rootGroup (k := GaloisField 2 f)).1 hx
    refine ⟨c, ?_⟩
    have h : ggIotaK_E6_min_aux n f hf (e6Data_valid.xm (GaloisField 2 f) β c) =
        pinnedX (langTag .E6) GGL β (ggRatEmb f c) := by
      rw [ggIotaK_E6_min_apply_aux, ggE6_isogeny_xm_pinned (GaloisField 2 f) hβ c]
      exact baseChangeGL_pinnedX (ggRatEmb f) β c
    rw [hc] at h
    rw [h] at hy
    exact hy
  · rintro ⟨c, rfl⟩
    refine ⟨e6Data_valid.xm (GaloisField 2 f) β c, ?_, ?_⟩
    · exact e6Data_valid.xm_mem_rootGroup (GaloisField 2 f) β c
    · rw [ggIotaK_E6_min_apply_aux, ggE6_isogeny_xm_pinned (GaloisField 2 f) hβ c]
      exact baseChangeGL_pinnedX (ggRatEmb f) β c

private theorem ggBC_param_E7_clean
    (n f : ℕ) (hf : 1 ≤ f) (β : Fin Tag.E7.rank → ℤ)
    (hβ : IsRoot Tag.E7 β) :
    ((e7Data_valid.rootGroup (GaloisField 2 f) β).map (ggIotaK_E7_min_aux n f hf) :
        Set (ModGL (langTag .E7) GGL)) =
      Set.range (fun c : GaloisField 2 f =>
        pinnedX (langTag .E7) GGL β (ggRatEmb f c)) := by
  ext y
  constructor
  · rintro ⟨x, hx, hy⟩
    obtain ⟨c, hc⟩ := (e7Data_valid.mem_rootGroup (k := GaloisField 2 f)).1 hx
    refine ⟨c, ?_⟩
    have h : ggIotaK_E7_min_aux n f hf (e7Data_valid.xm (GaloisField 2 f) β c) =
        pinnedX (langTag .E7) GGL β (ggRatEmb f c) := by
      rw [ggIotaK_E7_min_apply_aux, ggE7_isogeny_xm_pinned (GaloisField 2 f) hβ c]
      exact baseChangeGL_pinnedX (ggRatEmb f) β c
    rw [hc] at h
    rw [h] at hy
    exact hy
  · rintro ⟨c, rfl⟩
    refine ⟨e7Data_valid.xm (GaloisField 2 f) β c, ?_, ?_⟩
    · exact e7Data_valid.xm_mem_rootGroup (GaloisField 2 f) β c
    · rw [ggIotaK_E7_min_apply_aux, ggE7_isogeny_xm_pinned (GaloisField 2 f) hβ c]
      exact baseChangeGL_pinnedX (ggRatEmb f) β c

theorem ggBC_param_E6
    (n f : ℕ) (hf : 1 ≤ f) (β : Fin (ggU .E6 n f).D.rank → ℤ)
    (hβ : β ∈ (ggU .E6 n f).D.roots) :
    (((ggU .E6 n f).D.rootGroup β).map (ggIotaK .E6 n f hf) :
        Set (ModGL (langTag .E6) GGL)) =
      Set.range (fun c : GaloisField 2 f =>
        pinnedX (langTag .E6) GGL (ggLangReidx (ggRank_untw (Or.inr (Or.inl rfl)) n f) β)
          (ggRatEmb f c)) := by
  rw [ggReidx_E6_aux n f β]
  exact ggBC_param_E6_clean n f hf β (ggIsRoot_E6_aux n f β hβ)

theorem ggBC_param_E7
    (n f : ℕ) (hf : 1 ≤ f) (β : Fin (ggU .E7 n f).D.rank → ℤ)
    (hβ : β ∈ (ggU .E7 n f).D.roots) :
    (((ggU .E7 n f).D.rootGroup β).map (ggIotaK .E7 n f hf) :
        Set (ModGL (langTag .E7) GGL)) =
      Set.range (fun c : GaloisField 2 f =>
        pinnedX (langTag .E7) GGL (ggLangReidx (ggRank_untw (Or.inr (Or.inr (Or.inl rfl))) n f) β)
          (ggRatEmb f c)) := by
  rw [ggReidx_E7_aux n f β]
  exact ggBC_param_E7_clean n f hf β (ggIsRoot_E7_aux n f β hβ)

end Min

end CFSG.StandardType.GGFinModel
