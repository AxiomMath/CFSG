module

public import CFSG.LocalAnalysis.StandardType.GGFinModelBCTwGen

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.StandardType CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.HardMathSupport.Timmesfeld.LangTorus

section TwLe

theorem ggBC_twistedE6_le
    (n f : ℕ) (hf : 1 ≤ f) (β : Fin (Tag.rank .F4) → ℤ) :
    ((ggU .twistedE6 n f).D.rootGroup β).map (ggIotaK .twistedE6 n f hf) ≤
      twistedRootSubgroup {a : Fin (langTag .twistedE6).rank → ℤ | IsRoot (langTag .twistedE6) a}
        CFSG.LieType.Steinberg.TwistedE6.orbitMap
        (CFSG.Blueprint.Chevalley.rootSubgroup (langTag .twistedE6) GGL)
        (ggPhi .twistedE6 f) β := by
  rw [Subgroup.map_le_iff_le_comap]
  have hmap_root : ∀ {α : Fin (Tag.rank .E6) → ℤ}, IsRoot .E6 α →
      (e6Data_valid.rootGroup (GaloisField 2 (2 * f)) α).map (ggTwPsi f) ≤
        CFSG.Blueprint.Chevalley.rootSubgroup (langTag .twistedE6) GGL α := by
    intro α hα x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup (GaloisField 2 (2 * f))).1 hy
    rw [ggTwPsi_xm f hα c]
    exact (mem_rootSubgroup (τ := langTag .twistedE6) (R := GGL)).2 ⟨ggRatEmb (2 * f) c, rfl⟩
  intro g hg
  rw [Subgroup.mem_comap]
  change g ∈ twistedRootGroup (GaloisField 2 (2 * f)) (frobQ 2 f) β at hg
  simp only [twistedRootGroup, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hg
  obtain ⟨hg1, hg2⟩ := hg
  rw [ggIotaK_twistedE6_apply n f hf g]
  let h : e6Data_valid.minGroup (GaloisField 2 (2 * f)) :=
    (fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)).subtype g
  have hfix : sigma (GaloisField 2 (2 * f)) (frobQ 2 f) h = h := hg2
  have hm : (⨆ α ∈ {a : Fin (Tag.rank .E6) → ℤ | IsRoot .E6 a},
      ⨆ (_ : ∃ c : ℕ, 0 < c ∧
        orbitSum CFSG.LieType.Steinberg.TwistedE6.orbitMap α = c • β),
      e6Data_valid.rootGroup (GaloisField 2 (2 * f)) α).map (ggTwPsi f) ≤
    ⨆ α ∈ {a : Fin (langTag .twistedE6).rank → ℤ | IsRoot (langTag .twistedE6) a},
      ⨆ (_ : ∃ c : ℕ, 0 < c ∧
        orbitSum CFSG.LieType.Steinberg.TwistedE6.orbitMap α = c • β),
      CFSG.Blueprint.Chevalley.rootSubgroup (langTag .twistedE6) GGL α := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun α => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hα => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hc => ?_
    exact (hmap_root hα).trans
      (le_iSup_of_le α (le_iSup_of_le hα (le_iSup_of_le hc le_rfl)))
  refine ⟨?_, ?_⟩
  · exact hm (Subgroup.mem_map.mpr ⟨h, hg1, rfl⟩)
  · show ggPhi .twistedE6 f (ggTwPsi f h) = ggTwPsi f h
    rw [ggTwPsi_sigma f h, hfix]

end TwLe

end CFSG.StandardType.GGFinModel
