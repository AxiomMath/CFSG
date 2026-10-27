module

public import CFSG.LocalAnalysis.StandardType.GGFinModelBCTwClass
public import CFSG.LocalAnalysis.StandardType.GGFinModelBCTwGen
public import CFSG.LocalAnalysis.StandardType.GGFinModelBCTwLe
public import CFSG.LocalAnalysis.StandardType.GGFinModelBCTwLong
public import CFSG.LocalAnalysis.StandardType.GGFinModelBCTwShort

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.StandardType CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.HardMathSupport.Timmesfeld.LangTorus

section Tw

theorem ggBC_twistedE6_ge
    (n f : ℕ) (hf : 1 ≤ f) (β : Fin (Tag.rank .F4) → ℤ)
    (hβ : β ∈ (ggU .twistedE6 n f).D.roots) :
    twistedRootSubgroup {a : Fin (langTag .twistedE6).rank → ℤ | IsRoot (langTag .twistedE6) a}
        CFSG.LieType.Steinberg.TwistedE6.orbitMap
        (CFSG.Blueprint.Chevalley.rootSubgroup (langTag .twistedE6) GGL)
        (ggPhi .twistedE6 f) β ≤
      ((ggU .twistedE6 n f).D.rootGroup β).map (ggIotaK .twistedE6 n f hf) := by
  intro y hy
  unfold twistedRootSubgroup at hy
  obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
  have hfix : ggPhi .twistedE6 f y = y := hy2
  have hβ' : IsRoot .F4 β := isRoot_iff_mem_roots.mpr hβ
  obtain ⟨a, ha, hiff, hcases⟩ := ggTwClass β hβ'
  have hcond_a : ∃ c : ℕ, 0 < c ∧ orbitSum orbitMap a = c • β :=
    (hiff a ha).2 (Or.inl rfl)
  have hcond_ρ : ∃ c : ℕ, 0 < c ∧ orbitSum orbitMap (rho a) = c • β :=
    (hiff (rho a) (isRoot_rho ha)).2 (Or.inr rfl)
  have hmem_sup : y ∈ CFSG.Blueprint.Chevalley.rootSubgroup (langTag .twistedE6) GGL a ⊔
      CFSG.Blueprint.Chevalley.rootSubgroup (langTag .twistedE6) GGL (rho a) := by
    have hle : (⨆ α ∈ {a : Fin (langTag .twistedE6).rank → ℤ |
          IsRoot (langTag .twistedE6) a},
        ⨆ (_ : ∃ c : ℕ, 0 < c ∧ orbitSum orbitMap α = c • β),
          CFSG.Blueprint.Chevalley.rootSubgroup (langTag .twistedE6) GGL α) ≤
        CFSG.Blueprint.Chevalley.rootSubgroup (langTag .twistedE6) GGL a ⊔
          CFSG.Blueprint.Chevalley.rootSubgroup (langTag .twistedE6) GGL (rho a) := by
      refine iSup_le fun α => iSup_le fun hα => iSup_le fun hc => ?_
      rcases (hiff α hα).1 hc with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    exact hle hy1
  by_cases hρ : rho a = a
  · have hy_a : y ∈ CFSG.Blueprint.Chevalley.rootSubgroup (langTag .twistedE6) GGL a := by
      simpa [hρ] using hmem_sup
    obtain ⟨g, hgroot, hgfix, hgy⟩ := ggTwDescent_long f hf ha hρ hy_a hfix
    refine Subgroup.mem_map.2 ⟨⟨g, hgfix⟩, ?_, ?_⟩
    · change g ∈ twistedRootSubgroup {α : Fin (Tag.rank .E6) → ℤ | IsRoot .E6 α} orbitMap
        (e6Data_valid.rootGroup (GaloisField 2 (2 * f)))
        (sigma (GaloisField 2 (2 * f)) (frobQ 2 f)) β
      refine Subgroup.mem_inf.2 ⟨?_, hgfix⟩
      exact Subgroup.mem_iSup_of_mem a (Subgroup.mem_iSup_of_mem ha
        (Subgroup.mem_iSup_of_mem hcond_a hgroot))
    · rw [ggIotaK_twistedE6_apply n f hf ⟨g, hgfix⟩]
      exact hgy
  · obtain ⟨hsum, hzero⟩ := hcases.resolve_left hρ
    obtain ⟨g, hgroot, hgfix, hgy⟩ :=
      ggTwDescent_short f hf ha hρ hsum hzero hmem_sup hfix
    refine Subgroup.mem_map.2 ⟨⟨g, hgfix⟩, ?_, ?_⟩
    · change g ∈ twistedRootSubgroup {α : Fin (Tag.rank .E6) → ℤ | IsRoot .E6 α} orbitMap
        (e6Data_valid.rootGroup (GaloisField 2 (2 * f)))
        (sigma (GaloisField 2 (2 * f)) (frobQ 2 f)) β
      refine Subgroup.mem_inf.2 ⟨?_, hgfix⟩
      have hle : e6Data_valid.rootGroup (GaloisField 2 (2 * f)) a ⊔
            e6Data_valid.rootGroup (GaloisField 2 (2 * f)) (rho a) ≤
          (⨆ α ∈ {a : Fin (Tag.rank .E6) → ℤ | IsRoot .E6 a},
            ⨆ (_ : ∃ c : ℕ, 0 < c ∧ orbitSum orbitMap α = c • β),
              e6Data_valid.rootGroup (GaloisField 2 (2 * f)) α) :=
        sup_le
          (le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le hcond_a le_rfl)))
          (le_iSup_of_le (rho a)
            (le_iSup_of_le (isRoot_rho ha) (le_iSup_of_le hcond_ρ le_rfl)))
      exact hle hgroot
    · rw [ggIotaK_twistedE6_apply n f hf ⟨g, hgfix⟩]
      exact hgy

theorem ggBC_twistedE6
    (n f : ℕ) (hf : 1 ≤ f) (β : Fin (Tag.rank .F4) → ℤ)
    (hβ : β ∈ (ggU .twistedE6 n f).D.roots) :
    ((ggU .twistedE6 n f).D.rootGroup β).map (ggIotaK .twistedE6 n f hf) =
      twistedRootSubgroup {a : Fin (langTag .twistedE6).rank → ℤ | IsRoot (langTag .twistedE6) a}
        CFSG.LieType.Steinberg.TwistedE6.orbitMap
        (CFSG.Blueprint.Chevalley.rootSubgroup (langTag .twistedE6) GGL)
        (ggPhi .twistedE6 f) β :=
  le_antisymm (ggBC_twistedE6_le n f hf β) (ggBC_twistedE6_ge n f hf β hβ)

end Tw

end CFSG.StandardType.GGFinModel
