module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ExcNC
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionExceptional
public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms

public section

namespace CFSG.StandardType

open CFSG.Open

theorem ggRootNoCentralAt_top_map_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    {R : Subgroup G} (h : GGRootNoCentralAt (⊤ : Subgroup G) R) :
    GGRootNoCentralAt (⊤ : Subgroup H) (R.map e.toMonoidHom) := by
  intro A B hRA hAB hB hNA hNB hc
  simp only [top_inf_eq] at hB hNA hNB hc
  refine ggRootNormNoCentral_map_mulEquiv e ?_ A B hRA hAB hB hNA hNB hc
  intro A' B' hRA' hAB' hB' hNA' hNB' hc'
  exact h A' B' hRA' hAB' (by simpa only [top_inf_eq] using hB')
    (by simpa only [top_inf_eq] using hNA') (by simpa only [top_inf_eq] using hNB')
    (by simpa only [top_inf_eq] using hc')

theorem ggRootNormNoCentral_subgroupOf_of_noCentralAt {G : Type} [Group G] {K R : Subgroup G}
    (hRK : R ≤ K) (h : GGRootNoCentralAt K R) :
    GGRootNormNoCentral (R.subgroupOf K) := by
  intro A B hRA hAB hBcore hNA hNB hcomm
  set N : Subgroup G := K ⊓ Subgroup.normalizer (R : Set G) with hNdef
  have hNK : Subgroup.normalizer ((R.subgroupOf K : Subgroup K) : Set K) = N.subgroupOf K := by
    rw [hNdef, Subgroup.inf_subgroupOf_left]
    exact (Subgroup.subgroupOf_normalizer_eq hRK).symm
  have hcoreMap :
      (pCoreOf 2 (Subgroup.normalizer ((R.subgroupOf K : Subgroup K) : Set K))).map K.subtype =
        pCoreOf 2 N := by
    rw [hNK, GGRootNorm.pCoreOf_subgroupOf inf_le_left]
    exact Subgroup.map_subgroupOf_eq_of_le ((GGRootNorm.pCoreOf_le N).trans inf_le_left)
  have hnormMap : ∀ {S : Subgroup K},
      Subgroup.normalizer ((R.subgroupOf K : Subgroup K) : Set K) ≤
        Subgroup.normalizer (S : Set K) →
      N ≤ Subgroup.normalizer ((S.map K.subtype : Subgroup G) : Set G) := by
    intro S hS
    rw [Subgroup.le_normalizer_iff]
    intro n hn x hx
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
    have hnK : (⟨n, hn.1⟩ : K) ∈
        Subgroup.normalizer ((R.subgroupOf K : Subgroup K) : Set K) := by
      rw [hNK]
      exact Subgroup.mem_subgroupOf.mpr hn
    have hs' : (⟨n, hn.1⟩ : K) * s * (⟨n, hn.1⟩ : K)⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (hS hnK) s).mp hs
    exact Subgroup.mem_map.mpr ⟨_, hs', by simp⟩
  have hcommMap : ⁅B.map K.subtype, N⁆ ≤ A.map K.subtype := by
    have h1 : (⁅B, Subgroup.normalizer ((R.subgroupOf K : Subgroup K) : Set K)⁆).map K.subtype ≤
        A.map K.subtype := Subgroup.map_mono hcomm
    rwa [Subgroup.map_commutator, hNK, Subgroup.map_subgroupOf_eq_of_le inf_le_left] at h1
  have key := h (A.map K.subtype) (B.map K.subtype)
    (by
      rw [← Subgroup.map_subgroupOf_eq_of_le hRK]
      exact Subgroup.map_mono hRA)
    (Subgroup.map_mono hAB) ((Subgroup.map_mono hBcore).trans (le_of_eq hcoreMap))
    (hnormMap hNA) (hnormMap hNB) hcommMap
  intro b hb
  exact (Subgroup.mem_map_iff_mem K.subtype_injective).mp
    (key (Subgroup.mem_map_of_mem K.subtype hb))

end CFSG.StandardType

namespace CFSG.StandardType.LieKnownR2.ExcNC

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint.Chevalley

private theorem l10sxc_eq_highRoot_of_isRoot
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (h : ∑ i, CFSG.SeitzReduction.highRoot τ i ≤ ∑ i, γ i) :
    γ = CFSG.SeitzReduction.highRoot τ := by
  rcases hτ with rfl | rfl | rfl
  · obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check .E6)).1 hγ
    have hall : (List.range Tag.E6.rootCertificate.roots.length).all fun k =>
        decide (∑ i, CFSG.SeitzReduction.highRoot .E6 i ≤ ∑ i, Tag.E6.rootCertificate.root k i →
          Tag.E6.rootCertificate.root k = CFSG.SeitzReduction.highRoot .E6) := by decide +kernel
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hall
    exact hall k hk h
  · obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check .E7)).1 hγ
    have hall : (List.range Tag.E7.rootCertificate.roots.length).all fun k =>
        decide (∑ i, CFSG.SeitzReduction.highRoot .E7 i ≤ ∑ i, Tag.E7.rootCertificate.root k i →
          Tag.E7.rootCertificate.root k = CFSG.SeitzReduction.highRoot .E7) := by decide +kernel
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hall
    exact hall k hk h
  · obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check .E8)).1 hγ
    have hall : (List.range Tag.E8.rootCertificate.roots.length).all fun k =>
        decide (∑ i, CFSG.SeitzReduction.highRoot .E8 i ≤ ∑ i, Tag.E8.rootCertificate.root k i →
          Tag.E8.rootCertificate.root k = CFSG.SeitzReduction.highRoot .E8) := by decide +kernel
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hall
    exact hall k hk h

private theorem l10sxc_noCentral_maxHeight
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K] [CharP K 2]
    {γ₀ : Fin (adjDatum (rootOperatorFamily τ) K).rank → ℤ}
    (hγ₀ : γ₀ ∈ (adjDatum (rootOperatorFamily τ) K).roots)
    (hmax : ∀ δ ∈ (adjDatum (rootOperatorFamily τ) K).roots, ∑ i, δ i ≤ ∑ i, γ₀ i) :
    GGRootNoCentralAt (⊤ : Subgroup ↥(adjointGroup τ K))
      ((adjDatum (rootOperatorFamily τ) K).rootGroup γ₀) := by
  have hθ : IsRoot τ (CFSG.SeitzReduction.highRoot τ) := CFSG.SeitzReduction.isRoot_highRoot τ
  have hγθ : γ₀ = CFSG.SeitzReduction.highRoot τ :=
    l10sxc_eq_highRoot_of_isRoot hτ (mem_adjDatum_roots.1 hγ₀)
      (hmax (CFSG.SeitzReduction.highRoot τ) (mem_adjDatum_roots.2 hθ))
  have hR : (adjDatum (rootOperatorFamily τ) K).rootGroup γ₀ =
      (rootSubgroup τ K (CFSG.SeitzReduction.highRoot τ)).subgroupOf (adjointGroup τ K) := by
    rw [hγθ]
    change rootGroup (rootOperatorFamily τ) K (CFSG.SeitzReduction.highRoot τ) =
      (rootSubgroup τ K (CFSG.SeitzReduction.highRoot τ)).subgroupOf (adjointGroup τ K)
    rw [rootGroup_of_isRoot hθ]
    exact ((rootOperatorFamily τ).subgroupOf_rootSubgroup_eq K
      ⟨CFSG.SeitzReduction.highRoot τ, hθ⟩).symm
  rw [hR]
  intro A B hRA hAB hB hNA hNB hc
  simp only [top_inf_eq] at hB hNA hNB hc
  exact ggRootNormNoCentral_subgroupOf_of_noCentralAt
    (rootSubgroup_le_adjointGroup (CFSG.SeitzReduction.highRoot τ))
    (rootNoCentral_highRoot_exc τ (by rcases hτ with h | h | h <;> simp [h]) K)
    A B hRA hAB hB hNA hNB hc

theorem rootNoCentral_adj_simplyLaced
    (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : Type) [Field K] [Finite K] [CharP K 2]
    {β : Fin (adjDatum (rootOperatorFamily τ) K).rank → ℤ}
    (hβ : β ∈ (adjDatum (rootOperatorFamily τ) K).roots) :
    GGRootNoCentralAt (⊤ : Subgroup ↥(adjointGroup τ K))
      ((adjDatum (rootOperatorFamily τ) K).rootGroup β) := by
  have hl : GGLongRoot (adjDatum (rootOperatorFamily τ) K) β := by
    rcases hτ with rfl | rfl | rfl
    · exact ggLongRoot_of_symmetric CFSG.ClassicalInvolution.ModelFacts.isIrreducible_E6
        (cartanE_symm 6) rfl hβ
    · exact ggLongRoot_of_symmetric CFSG.ClassicalInvolution.ModelFacts.isIrreducible_E7
        (cartanE_symm 7) rfl hβ
    · exact ggLongRoot_of_symmetric CFSG.ClassicalInvolution.ModelFacts.isIrreducible_E8
        (cartanE_symm 8) rfl hβ
  obtain ⟨w, γ₀, hγ₀, hmax, hβeq⟩ := hl
  have hNC := l10sxc_noCentral_maxHeight hτ hγ₀ hmax
  have hct := adjDatum_isCTGroupDatum (rootOperatorFamily τ) K
  have hact := CFSG.LieType.Steinberg.actsAs_nrep hct w
  have hmap : ((adjDatum (rootOperatorFamily τ) K).rootGroup γ₀).map
      (MulAut.conj (CFSG.LieType.Steinberg.nrep hct w)).toMonoidHom =
        (adjDatum (rootOperatorFamily τ) K).rootGroup β := by
    rw [hact γ₀ hγ₀, ← hβeq]
  have h := ggRootNoCentralAt_top_map_mulEquiv
    (MulAut.conj (CFSG.LieType.Steinberg.nrep hct w)) hNC
  rwa [hmap] at h

end CFSG.StandardType.LieKnownR2.ExcNC
