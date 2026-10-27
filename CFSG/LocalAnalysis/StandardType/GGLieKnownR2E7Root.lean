module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2E7Bridge
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ExcNCRoots
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ExcInner
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ItemThree
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2CoverNC
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortTransport

public section

namespace CFSG.StandardType.LieKnownR2.E7

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.Blueprint.Chevalley

private theorem l10se7_noCentral_root
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {β : Fin (e7Datum K).rank → ℤ} (hβ : β ∈ (e7Datum K).roots) :
    GGRootNoCentralAt (⊤ : Subgroup ↥(e7Data_valid.minGroup K)) ((e7Datum K).rootGroup β) := by
  have hβ' : IsRoot .E7 β := by
    have h := hβ
    rw [MinData.Valid.minDatum_roots] at h
    exact h
  have hadj := ExcNC.rootNoCentral_adj_simplyLaced .E7 (Or.inr (Or.inl rfl)) K
    (β := β) (mem_adjDatum_roots.2 hβ')
  have h := ggRootNoCentralAt_top_map_mulEquiv
    (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K).symm hadj
  have hmap : ((adjDatum (rootOperatorFamily .E7) K).rootGroup β).map
      (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K).symm.toMonoidHom =
        (e7Datum K).rootGroup β := by
    rw [← map_e7MinEquivAdjoint_rootGroup hβ']
    exact GGRootNorm.map_symm_map _ _
  rwa [hmap] at h

private theorem l10se7_inner_root
    {f : ℕ} (hf : 1 ≤ f)
    {β : Fin (e7Datum (GaloisField 2 f)).rank → ℤ} (hβ : β ∈ (e7Datum (GaloisField 2 f)).roots) :
    GGRootNormInner ((e7Datum (GaloisField 2 f)).rootGroup β) := by
  have hβ' : IsRoot .E7 β := by
    have h := hβ
    rw [MinData.Valid.minDatum_roots] at h
    exact h
  have hadj := ExcInner.ggRootNormInner_adj_E78 .E7 (Or.inl rfl) hf (β := β)
    (mem_adjDatum_roots.2 hβ')
  have h := ggRootNormInner_map_mulEquiv
    (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint (GaloisField 2 f)).symm hadj
  have hmap : ((adjDatum (rootOperatorFamily .E7) (GaloisField 2 f)).rootGroup β).map
      (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint (GaloisField 2 f)).symm.toMonoidHom =
        (e7Datum (GaloisField 2 f)).rootGroup β := by
    rw [← map_e7MinEquivAdjoint_rootGroup hβ']
    exact GGRootNorm.map_symm_map _ _
  rwa [hmap] at h

theorem ggRootNormInner_e7
    {n f : ℕ} (hf : 1 ≤ f)
    {β : Fin (ggU .E7 n f).D.rank → ℤ} (hβ : β ∈ (ggU .E7 n f).D.roots)
    (u : (ggU .E7 n f).K) :
    GGRootNormInner (ggRootSub (ggU .E7 n f).D (MonoidHom.id (ggU .E7 n f).K) β u) := by
  have hI : GGRootNormInner ((ggU .E7 n f).D.rootGroup β) := l10se7_inner_root hf hβ
  have h := ggRootNormInner_map_mulEquiv (MulAut.conj u) hI
  rw [ggRootSub, Subgroup.map_id]
  exact h

private theorem l10se7_inner_range
    {n f : ℕ} (hf : 1 ≤ f) {X : Type} [Group X]
    (φ : (ggU .E7 n f).K →* X) (hker : φ.ker ≤ Subgroup.center (ggU .E7 n f).K)
    {β : Fin (ggU .E7 n f).D.rank → ℤ} (hβ : β ∈ (ggU .E7 n f).D.roots)
    (u : (ggU .E7 n f).K) :
    GGRootNormInner ((ggRootSub (ggU .E7 n f).D φ β u).subgroupOf φ.range) := by
  have hkerbot : φ.ker = ⊥ := le_bot_iff.mp (hker.trans (le_of_eq center_eq_bot_E7))
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hkerbot
  have hI : GGRootNormInner
      (((ggU .E7 n f).D.rootGroup β).map (MulAut.conj u).toMonoidHom) := by
    have h := ggRootNormInner_e7 hf hβ u
    rwa [ggRootSub, Subgroup.map_id] at h
  have hmap := ggRootNormInner_map_mulEquiv (MonoidHom.ofInjective hinj) hI
  have hRbar : (((ggU .E7 n f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map
        (MonoidHom.ofInjective hinj).toMonoidHom =
      ((((ggU .E7 n f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map
        φ).subgroupOf φ.range := by
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro hr
      exact ⟨(MonoidHom.ofInjective hinj).symm x, hr,
        MonoidHom.apply_ofInjective_symm hinj x⟩
    · rintro ⟨r, hr, hx⟩
      have hx' : MonoidHom.ofInjective hinj r = x := by
        apply Subtype.ext
        simpa only [MonoidHom.ofInjective_apply hinj] using hx
      rw [← hx']
      simpa using hr
  rw [hRbar] at hmap
  exact hmap

theorem ggRootInnerAt_ggU_e7
    {n f : ℕ} (hf : 1 ≤ f) {X : Type} [Group X]
    (φ : (ggU .E7 n f).K →* X) (hker : φ.ker ≤ Subgroup.center (ggU .E7 n f).K)
    {β : Fin (ggU .E7 n f).D.rank → ℤ} (hβ : β ∈ (ggU .E7 n f).D.roots)
    (u : (ggU .E7 n f).K) :
    GGRootInnerAt φ.range (ggRootSub (ggU .E7 n f).D φ β u) := by
  have hI := l10se7_inner_range hf φ hker hβ u
  intro Y hY2 hYK hYR hNY
  exact ggRootNormInner_le_sup_centralizer (Subgroup.map_le_range _ _) hYK hYR hY2 hNY hI

theorem itemThree_ggU_e7
    {n f : ℕ} (hf : 1 ≤ f) {X : Type} [Group X]
    (ψ : (ggU .E7 n f).K →* X) (hker : ψ.ker ≤ Subgroup.center (ggU .E7 n f).K)
    {β : Fin (ggU .E7 n f).D.rank → ℤ} (hβ : β ∈ (ggU .E7 n f).D.roots)
    (u : (ggU .E7 n f).K) {R : Subgroup X} (hR : R = ggRootSub (ggU .E7 n f).D ψ β u) :
    ∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (ψ.range : Set X) →
      Y ≤ Subgroup.normalizer (R : Set X) →
      ⁅Y, ψ.range ⊓ Subgroup.normalizer (R : Set X)⁆ ≤
        pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (R : Set X)) →
      Y ≤ ψ.range ⊔ Subgroup.centralizer (ψ.range : Set X) := by
  have hI := l10se7_inner_range hf ψ hker hβ u
  intro Y hY2 hYK hYR hcomm
  refine ggRootNormInner_le_sup_centralizer_of_commutator ?_ hYK hYR hY2 hcomm ?_
  · rw [hR]
    exact Subgroup.map_le_range _ _
  · rw [hR]
    exact hI

theorem ggRootNoCentral_e7
    {n f : ℕ}
    {β : Fin (ggU .E7 n f).D.rank → ℤ} (hβ : β ∈ (ggU .E7 n f).D.roots)
    (u : (ggU .E7 n f).K) :
    GGRootNoCentralAt (⊤ : Subgroup (ggU .E7 n f).K)
      (ggRootSub (ggU .E7 n f).D (MonoidHom.id (ggU .E7 n f).K) β u) := by
  have hNC : GGRootNoCentralAt (⊤ : Subgroup (ggU .E7 n f).K) ((ggU .E7 n f).D.rootGroup β) :=
    l10se7_noCentral_root (K := GaloisField 2 f) hβ
  have hmap : ((ggU .E7 n f).D.rootGroup β).map (MulAut.conj u).toMonoidHom =
      ggRootSub (ggU .E7 n f).D (MonoidHom.id (ggU .E7 n f).K) β u := by
    simp only [ggRootSub, Subgroup.map_id]
  have h := ggRootNoCentralAt_top_map_mulEquiv (MulAut.conj u) hNC
  rwa [hmap] at h

theorem ggRootNoCentralAt_ggU_e7
    {n f : ℕ} {X : Type} [Group X] [Finite X]
    (φ : (ggU .E7 n f).K →* X) (hker : φ.ker ≤ Subgroup.center (ggU .E7 n f).K)
    {β : Fin (ggU .E7 n f).D.rank → ℤ} (hβ : β ∈ (ggU .E7 n f).D.roots)
    (u : (ggU .E7 n f).K) :
    GGRootNoCentralAt φ.range (ggRootSub (ggU .E7 n f).D φ β u) := by
  have hcenter : Subgroup.center (ggU .E7 n f).K = ⊥ := center_eq_bot_E7
  have hker_bot : φ.ker = ⊥ := le_bot_iff.mp (hker.trans (le_of_eq hcenter))
  have hodd : Odd (Nat.card φ.ker) := by
    rw [hker_bot, Subgroup.card_bot]
    exact odd_one
  have hR : IsPGroup 2 (ggRootSub (ggU .E7 n f).D (MonoidHom.id (ggU .E7 n f).K) β u) :=
    rootGroup_isPGroup_E7 u rfl
  have hbase : GGRootNoCentralAt (⊤ : Subgroup (ggU .E7 n f).K)
      (ggRootSub (ggU .E7 n f).D (MonoidHom.id (ggU .E7 n f).K) β u) :=
    ggRootNoCentral_e7 hβ u
  have h := SpecialLinearNC.ggRootNoCentralAt_map_of_odd_central_ker φ hker hodd hR hbase
  have hgoal : (ggRootSub (ggU .E7 n f).D (MonoidHom.id (ggU .E7 n f).K) β u).map φ =
      ggRootSub (ggU .E7 n f).D φ β u :=
    (Short.ggRootSub_eq_map (ggU .E7 n f).D φ β u).symm
  rwa [hgoal] at h

end CFSG.StandardType.LieKnownR2.E7
