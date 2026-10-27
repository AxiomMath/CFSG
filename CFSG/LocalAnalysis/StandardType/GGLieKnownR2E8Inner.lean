module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ExcInner
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ItemThree
public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms
public import CFSG.LieType.Chevalley.AdjointCenter

public section

namespace CFSG.StandardType.LieKnownR2.E8

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint.Chevalley

theorem ggRootNormInner_e8
    {n f : ℕ} (hf : 1 ≤ f)
    {β : Fin (ggU .E8 n f).D.rank → ℤ} (hβ : β ∈ (ggU .E8 n f).D.roots)
    (u : (ggU .E8 n f).K) :
    GGRootNormInner (ggRootSub (ggU .E8 n f).D (MonoidHom.id (ggU .E8 n f).K) β u) := by
  have hI : GGRootNormInner ((ggU .E8 n f).D.rootGroup β) :=
    ExcInner.ggRootNormInner_adj_E78 .E8 (Or.inr rfl) hf hβ
  have h := ggRootNormInner_map_mulEquiv (MulAut.conj u) hI
  rw [ggRootSub, Subgroup.map_id]
  exact h

private theorem l10se8_inner_range
    {n f : ℕ} (hf : 1 ≤ f) {X : Type} [Group X]
    (φ : (ggU .E8 n f).K →* X) (hker : φ.ker ≤ Subgroup.center (ggU .E8 n f).K)
    {β : Fin (ggU .E8 n f).D.rank → ℤ} (hβ : β ∈ (ggU .E8 n f).D.roots)
    (u : (ggU .E8 n f).K) :
    GGRootNormInner ((ggRootSub (ggU .E8 n f).D φ β u).subgroupOf φ.range) := by
  haveI : CharP (GaloisField 2 f) 2 := inferInstance
  have hZ : Subgroup.center (ggU .E8 n f).K = ⊥ := by
    change Subgroup.center (adjointGroup .E8 (GaloisField 2 f)) = ⊥
    exact center_adjointGroup_eq_bot
  have hkerbot : φ.ker = ⊥ := le_bot_iff.mp (hker.trans (le_of_eq hZ))
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hkerbot
  have hI : GGRootNormInner
      (((ggU .E8 n f).D.rootGroup β).map (MulAut.conj u).toMonoidHom) := by
    have h := ggRootNormInner_e8 hf hβ u
    rwa [ggRootSub, Subgroup.map_id] at h
  have hmap := ggRootNormInner_map_mulEquiv (MonoidHom.ofInjective hinj) hI
  have hRbar : (((ggU .E8 n f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map
        (MonoidHom.ofInjective hinj).toMonoidHom =
      ((((ggU .E8 n f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map
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

theorem ggRootInnerAt_ggU_e8
    {n f : ℕ} (hf : 1 ≤ f) {X : Type} [Group X]
    (φ : (ggU .E8 n f).K →* X) (hker : φ.ker ≤ Subgroup.center (ggU .E8 n f).K)
    {β : Fin (ggU .E8 n f).D.rank → ℤ} (hβ : β ∈ (ggU .E8 n f).D.roots)
    (u : (ggU .E8 n f).K) :
    GGRootInnerAt φ.range (ggRootSub (ggU .E8 n f).D φ β u) := by
  have hI := l10se8_inner_range hf φ hker hβ u
  intro Y hY2 hYK hYR hNY
  exact ggRootNormInner_le_sup_centralizer (Subgroup.map_le_range _ _) hYK hYR hY2 hNY hI

theorem itemThree_ggU_e8
    {n f : ℕ} (hf : 1 ≤ f) {X : Type} [Group X]
    (ψ : (ggU .E8 n f).K →* X) (hker : ψ.ker ≤ Subgroup.center (ggU .E8 n f).K)
    {β : Fin (ggU .E8 n f).D.rank → ℤ} (hβ : β ∈ (ggU .E8 n f).D.roots)
    (u : (ggU .E8 n f).K) {R : Subgroup X} (hR : R = ggRootSub (ggU .E8 n f).D ψ β u) :
    ∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (ψ.range : Set X) →
      Y ≤ Subgroup.normalizer (R : Set X) →
      ⁅Y, ψ.range ⊓ Subgroup.normalizer (R : Set X)⁆ ≤
        pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (R : Set X)) →
      Y ≤ ψ.range ⊔ Subgroup.centralizer (ψ.range : Set X) := by
  have hI := l10se8_inner_range hf ψ hker hβ u
  intro Y hY2 hYK hYR hcomm
  refine ggRootNormInner_le_sup_centralizer_of_commutator ?_ hYK hYR hY2 hcomm ?_
  · rw [hR]
    exact Subgroup.map_le_range _ _
  · rw [hR]
    exact hI

end CFSG.StandardType.LieKnownR2.E8
