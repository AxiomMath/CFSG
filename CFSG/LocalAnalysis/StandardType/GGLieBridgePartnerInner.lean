module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreBridge
public import CFSG.LocalAnalysis.StandardType.GGInterfaceFive
public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs
public import CFSG.LocalAnalysis.StandardType.GGFinModelInput
public import CFSG.LocalAnalysis.StandardType.GGLieBridgeHom
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerE7
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAdj

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel
open CFSG.Open (StatedLieTag)

private theorem l10b4_conj_eq {G : Type} [Group G] {G₀ : Subgroup G} {d g : G} (hg : g ∈ G₀)
    (hdg : d * g ∈ Subgroup.centralizer (G₀ : Set G)) {x : G} (hx : x ∈ G₀) :
    d * x * d⁻¹ = g⁻¹ * x * g := by
  have hy : g⁻¹ * x * g ∈ G₀ := mul_mem (mul_mem (inv_mem hg) hx) hg
  have h1 : (g⁻¹ * x * g) * (d * g) = (d * g) * (g⁻¹ * x * g) :=
    Subgroup.mem_centralizer_iff.mp hdg _ hy
  have h2 : (g⁻¹ * x * g) * d = d * x := by
    apply mul_right_cancel (b := g)
    calc (g⁻¹ * x * g) * d * g = (g⁻¹ * x * g) * (d * g) := by group
      _ = (d * g) * (g⁻¹ * x * g) := h1
      _ = d * x * g := by group
  calc d * x * d⁻¹ = ((g⁻¹ * x * g) * d) * d⁻¹ := by rw [h2]
    _ = g⁻¹ * x * g := by group

private theorem l10b4_partner_abs {G Y : Type} [Group G] [Group Y] {G₀ : Subgroup G}
    (θ : ↥G₀ →* Y) {d g : G} (hg : g ∈ G₀) (hdg : d * g ∈ Subgroup.centralizer (G₀ : Set G)) :
    GGLiePartner G₀ θ d (θ ⟨g, hg⟩)⁻¹ := by
  intro x h
  have e : d * (x : G) * d⁻¹ = g⁻¹ * (x : G) * g := l10b4_conj_eq hg hdg x.2
  have hsub : (⟨d * (x : G) * d⁻¹, h⟩ : ↥G₀) = ⟨g, hg⟩⁻¹ * x * ⟨g, hg⟩ :=
    Subtype.ext (by simpa using e)
  rw [hsub, map_mul, map_mul, map_inv, inv_inv]

private theorem l10b4_innerTag {t : StatedLieTag} (ht : t = .F4 ∨ t = .E7 ∨ t = .E8) :
    GGInnerTag t := by
  rcases ht with h | h | h <;> simp [GGInnerTag, h]

theorem ggLiePartner_inner
    {t : StatedLieTag} {n f : ℕ} (ht : t = .F4 ∨ t = .E7 ∨ t = .E8)
    {G : Type} [Group G] [Finite G] {ψ : (ggU t n f).K →* G} {G₀ : Subgroup G}
    (hpres : GGPresentsG0 G₀ (ggU t n f).D t n f ψ) {θ : ↥G₀ →* ModGL (langTag t) GGL}
    (hrange : θ.range ≤ ggFixGp t f)
    {d : G} (hd : d ∈ Subgroup.normalizer (G₀ : Set G))
    (hψ : GGPsiInnerDiag (ggU t n f).D ψ d) :
    ∃ a ∈ ggFixGp t f, GGLiePartner G₀ θ d a := by
  obtain ⟨g, hg, hdg⟩ :=
    ggPsiDiagInnerAt_of_ggInnerTag t (l10b4_innerTag ht) G n f ψ G₀ hpres d hd hψ
  exact ⟨(θ ⟨g, hg⟩)⁻¹, inv_mem (hrange ⟨⟨g, hg⟩, rfl⟩), l10b4_partner_abs θ hg hdg⟩

end CFSG.StandardType.LieCore
