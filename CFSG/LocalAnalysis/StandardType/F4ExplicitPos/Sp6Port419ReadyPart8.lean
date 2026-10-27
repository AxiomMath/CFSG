module

public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Steinberg.Adjoint.Presentation
public import CFSG.LieType.TitsSimplicity.Core
public import CFSG.LocalAnalysis.StandardType.GGLieBridgeHom
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.WeylCharStab
public import CFSG.HardMathSupport.Timmesfeld.Torality.DescentCongruence
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxDefs
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxToral
public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs
public import CFSG.LocalAnalysis.StandardType.GGSixTCKSpace
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart4

@[expose] public section

public section
open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LocalAnalysis.ComponentInitial

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
open scoped CFSG.ConvolutionPoints

public noncomputable section
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.AlgebraicGroups WithConv
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped CFSG.ConvolutionPoints

public section

public section

public section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition

public section

public section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

public section
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.TableCRes
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

public section
open CFSG.Open
open scoped MatrixGroups

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition
open CFSG.LieType.Chevalley

public section

public section

public section
open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition

public noncomputable section

open CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Universal
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.TitsSimplicity CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

public section

namespace CFSG.StandardType.F4ExplicitPos.Partner

open CFSG.StandardType.LieCore CFSG.Assembly CFSG.Open

private theorem partner_unique {G Y : Type} [Group G] [Group Y] {G₀ : Subgroup G}
    {θ : ↥G₀ →* Y} {Φ : Subgroup Y}
    (hcent : ∀ z ∈ Φ, (∀ x : ↥G₀, z * θ x = θ x * z) → z = 1) {d : G}
    (hdN : d ∈ Subgroup.normalizer (G₀ : Set G)) {a a' : Y} (ha : a ∈ Φ) (ha' : a' ∈ Φ)
    (h : GGLiePartner G₀ θ d a) (h' : GGLiePartner G₀ θ d a') : a = a' := by
  have key : ∀ x : ↥G₀, (a'⁻¹ * a) * θ x = θ x * (a'⁻¹ * a) := by
    intro x
    have hx : d * (x : G) * d⁻¹ ∈ G₀ := (Subgroup.mem_normalizer_iff.mp hdN (x : G)).mp x.2
    have heq : a * θ x * a⁻¹ = a' * θ x * a'⁻¹ := (h x hx).symm.trans (h' x hx)
    have hc := congrArg (fun t => a'⁻¹ * t * a) heq
    simpa [mul_assoc] using hc
  have hmem : a'⁻¹ * a ∈ Φ := mul_mem (inv_mem ha') ha
  exact (inv_mul_eq_one.mp (hcent _ hmem key)).symm

private theorem partner_mul {G Y : Type} [Group G] [Group Y] {G₀ : Subgroup G}
    {θ : ↥G₀ →* Y} {d d' : G} (hdN : d ∈ Subgroup.normalizer (G₀ : Set G))
    (hdN' : d' ∈ Subgroup.normalizer (G₀ : Set G)) {a a' : Y} (h : GGLiePartner G₀ θ d a)
    (h' : GGLiePartner G₀ θ d' a') : GGLiePartner G₀ θ (d * d') (a * a') := by
  intro x hx
  have hx' : d' * (x : G) * d'⁻¹ ∈ G₀ :=
    (Subgroup.mem_normalizer_iff.mp hdN' (x : G)).mp x.2
  have hmem : d * (d' * (x : G) * d'⁻¹) * d⁻¹ ∈ G₀ :=
    (Subgroup.mem_normalizer_iff.mp hdN (d' * (x : G) * d'⁻¹)).mp hx'
  have h1 := h ⟨d' * (x : G) * d'⁻¹, hx'⟩ hmem
  have h2 := h' x hx'
  have hsub : (⟨d * (d' * (x : G) * d'⁻¹) * d⁻¹, hmem⟩ : ↥G₀)
      = ⟨d * d' * (x : G) * (d * d')⁻¹, hx⟩ := by
    apply Subtype.ext
    group
  rw [hsub] at h1
  calc θ ⟨d * d' * (x : G) * (d * d')⁻¹, hx⟩
      = a * θ ⟨d' * (x : G) * d'⁻¹, hx'⟩ * a⁻¹ := h1
    _ = a * (a' * θ x * a'⁻¹) * a⁻¹ := by rw [h2]
    _ = (a * a') * θ x * (a * a')⁻¹ := by group

theorem exists_partner_hom {G Y : Type} [Group G] [Group Y] {G₀ D : Subgroup G}
    {Φ : Subgroup Y} {θ : ↥G₀ →* Y}
    (hcent : ∀ z ∈ Φ, (∀ x : ↥G₀, z * θ x = θ x * z) → z = 1)
    (hDN : D ≤ Subgroup.normalizer (G₀ : Set G))
    (hpart : ∀ d ∈ D, ∃ a ∈ Φ, GGLiePartner G₀ θ d a) :
    ∃ lam : ↥D →* Y, ∀ d : ↥D, lam d ∈ Φ ∧ GGLiePartner G₀ θ (d : G) (lam d) := by
  classical
  choose f hfΦ hfp using fun d : ↥D => hpart d d.2
  have hmul : ∀ d d' : ↥D, f (d * d') = f d * f d' := by
    intro d d'
    refine partner_unique hcent (hDN (d * d').2) (hfΦ (d * d'))
      (mul_mem (hfΦ d) (hfΦ d')) ?_ ?_
    · exact hfp (d * d')
    · rw [Subgroup.coe_mul]
      exact partner_mul (hDN d.2) (hDN d'.2) (hfp d) (hfp d')
  exact ⟨MonoidHom.mk' f hmul, fun d => ⟨hfΦ d, hfp d⟩⟩

end CFSG.StandardType.F4ExplicitPos.Partner

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end
