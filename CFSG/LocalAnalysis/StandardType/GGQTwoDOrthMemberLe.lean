module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthMember
public import CFSG.LocalAnalysis.StandardType.GGQTwoDInputs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.OrthTorus CFSG.ClassicalInvolution.Phan CFSG.Open

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private lemma qtwoDOrthLe_oTwoPrime_mono {H K : Subgroup G} (h : H ≤ K) :
    ggOTwoPrime H ≤ ggOTwoPrime K :=
  Subgroup.closure_mono fun _ hy => ⟨h hy.1, hy.2⟩

theorem qtwoMemberFacts_of_le_orth {p : ℕ} {Bs X Y : Subgroup G} {ι : Type}
    {M : CoxeterMatrix ι} {A : Subgroup (MulAut ↥Bs)} {e : M.Group ≃* ↥A} (hXY : X ≤ Y)
    (hY : QTwoOrthMemberFacts p Bs Y) (hrefl : ∀ r ∈ ggCoxRefl M e, GGIsReflection p r)
    (h1 : ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → ggRankOne Bs r = ggRankOneIn X Bs r)
    (h2 : ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → ∀ r' ∈ ggAutomizer X Bs,
      r' ∈ ggCoxRefl M e → r * r' ≠ r' * r → ggRankTwo Bs r r' = ggRankTwoIn X Bs r r') :
    QTwoMemberFacts Bs X M A e := by
  have hA : ∀ r ∈ ggAutomizer X Bs, r ∈ ggAutomizer Y Bs := fun r hr =>
    ggAutomizer_mono Bs hXY hr
  have hone : ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e →
      ggRankOneIn Y Bs r = ggRankOneIn X Bs r := by
    intro r hr hrC
    refine le_antisymm ?_ (qtwoDOrthLe_oTwoPrime_mono (inf_le_inf_right _ hXY))
    rw [← h1 r hr hrC]
    exact qtwoDOrthLe_oTwoPrime_mono inf_le_right
  have htwo : ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → ∀ r' ∈ ggAutomizer X Bs,
      r' ∈ ggCoxRefl M e → r * r' ≠ r' * r →
        ggRankTwoIn Y Bs r r' = ggRankTwoIn X Bs r r' := by
    intro r hr hrC r' hr' hr'C hnc
    refine le_antisymm ?_ (qtwoDOrthLe_oTwoPrime_mono (inf_le_inf_right _ hXY))
    rw [← h2 r hr hrC r' hr' hr'C hnc]
    exact qtwoDOrthLe_oTwoPrime_mono inf_le_right
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · intro r hr hrC r' hr' hr'C hnc _
    have h := hY.1 r (hA r hr) (hrefl r hrC) r' (hA r' hr') (hrefl r' hr'C) hnc
    rwa [htwo r hr hrC r' hr' hr'C hnc, hone r hr hrC, hone r' hr' hr'C] at h
  · intro r₁ h₁ hr₁ r₂ h₂ hr₂ r₃ h₃ hr₃ h12 h23 h13 hne _
    obtain ⟨θ, hθ⟩ := hY.2.1 r₁ (hA r₁ h₁) (hrefl r₁ hr₁) r₂ (hA r₂ h₂) (hrefl r₂ hr₂) r₃
      (hA r₃ h₃) (hrefl r₃ hr₃) h12 h23 h13 hne
    exact ⟨θ, by rw [hθ, htwo r₁ h₁ hr₁ r₂ h₂ hr₂ h12, htwo r₂ h₂ hr₂ r₃ h₃ hr₃ h23]⟩
  · intro r₁ h₁ hr₁ r₂ h₂ hr₂ r₃ h₃ hr₃ r₄ h₄ hr₄ h12 h34 h13 h14 h23 h24 y hy z hz
    exact hY.2.2 r₁ (hA r₁ h₁) (hrefl r₁ hr₁) r₂ (hA r₂ h₂) (hrefl r₂ hr₂) r₃ (hA r₃ h₃)
      (hrefl r₃ hr₃) r₄ (hA r₄ h₄) (hrefl r₄ hr₄) h12 h34 h13 h14 h23 h24 y
      (qtwoDOrthLe_oTwoPrime_mono (inf_le_inf_right _ hXY) hy) z
      (qtwoDOrthLe_oTwoPrime_mono (inf_le_inf_right _ hXY) hz)

end CFSG.StandardType.QTwo

end
