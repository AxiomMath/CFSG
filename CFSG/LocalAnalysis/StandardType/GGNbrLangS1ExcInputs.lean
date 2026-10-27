module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1Labels
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorJInputs
public import CFSG.LocalAnalysis.StandardType.GGFixSub
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxToral
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangPow
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Conj
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def GGGeomToral
    (τ : Tag) (K₀ : Type) [Field K₀] (W : Subgroup (ModGL τ K₀)) :
    Prop :=
  ExcFramesHalf.IsToralSubgroup τ (AlgebraicClosure K₀)
    (W.map (baseChangeGL (τ := τ) (algebraMap K₀ (AlgebraicClosure K₀))))

@[expose] def GGExcToralActUntw
    (τ : Tag) {K : Type} [Group K] (J₀ : Subgroup K)
    (A : Set (MulAut K)) : Prop :=
  ∃ (K₀ : Type) (_ : Field K₀) (_ : Finite K₀)
    (θ₀ : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃* ↥(adjointGroup τ K₀))
    (W : Subgroup ↥(RecipeExcLang.inndiagGroup τ K₀)),
    GGGeomToral τ K₀ (W.map (RecipeExcLang.inndiagGroup τ K₀).subtype) ∧
    ∀ α ∈ A, ∃ w ∈ W, ∀ j : ↥J₀, ∃ j' : ↥J₀, (j' : K) = α j ∧
      θ₀ (QuotientGroup.mk j') = RecipeExcLang.inndiagConj τ K₀ w (θ₀ (QuotientGroup.mk j))

@[expose] def GGExcToralActTw
    {K : Type} [Group K] (J₀ : Subgroup K) (A : Set (MulAut K)) :
    Prop :=
  ∃ (K₀ : Type) (_ : Field K₀) (_ : Finite K₀) (σ : K₀ ≃+* K₀), orderOf σ = 2 ∧
    ∃ (θ₀ : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃* ↥(graphFixedRootGroup TwistTag.E6 K₀ σ.toRingHom))
      (W : Subgroup ↥(RecipeExcLang.twInndiagGroup K₀ σ)),
    GGGeomToral TwistTag.E6.tag K₀ (W.map (RecipeExcLang.twInndiagGroup K₀ σ).subtype) ∧
    ∀ α ∈ A, ∃ w ∈ W, ∀ j : ↥J₀, ∃ j' : ↥J₀, (j' : K) = α j ∧
      θ₀ (QuotientGroup.mk j') = RecipeExcLang.twConj K₀ σ w (θ₀ (QuotientGroup.mk j))

@[expose] def GGExcToralAct
    {K : Type} [Group K] (J₀ : Subgroup K) (A : Set (MulAut K)) :
    Prop :=
  GGExcToralActUntw .E6 J₀ A ∨ GGExcToralActUntw .E7 J₀ A ∨ GGExcToralActTw J₀ A

@[expose] def GGBstarToralJExcInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 3 B Bs x L D J → GGInnerDiagOn Bs L → GGInnerDiagOn Bs J →
      ∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ →
        (labJ.tag = .E6 ∨ labJ.tag = .twE6 ∨ labJ.tag = .E7) →
        GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) →
          GGExcToralAct J ((fun b : G => MulAut.conj b) '' (Bs : Set G))

@[expose] def GGBstarToralJExcInputOn
    (S : LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 3 B Bs x L D J →
      LargeEvenMarking L (fun lab _ _ I _ θ => S lab ∧
        Bs ≤ Subgroup.normalizer (L : Set G) ∧
          ∀ b ∈ Bs, ∃ φ ∈ I,
            LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
      GGInnerDiagOn Bs J → ∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ →
        (labJ.tag = .E6 ∨ labJ.tag = .twE6 ∨ labJ.tag = .E7) →
        GGHasLabel labJ (J ⧸ Subgroup.center J) →
          GGExcToralAct J ((fun b : G => MulAut.conj b) '' (Bs : Set G))

section Selector

theorem GGBstarToralJExcInputOn.mono {S T : LargeEvenLabel → Prop}
    (hTS : ∀ lab, T lab → S lab) (h : GGBstarToralJExcInputOn S) :
    GGBstarToralJExcInputOn T := by
  intro G _ _ B Bs x L D J hcfg hmark hJ
  exact h G B Bs x L D J hcfg
    (largeEvenMarking_mono (fun lab R _ I F θ hh => ⟨hTS lab hh.1, hh.2⟩) hmark) hJ

theorem GGBstarToralJExcInputOn.of_compl {S T : LargeEvenLabel → Prop}
    (hSnotT : GGBstarToralJExcInputOn (fun lab => S lab ∧ ¬ T lab))
    (hT : GGBstarToralJExcInputOn T) :
    GGBstarToralJExcInputOn S := by
  classical
  intro G _ _ B Bs x L D J hcfg hmark hJ
  obtain ⟨hperf, lab, hlab, hraw⟩ := hmark
  by_cases hTlab : T lab
  · refine hT G B Bs x L D J hcfg ⟨hperf, lab, hlab, ?_⟩ hJ
    refine largeEvenRawDatum_mono (fun R _ I F hh => ?_) hraw
    obtain ⟨hs, hna, θ, _, hN, hact⟩ := hh
    exact ⟨hs, hna, θ, hTlab, hN, hact⟩
  · refine hSnotT G B Bs x L D J hcfg ⟨hperf, lab, hlab, ?_⟩ hJ
    refine largeEvenRawDatum_mono (fun R _ I F hh => ?_) hraw
    obtain ⟨hs, hna, θ, hS, hN, hact⟩ := hh
    exact ⟨hs, hna, θ, ⟨hS, hTlab⟩, hN, hact⟩

end Selector

@[expose] def KGLangAxisS1ExcCont
    (p : ℕ) : LargeEvenRawCont := fun R _ I F =>
  ∀ (K : Type) [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R), commutator K = ⊤ →
    ∀ A : Subgroup (MulAut K), IsElemAbelian p A →
      (∀ α ∈ A, ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, kgInducedAut θ α = u * f) →
      ∀ α₀ ∈ A, kgInducedAut θ α₀ ∉ I →
      p ^ 2 ≤ Nat.card {α : MulAut K // α ∈ A ∧ kgInducedAut θ α ∈ I} →
      ∀ ξ ∈ A, kgInducedAut θ ξ ∉ I →
      ∀ J₀ : Subgroup K, IsComponentOf J₀ (ggFixSub ξ) → GGExcToralAct J₀ (A : Set (MulAut K)) →
      ∃ k e : K, e ≠ 1 ∧ e ^ p = 1 ∧ (∀ α ∈ A, α e = e) ∧
        (∀ α ∈ A, kgInducedAut θ α ∈ I → α k = k) ∧ k * (α₀ k)⁻¹ = e

@[expose] def KGLangAxisS1ExcInput :
    Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
    GGNbrLangS1ExcELabel p lab → LargeEvenLabelAll lab (KGLangAxisS1ExcCont p)

end CFSG.StandardType
