module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

structure burnsideF437_Inv {E : Type} [Group E] (Gp M₁ M₂ : Subgroup E) (fb : E) : Prop where
  mem : fb ∈ M₁ ⊓ M₂
  not_mem : fb ∉ Gp
  sq : fb * fb = 1
  sylow : ChF.IsSylowOf 2
    (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({fb} : Set E)) (cenIn Gp fb)

structure burnsideF437_FixedFacts (κ : GLKind) (degree : ℕ) {E : Type} [Group E]
    (Gp M₁ M₂ : Subgroup E) (chart : NativeChart κ 2 degree Gp) (fb : E) : Prop where
  field_lie : chart.IsFieldInv fb → IsGenLie (cenIn Gp fb) κ 2 (degree / 2)
  parabolics : IsLieParabolics 2 (cenIn Gp fb) (cenIn (Gp ⊓ (M₁ ⊓ M₂)) fb)
    (cenIn (Gp ⊓ M₁) fb) (cenIn (Gp ⊓ M₂) fb)
  unique_sylow : ∀ S : Subgroup E, ChF.IsSylowOf 2 S Gp →
    pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({fb} : Set E) ≤ S →
      S = pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))
  rigid : Subgroup.centralizer ((cenIn Gp fb : Subgroup E) : Set E) ⊓
    Subgroup.centralizer ({fb} : Set E) ≤ Subgroup.zpowers fb

@[expose] def burnsideF437_FixedInput : Prop :=
  ∀ (κ : GLKind) (degree : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E)
    (hyp : HypF_4_4 κ 2 degree Gp M₁ M₂) (fb : E), burnsideF437_Inv Gp M₁ M₂ fb →
    (hyp.toHypF_4_4g.chart.IsFieldInv fb ∨ hyp.toHypF_4_4g.chart.IsGraphInv fb) →
      burnsideF437_FixedFacts κ degree Gp M₁ M₂ hyp.toHypF_4_4g.chart fb

@[expose] def burnsideF437_ClassInput : Prop :=
  ∀ (κ : GLKind) (degree : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E)
    (hyp : HypF_4_4 κ 2 degree Gp M₁ M₂), κ.IsLie →
    ∀ T : Subgroup E, ChF.IsSylowOf 2 T (M₁ ⊓ M₂) →
    ∀ t ∈ T, t ∉ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) → t * t = 1 →
      hyp.toHypF_4_4g.chart.IsFieldInv t ∨
        (hyp.toHypF_4_4g.chart.IsGraphInv t ∧ IsGenLie ↥(cenIn Gp t) GLKind.Sp4 2 degree ∧
          hyp.toHypF_4_4g.chart.GraphFixedMarkingGoal t) ∨
        hyp.toHypF_4_4g.chart.IsTypeIIIInv t

end CFSG.ASVolI
