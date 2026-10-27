module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1Labels
public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1KGField
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGFixSub
public import CFSG.LocalAnalysis.StandardType.GGNbrLangKGInputs
public import CFSG.LocalAnalysis.StandardType.GGTableBLinear
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorARankKG
public import CFSG.LocalAnalysis.StandardType.GGL45NtClUni

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def KGCentCompNotE8F4Cont (p : ℕ) : LargeEvenRawCont := fun R _ I _ =>
  ∀ h ∈ I, h ≠ 1 → h ^ p = 1 →
    ∀ J₀ : Subgroup R, IsComponentOf J₀ (MonoidHom.eqLocus (h : R →* R) (MonoidHom.id R)) →
      ∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ →
        GGHasLabel labJ (↥J₀ ⧸ Subgroup.center ↥J₀) →
          labJ.tag ≠ .E8 ∧ labJ.tag ≠ .F4 ∧ labJ.tag ≠ .twF4 ∧ labJ.tag ≠ .twF4der

@[expose] def KGLangAxisS1LinCont (p : ℕ) : LargeEvenRawCont := fun R _ I F =>
  ∀ (K : Type) [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R), commutator K = ⊤ →
    ∀ A : Subgroup (MulAut K), IsElemAbelian p A →
      (∀ α ∈ A, ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, kgInducedAut θ α = u * f) →
      ∀ α₀ ∈ A, kgInducedAut θ α₀ ∉ I →
      p ^ 2 ≤ Nat.card {α : MulAut K // α ∈ A ∧ kgInducedAut θ α ∈ I} →
      ∀ ξ ∈ A, kgInducedAut θ ξ ∉ I →
      ∀ J₀ : Subgroup K, IsComponentOf J₀ (ggFixSub ξ) →
      ∀ (d : ℕ) (E : Type) [Field E] [Finite E]
        (θ₀ : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) E)),
      (∃ At : Subgroup (GL (Fin d) E), IsMulCommutative At ∧
        ∀ α ∈ A, ∃ g ∈ At, ∀ j : ↥J₀, ∃ j' : ↥J₀, (j' : K) = α j ∧
          θ₀ (QuotientGroup.mk j') = TableB.linConjAut (Fin d) E g (θ₀ (QuotientGroup.mk j))) →
      ∃ k e : K, e ≠ 1 ∧ e ^ p = 1 ∧ (∀ α ∈ A, α e = e) ∧
        (∀ α ∈ A, kgInducedAut θ α ∈ I → α k = k) ∧ k * (α₀ k)⁻¹ = e

@[expose] def KGLangAxisS1LinInput : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
    GGNbrLangS1LinLabel p lab → LargeEvenLabelAll lab (KGLangAxisS1LinCont p)

@[expose] def KGLangAxisS1UniCont (p : ℕ) : LargeEvenRawCont := fun R _ I F =>
  ∀ (K : Type) [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R), commutator K = ⊤ →
    ∀ A : Subgroup (MulAut K), IsElemAbelian p A →
      (∀ α ∈ A, ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, kgInducedAut θ α = u * f) →
      ∀ α₀ ∈ A, kgInducedAut θ α₀ ∉ I →
      p ^ 2 ≤ Nat.card {α : MulAut K // α ∈ A ∧ kgInducedAut θ α ∈ I} →
      ∀ ξ ∈ A, kgInducedAut θ ξ ∉ I →
      ∀ J₀ : Subgroup K, IsComponentOf J₀ (ggFixSub ξ) →
      ∀ (d m : ℕ) (E : Type) [Field E]
        (hE : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 m E)
        (θ₀ : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m))),
      (∃ At : Subgroup ↥(TableB.unitGroup (ι := Fin d) hE.bar), IsMulCommutative At ∧
        ∀ α ∈ A, ∃ g ∈ At, ∀ j : ↥J₀, ∃ j' : ↥J₀, (j' : K) = α j ∧
          θ₀ (QuotientGroup.mk j') =
            CFSG.HardMathSupport.C14Cl.uniConj hE d g (θ₀ (QuotientGroup.mk j))) →
      ∃ k e : K, e ≠ 1 ∧ e ^ p = 1 ∧ (∀ α ∈ A, α e = e) ∧
        (∀ α ∈ A, kgInducedAut θ α ∈ I → α k = k) ∧ k * (α₀ k)⁻¹ = e

@[expose] def KGLangAxisS1UniInput : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
    GGNbrLangS1UniLabel p lab → LargeEvenLabelAll lab (KGLangAxisS1UniCont p)

end CFSG.StandardType
