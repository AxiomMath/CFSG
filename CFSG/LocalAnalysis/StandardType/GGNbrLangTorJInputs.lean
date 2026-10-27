module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLangRegKG
public import CFSG.LocalAnalysis.StandardType.GGNbrLangKGInputs
public import CFSG.LocalAnalysis.StandardType.GGTableBLinear

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGBstarInnerDiagJInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagOn Bs L → GGInnerDiagOn Bs J

@[expose] def GGBstarAbelianPreimageJLinInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
      ∀ (hN : Bs ≤ Subgroup.normalizer (J : Set G)) (d : ℕ) (K : Type) [Field K] [Finite K]
        (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)),
        IsMulCommutative
          ((((ggBsAut hN).range).map (kgInducedAut θ)).comap (TableB.linConjAut (Fin d) K))

@[expose] def KGLangAxisT3Cont : LargeEvenRawCont := fun R _ I F =>
  ∀ (K : Type) [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R), commutator K = ⊤ →
    ∀ A : Subgroup (MulAut K), IsElemAbelian 3 A →
      (∀ α ∈ A, ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, kgInducedAut θ α = u * f) →
      ∀ α₀ ∈ A, kgInducedAut θ α₀ ∉ I →
      ∀ h : K, h ≠ 1 → MulAut.conj h ∈ A →
      ∀ J₀ : Subgroup K, IsComponentOf J₀ (Subgroup.centralizer ({h} : Set K)) →
      ∀ (E : Type) [Field E] [Finite E]
        (θ₀ : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃* LargeEvenProj (LargeEvenSLGroup (Fin 3) E)),
      (∃ At : Subgroup (GL (Fin 3) E), IsMulCommutative At ∧
        ∀ α ∈ A, ∃ g ∈ At, ∀ j : ↥J₀, ∃ j' : ↥J₀, (j' : K) = α j ∧
          θ₀ (QuotientGroup.mk j') = TableB.linConjAut (Fin 3) E g (θ₀ (QuotientGroup.mk j))) →
      ∃ k : K, (∀ α ∈ A, kgInducedAut θ α ∈ I → α k = k) ∧ k * (α₀ k)⁻¹ = h

@[expose] def KGLangAxisT3Input : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .triD4 → 3 ∣ 2 ^ lab.n - 1 →
    LargeEvenLabelAll lab KGLangAxisT3Cont

end CFSG.StandardType
