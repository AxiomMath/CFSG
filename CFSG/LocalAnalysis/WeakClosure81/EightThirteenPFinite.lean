module

public import CFSG.LocalAnalysis.WeakClosure81.EightTwelveDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
  (IsL2 IsSz IsL3 IsU3 IsSp4 IsU4 IsU5 IsOmega8m Is3D4 IsAlt IsSL3 Bar2 OInf Opp)

@[expose] def OddShape5 {Y : Type} [Group Y] (L : Subgroup Y) : Prop :=
  CFSG.Open.IsQuasisimple ↥L ∧ Odd (Nat.card ↥(Subgroup.center ↥L)) ∧
    (IsL2 ↥L 2 ∨ IsU3 ↥L 2 ∨ IsL3 ↥L 2 ∨ IsSp4 ↥L 2 ∨ IsSL3 ↥L 2)

@[expose] def RankTwoShape {Y : Type} [Group Y] (L : Subgroup Y) : Prop :=
  IsL3 ↥L 2 ∨ IsSp4 ↥L 2 ∨ IsSL3 ↥L 2

@[expose] def K1In {Y : Type} [Group Y] (L A : Subgroup Y) : Prop :=
  ∀ α ∈ A, ∀ β ∈ A, β ≠ 1 →
    IsElemAbelian 2 (Subgroup.closure
      {γ : Y | ∃ x ∈ L ⊓ centralizer ({β} : Set Y), γ = x * α * x⁻¹})

theorem K1In.of_top {Y : Type} [Group Y] {A : Subgroup Y} (L : Subgroup Y) (h : K1In ⊤ A) :
    K1In L A := by
  intro α hα β hβ hβ1
  refine CFSG.Open.IsElemAbelian.mono (h α hα β hβ hβ1) (Subgroup.closure_mono ?_)
  rintro γ ⟨x, hx, rfl⟩
  exact ⟨x, Subgroup.mem_inf.mpr ⟨Subgroup.mem_top x, (Subgroup.mem_inf.mp hx).2⟩, rfl⟩

@[expose] def TISIn {Y : Type} [Group Y] (L A : Subgroup Y) : Prop :=
  ∀ S' : Subgroup Y, IsSylowIn 2 S' L → A ⊓ S' = ⊥ ∨ A ≤ S'

@[expose] def ElemAbOrderEight (E : Type) [Group E] : Prop :=
  Nat.card E = 8 ∧ (∀ x y : E, x * y = y * x) ∧ ∀ x : E, x * x = 1

@[expose] def OddSchurMultiplierFact : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
    Odd (Nat.card ↥(Subgroup.center Q)) →
    (IsL2 (Q ⧸ Subgroup.center Q) 2 ∨ IsU3 (Q ⧸ Subgroup.center Q) 2 ∨
      IsSp4 (Q ⧸ Subgroup.center Q) 2) →
    Nat.card ↥(Subgroup.center Q) = 1

@[expose] def InvolutionCentralizerFact : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y) (b : Y),
    OddShape5 L → b ∈ normalizer (L : Set Y) → b * b = 1 →
    (∀ x ∈ L, x * b = b * x → ∀ l ∈ L, (x * x) * l = l * (x * x)) →
    ∃ s ∈ L, s * s = 1 ∧ ∃ c ∈ centralizer (L : Set Y), b = s * c

@[expose] def FourGroupInnerFact : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L A : Subgroup Y),
    OddShape5 L → A ≤ normalizer (L : Set Y) → IsElemAbelian 2 A → Nat.card A = 4 →
    A ⊓ centralizer (L : Set Y) = ⊥ → K1In L A → A ≤ L ⊔ centralizer (L : Set Y)

@[expose] def BorelOvergroupFact : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L S : Subgroup Y), OddShape5 L → IsSylowIn 2 S L →
    ((IsL2 ↥L 2 ∨ IsU3 ↥L 2) →
      ∀ P : Subgroup Y, L ⊓ normalizer (S : Set Y) ≤ P → P ≤ L →
        P = L ⊓ normalizer (S : Set Y) ∨ P = L) ∧
    (RankTwoShape L →
      ∃ P₁ P₂ : Subgroup Y, IsMaxParabolicMod ⊥ L P₁ ∧ IsMaxParabolicMod ⊥ L P₂ ∧
        L ⊓ normalizer (S : Set Y) ≤ P₁ ∧ L ⊓ normalizer (S : Set Y) ≤ P₂ ∧
        (∀ l ∈ L, conjSubgroup P₁ l ≠ P₂) ∧
        ∀ P : Subgroup Y, L ⊓ normalizer (S : Set Y) ≤ P → P ≤ L →
          P = L ⊓ normalizer (S : Set Y) ∨ P = P₁ ∨ P = P₂ ∨ P = L)

@[expose] def ChoiceOfKFact : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L S A : Subgroup Y), OddShape5 L → IsSylowIn 2 S L →
    A ≤ S → IsElemAbelian 2 A → Nat.card A = 4 → K1In L A → TISIn L A →
    ∃ K : Subgroup Y, K ≤ L ∧ A ≤ K ∧ ¬ A ≤ oTwoMod ⊥ K ∧
      HasQuotShape K (oTwoMod ⊥ K : Set Y) (fun X _ => IsL2 X 2) ∧ IsSylowIn 2 (S ⊓ K) K ∧
      (K ⊓ (L ⊓ normalizer (S : Set Y))).relIndex K = 5 ∧
      (RankTwoShape L → ¬ (∀ a ∈ A, ∀ s ∈ S, a * s = s * a) →
        ∃ P : Subgroup Y, IsMaxParabolicMod ⊥ L P ∧ K = oddResMod ⊥ P)

@[expose] def BorelGL32Fact : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L S : Subgroup Y), OddShape5 L → IsSylowIn 2 S L →
    ∀ (E : Type) [Group E], ElemAbOrderEight E →
      ∀ (W : Subgroup (MulAut E)) (X : Type) [Group X] (ψ : ↥W →* X), Function.Surjective ψ →
        ∀ φ : ↥(L ⊓ normalizer (S : Set Y)) →* X,
          (IsU3 ↥L 2 → S.subgroupOf (L ⊓ normalizer (S : Set Y)) ≤ φ.ker) ∧
          (RankTwoShape L →
            (S ⊓ centralizer (S : Set Y)).subgroupOf (L ⊓ normalizer (S : Set Y)) ≤ φ.ker)

end CFSG.LocalAnalysis.WeakClosure81

end
