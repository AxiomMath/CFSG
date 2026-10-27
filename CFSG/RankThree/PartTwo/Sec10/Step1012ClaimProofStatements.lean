module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Sec10.Sec10XProofSym

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def KS1012GL34 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], (∀ s t : S, s * t = t * s) → (∀ s : S, s ^ 2 = 1) →
    ∀ (Y : Subgroup (MulAut S)) (z x w : MulAut S), z ∈ Y → x ∈ Y → w ∈ Y →
      (∀ y ∈ Y, y * z = z * y) → z ^ 3 = 1 → (∀ s : S, z s = s → s = 1) →
      x ^ 3 = 1 → Nat.card {s : S // x s = s} = 4 → w * x * w⁻¹ = x * z →
      (∃ T : Subgroup (MulAut S), T ≤ Y ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
        x ∈ Subgroup.normalizer (T : Set (MulAut S))) →
      Sec4.IsSLThreePiAt (inSubgroup perfectResidual Y) 4 ∨
        Sec4.IsTripleCover (inSubgroup perfectResidual Y) (alternatingGroup (Fin 6))

@[expose] def KS1012AutHyp : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.IsQuasisimple Q →
    (Sec4.IsSLThreePiAt Q 4 ∨ Sec4.IsTripleCover Q (alternatingGroup (Fin 6)) ∨
      Sec4.IsSLThreePiAt Q 64) →
    ∀ F : Subgroup (MulAut Q), CFSG.Assembly.IsElemAbelian 3 F →
      ∃ F' ≤ F, Nat.card F ≤ 3 * Nat.card F' ∧
        ∃ V : Subgroup Q, V ≠ ⊥ ∧ IsPGroup 2 V ∧ ∀ f ∈ F', ∀ v ∈ V, f v ∈ V


@[expose] def Step1012ClaimK : Prop :=
  Sec4.Item4_5 → Sec9.Item97 →
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), Sec10Std G A c L a R → ∀ d : G, A ⊓ L = Subgroup.zpowers d →
      sec10U L a ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) →
      sec10U L a ∈
        maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piOf 2) →
      ∀ S ∈ maxInvariantPiSubgroups
          (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))) A (piOf 2),
        sec10U L a ≤ S → S ⊓ Subgroup.centralizer ({c} : Set G) = sec10U L a →
        S ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ → IsMulCommutative S →
      ∀ w ∈ Subgroup.normalizer (A : Set G), w ∈ Subgroup.normalizer (S : Set G) →
        w * a * w⁻¹ = a → w * d * w⁻¹ = d → w * c * w⁻¹ = c * d →
      ∀ V : Subgroup G, IsPGroup 2 V → A ≤ Subgroup.normalizer (V : Set G) →
        V ≤ Subgroup.normalizer (S : Set G) →
        V ≤ Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G) →
        V ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (sec10U L a : Set G)) →
        ¬ V ≤ Subgroup.centralizer (S : Set G) →
        ¬ V ≤ inSubgroup (aschbacherSolvableCore 3)
          (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)) →
      (Sec4.IsSLThreePiAt (inSubgroup perfectResidual (Sec4.autIn
          (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)) S)) 4 ∨
        Sec4.IsTripleCover (inSubgroup perfectResidual (Sec4.autIn
          (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)) S))
          (alternatingGroup (Fin 6))) →
      ∃ K ∈ thetaComponentsIn
          (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)),
        (Sec4.IsSLThreePiAt (K ⧸ aschbacherSolvableCore 3 K) 4 ∨
          Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6))) ∧
        inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G)) ≠ ⊥ ∧
        inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G)) ≤
          Subgroup.centralizer (Subgroup.centralizer ({d} : Set G) : Set G)

@[expose] def Step1012ClaimON : Prop :=
  Sec4.Item4_5 → Sec9.Item97 →
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), Sec10Std G A c L a R → ∀ d : G, A ⊓ L = Subgroup.zpowers d →
    ∀ K ∈ thetaComponentsIn
        (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)),
      Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6)) →
      inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G)) ≠ ⊥ →
      inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G)) ≤
        Subgroup.centralizer (Subgroup.centralizer ({d} : Set G) : Set G) →
    ∀ X ∈ thetaComponentsAt 3 d, K ≤ X →
      ¬ Sec4.IsTripleCover (X ⧸ aschbacherSolvableCore 3 X) Blueprint.NativeSporadic.ON

end CFSG.RankThree.PartTwo.Sec10
