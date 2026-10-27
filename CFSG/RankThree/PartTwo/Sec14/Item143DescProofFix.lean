module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog
public import CFSG.RankThree.PartTwo.KFacts.AutKinds
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts

@[expose] def Item4_25Fix : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → ∀ A : Subgroup G, Late.IsE27 A →
    CFSG.Open.pRank 3 (⊤ : Subgroup G) = 3 → aschbacherSolvableCore 3 G = ⊥ →
    ∀ L : Subgroup G, IsComponent L → ∀ c : G,
    ∀ K : Subgroup (L ⊓ Subgroup.centralizer {c} : Subgroup G), IsComponent K →
    ∀ K' : Subgroup G, K' = K.map (L ⊓ Subgroup.centralizer {c}).subtype →
      (IsSLThreePi (K ⧸ aschbacherSolvableCore 3 K) ∨
        IsExtOf (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6))
          (Multiplicative (ZMod 3)) ∨
        IsExtOf (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 7))
          (Multiplicative (ZMod 3)) ∨
        IsExtOf (K ⧸ aschbacherSolvableCore 3 K) Blueprint.NativeSporadic.M22
          (Multiplicative (ZMod 3))) →
      A ⊓ (K' ⊓ Subgroup.centralizer (K' : Set G)) = Subgroup.zpowers c →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
      K' = L ∨
      (IsExtOf K (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3)) ∧
        Nonempty (L ≃* Blueprint.NativeSporadic.J2)) ∨
      (∃ p f : ℕ, IsSLThreePiAt K (p ^ f) ∧
        (Blueprint.ChevalleyExceptionalModel L .G2 p f ∨
          Blueprint.ChevalleyExceptionalModel L .trialityD4 p f)) ∨
      (((IsExtOf K (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3)) ∧
            Nonempty (L ≃* Blueprint.NativeSporadic.M24)) ∨
          (IsExtOf K (alternatingGroup (Fin 7)) (Multiplicative (ZMod 3)) ∧
            Nonempty (L ≃* Blueprint.NativeSporadic.He))) ∧
        ∃ E : Subgroup G, E ≤ K' ⊔ (A ⊓ Subgroup.centralizer (K' : Set G)) ∧ Late.IsE27 E ∧
          ¬ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))

end CFSG.RankThree.PartTwo.Sec4
