module

public import CFSG.RankThree.PartTwo.Sec13.Statements
public import CFSG.RankThree.PartTwo.Sec4.Item426A6
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
import CFSG.RankThree.PartTwo.Sec13.Item134Dichotomy

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item134ON : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L →
    Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ d ∈ A, d ≠ 1 →
    (∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S L ∧
      (Subgroup.center S).map S.subtype = Subgroup.zpowers d) →
    ∀ K ∈ thetaComponentsAt 3 d,
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K →
      Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) CFSG.Blueprint.NativeSporadic.ON →
        Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) ∧
        omegaA A = orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers c) ∧
        (omegaA A).ncard = 12

@[expose] def Item134Arg128 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L →
    Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ d ∈ A, d ≠ 1 →
    (∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S L ∧
      (Subgroup.center S).map S.subtype = Subgroup.zpowers d) →
    ∀ K ∈ thetaComponentsAt 3 d,
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K →
      K = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔
          inSubgroup (aschbacherSolvableCore 3) K →
      Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6)) →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
        omegaA A = {Subgroup.zpowers c} ∨
        CFSG.Assembly.IsElemAbelian 3 (oThreeWStar A) ∧ Nat.card (oThreeWStar A) = 9 ∧
        CFSG.ABGLocalTools.IsSylowOf 3 (oThreeWStar A) (wStar A) ∧
        ((omegaA A = orbitIn (oThreeWPre A) (Subgroup.zpowers c) ∧ (omegaA A).ncard = 3) ∨
          ∃ I ∈ thetaComponentsAt 3 d, d ∈ I ∧
            Sec4.IsTripleCover (I ⧸ aschbacherSolvableCore 3 I) (alternatingGroup (Fin 6)) ∧
            ∃ a ∈ A ⊓ K, a ∉ Subgroup.zpowers d ∧
              omegaA A = orbitIn (oThreeWPre A) (Subgroup.zpowers c) ∪
                orbitIn (oThreeWPre A) (Subgroup.zpowers a) ∧ (omegaA A).ncard = 6 ∧
              ∃ La : Subgroup G, lA A a = {La} ∧
                Nonempty (La ⧸ aschbacherSolvableCore 3 La ≃*
                  CFSG.Blueprint.NativeSporadic.J2))

@[expose] def Item134Sylow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L →
    Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ d ∈ A, d ≠ 1 →
    (∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S L ∧
      (Subgroup.center S).map S.subtype = Subgroup.zpowers d) →
    ∀ K ∈ thetaComponentsAt 3 d,
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K →
      K = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔
          inSubgroup (aschbacherSolvableCore 3) K →
      Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6)) →
      ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
        omegaA A = {Subgroup.zpowers c}

theorem rank3II_13_4_of_steps (h426 : Sec4.Item4_26ThetaA6) (h415 : Sec4.Item4_15)
    (hON : Item134ON) (h128 : Item134Arg128) (hSyl : Item134Sylow) : Item134 := by
  intro G _ _ A c L h hJ d hdA hd1 hS K hK hLK
  rcases dichotomy134 h426 h415 h hJ hdA hd1 hS hK hLK with ⟨hKeq, hA6⟩ | hON'
  · by_cases hW : Subgroup.normalizer (A : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers d : Set G)
    · rcases h128 G A c L h hJ d hdA hd1 hS K hK hLK hKeq hA6 hW with h1 | h2
      · exact Or.inl ⟨hKeq, hA6, h1⟩
      · exact Or.inr (Or.inl ⟨hKeq, hA6, hW, h2⟩)
    · exact Or.inl ⟨hKeq, hA6, hSyl G A c L h hJ d hdA hd1 hS K hK hLK hKeq hA6 hW⟩
  · exact Or.inr (Or.inr ⟨hON', hON G A c L h hJ d hdA hd1 hS K hK hLK hON'⟩)

end CFSG.RankThree.PartTwo.Sec13
