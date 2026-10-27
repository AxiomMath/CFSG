module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartTwo.Sec13.Notation
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def wStar {G : Type*} [Group G] (A : Subgroup G) : Subgroup (MulAut A) :=
  Sec4.autIn ⊤ A

@[expose] def oThreeWStar {G : Type*} [Group G] (A : Subgroup G) : Subgroup (MulAut A) :=
  (CFSG.pCore 3 (wStar A)).map (wStar A).subtype

@[expose] def oThreeWPre {G : Type*} [Group G] (A : Subgroup G) : Subgroup G :=
  ((oThreeWStar A).comap A.normalizerMonoidHom).map (Subgroup.normalizer (A : Set G)).subtype

@[expose] def orbitIn {G : Type*} [Group G] (X F : Subgroup G) : Set (Subgroup G) :=
  {F' | ∃ x ∈ X, F' = F.map (MulAut.conj x).toMonoidHom}

@[expose] def Item134 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L →
    Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ d ∈ A, d ≠ 1 →
    (∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S L ∧
      (Subgroup.center S).map S.subtype = Subgroup.zpowers d) →
    ∀ K ∈ thetaComponentsAt 3 d,
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K →
      (K = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔
            inSubgroup (aschbacherSolvableCore 3) K ∧
          Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6)) ∧
          omegaA A = {Subgroup.zpowers c}) ∨
        (K = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔
            inSubgroup (aschbacherSolvableCore 3) K ∧
          Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6)) ∧
          Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) ∧
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
                    CFSG.Blueprint.NativeSporadic.J2))) ∨
        (Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) CFSG.Blueprint.NativeSporadic.ON ∧
          Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) ∧
          omegaA A = orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers c) ∧
          (omegaA A).ncard = 12)

@[expose] def Item135 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → HypS A ∨ HypT A → CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L)

end CFSG.RankThree.PartTwo.Sec13
