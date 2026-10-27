module

public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec14.Std

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Item143NAt (A : Subgroup G) (LB : Subgroup G → Subgroup G)
    (a : G) : Prop :=
  ∀ Q ∈ maxInvariantPiSubgroups (delta A LB (Subgroup.centralizer ({a} : Set G))) A
      (piCompl 3),
    Q ∈ collectionIn (scriptQ A LB) (Subgroup.centralizer ({a} : Set G)) ∧
    (delta A LB (Subgroup.centralizer ({a} : Set G)) =
        pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ∨
      ∃ (b d : G) (Lb : Subgroup G), Subgroup.zpowers b ∈ omegaA A ∧ Lb ∈ lA A b ∧
        Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
        d ∈ A ∧ d ≠ 1 ∧ IsThreeCentralIn Lb d ∧ a ∈ Subgroup.closure {b, d} ∧
        ∃ X : Subgroup G,
          delta A LB (Subgroup.centralizer ({a} : Set G)) =
            pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
              pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X ∧
          Subgroup.centralizer ({a} : Set G) ≤
            Subgroup.normalizer
              ((pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X : Subgroup G) :
                Set G) ∧
          ((X ∈ thetaComponentsAt 3 a ∧
              X = LB (Subgroup.closure {a, b}) ⊔ inSubgroup (aschbacherSolvableCore 3) X ∧
              Subgroup.zpowers a ≠ Subgroup.zpowers d) ∨
            (Subgroup.zpowers a = Subgroup.zpowers d ∧
              (∃ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 a ∧ 𝒳.Nonempty ∧ X = sSup 𝒳) ∧
              (Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
                  CFSG.Blueprint.NativeSporadic.ON ∨
                Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
                  (alternatingGroup (Fin 6)) ∨
                IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X)))))

theorem item143N_iff_forall_at {A : Subgroup G} {LB : Subgroup G → Subgroup G} :
    Item143N A LB ↔ ∀ a ∈ A, a ≠ 1 → Subgroup.zpowers a ∉ omegaA A → Item143NAt A LB a :=
  Iff.rfl

theorem exists_isLBConfig_of_lB_ne_bot {A B : Subgroup G} (h : lB A B ≠ ⊥) :
    ∃ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb := by
  by_contra hno
  push Not at hno
  exact h (lB_eq_bot hno)

@[expose] def Step143HJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ a ∈ A, a ≠ 1 → Subgroup.zpowers a ∉ omegaA A →
      ∀ (B : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A B → a ∈ B →
        IsLBConfig A B b d Lb → Item143NAt A (lB A) a

@[expose] def Step143HJMem : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ a ∈ A, a ≠ 1 → Subgroup.zpowers a ∉ omegaA A →
      ∀ (B : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A B → a ∈ B →
        IsLBConfig A B b d Lb →
          ∀ Q ∈ maxInvariantPiSubgroups (delta A (lB A) (Subgroup.centralizer ({a} : Set G))) A
            (piCompl 3), Q ∈ collectionIn (scriptQ A (lB A)) (Subgroup.centralizer ({a} : Set G))

theorem step143HJMem_of_step143HJ (h : Step143HJ) : Step143HJMem :=
  fun G _ _ A c L hs a ha ha1 hΩ B b d Lb hB haB hc Q hQ =>
    (h G A c L hs a ha ha1 hΩ B b d Lb hB haB hc Q hQ).1

end CFSG.RankThree.PartTwo.Sec14
