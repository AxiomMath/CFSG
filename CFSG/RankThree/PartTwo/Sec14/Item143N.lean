module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
public import CFSG.RankThree.PartTwo.Sec14.Item1446

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Item143N (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ a ∈ A, a ≠ 1 → Subgroup.zpowers a ∉ omegaA A →
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

theorem item143_of_item143N {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (h : Item143N A LB) : Item143 A LB := fun a ha ha1 hΩ Q hQ =>
  (h a ha ha1 hΩ Q hQ).imp_right (Or.imp_right fun ⟨b, d, Lb, hb, hLb, hJ, hdA, hd1, hdc, hab,
    X, hX, _, hcase⟩ => ⟨b, d, Lb, hb, hLb, hJ, hdA, hd1, hdc, hab, X, hX, hcase⟩)

theorem concl143_of_item143N {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (h : Item143N A LB) : Concl143 A LB := fun a ha ha1 hΩ Q hQ => (h a ha ha1 hΩ Q hQ).1

end CFSG.RankThree.PartTwo.Sec14
