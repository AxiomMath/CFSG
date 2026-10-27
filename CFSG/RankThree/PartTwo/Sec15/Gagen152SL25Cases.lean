module

public import CFSG.RankThree.PartTwo.Sec15.Ronan152SL25Narrow

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank

@[expose] noncomputable def Step152SL25NoConfR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → AllPointsHJ A →
    ∀ M X : Subgroup G, Ctx152J A (lB A) M X →
    ∀ (B : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A B → IsLBConfig A B b d Lb →
      Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) = (B : Set G) →
        False

@[expose] noncomputable def Step152SL25OneOmegaR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → AllPointsHJ A →
    ∀ M X : Subgroup G, Ctx152J A (lB A) M X →
    ∀ (B : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A B → IsLBConfig A B b d Lb →
      Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) = (B : Set G) →
      omegaA A = {Subgroup.zpowers b} → False

@[expose] noncomputable def Step152SL25OmegaNeR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → AllPointsHJ A →
    ∀ M X : Subgroup G, Ctx152J A (lB A) M X →
    ∀ (B : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A B → IsLBConfig A B b d Lb →
      Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) = (B : Set G) →
      omegaA A ≠ {Subgroup.zpowers b} → False

theorem step152SL25NoConfR_of_omega (h1 : Step152SL25OneOmegaR) (hne : Step152SL25OmegaNeR) :
    Step152SL25NoConfR := by
  intro G _ _ A c L h hHJ M X hctx B b d Lb hB hc hcent
  by_cases hΩ : omegaA A = {Subgroup.zpowers b}
  · exact h1 G A c L h hHJ M X hctx B b d Lb hB hc hcent hΩ
  · exact hne G A c L h hHJ M X hctx B b d Lb hB hc hcent hΩ

theorem y4CoreExclSL25HJR_of_noConf
    (h142 : Item142AllS14)
    (h425 : Sec4.Item4_25Fix) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h41 : Sec4.Item4_1LargePrime) (hGW : Sec6.GWLBalanceStatement)
    (hno : Step152SL25NoConfR) : Y4CoreExclSL25HJR :=
  y4CoreExclSL25HJR_of_narrow h142 h425 h134 h48 h41 hGW
    (fun G _ _ A c L h hHJ M X hctx B b d Lb hB hc hcent =>
      (hno G A c L h hHJ M X hctx B b d Lb hB hc hcent).elim)
    (fun G _ _ A c L h hHJ M X hctx B b d Lb hB hc hcent =>
      (hno G A c L h hHJ M X hctx B b d Lb hB hc hcent).elim)
    (fun G _ _ A c L h hHJ M X hctx B b d Lb hB hc hcent =>
      (hno G A c L h hHJ M X hctx B b d Lb hB hc hcent).elim)

theorem y4CoreExclSL25HJR_of_omega
    (h142 : Item142AllS14)
    (h425 : Sec4.Item4_25Fix) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h41 : Sec4.Item4_1LargePrime) (hGW : Sec6.GWLBalanceStatement)
    (h1 : Step152SL25OneOmegaR) (hne : Step152SL25OmegaNeR) : Y4CoreExclSL25HJR :=
  y4CoreExclSL25HJR_of_noConf h142 h425 h134 h48 h41 hGW (step152SL25NoConfR_of_omega h1 hne)

end CFSG.RankThree.PartTwo.Sec15
