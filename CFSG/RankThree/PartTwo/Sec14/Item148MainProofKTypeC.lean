module

public import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)

variable {G : Type} [Group G] [Finite G]

@[expose] def KThetaC148 (K Le : Subgroup G) : Prop :=
  Nonempty (↥K ⧸ aschbacherSolvableCore 3 ↥K ≃* ↥Le ⧸ aschbacherSolvableCore 3 ↥Le) ∨
    ((Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
        (∃ _ : Fact (Nat.Prime 5), Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃*
          projSL 3 (GaloisField 5 2))) ∨
        (∃ _ : Fact (Nat.Prime 5), Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃*
          projSU 3 5 1))) ∧
      Nonempty (↥K ⧸ aschbacherSolvableCore 3 ↥K ≃* alternatingGroup (Fin 7))) ∨
    (∃ (p f e' : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ 1 ≤ e' ∧
      Sec4.IsoLThreePi (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) p (f * e') ∧
      IsLThreeEpsAt (↥K ⧸ aschbacherSolvableCore 3 ↥K) p f)

@[expose] def Step148KThetaHJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G), Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      Subgroup.zpowers e ∈ omegaA A → Le ∈ lA A e →
      Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.J2) →
        KThetaC148 K Le

@[expose] def Step148KThetaL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G), Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      Subgroup.zpowers e ∈ omegaA A → Le ∈ lA A e →
      IsLThreePi (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) →
        KThetaC148 K Le

@[expose] def Step148KThetaA7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G), Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      Subgroup.zpowers e ∈ omegaA A → Le ∈ lA A e →
      Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* alternatingGroup (Fin 7)) →
        KThetaC148 K Le

@[expose] def Step148KThetaM22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G), Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      Subgroup.zpowers e ∈ omegaA A → Le ∈ lA A e →
      Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.M22) →
        KThetaC148 K Le

@[expose] def Step148KThetaM12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G), Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      Subgroup.zpowers e ∈ omegaA A → Le ∈ lA A e →
      Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.M12) →
        KThetaC148 K Le

theorem step148KThetaOmega_of (hHJ : Step148KThetaHJ) (hL3 : Step148KThetaL3)
    (hA7 : Step148KThetaA7) (hM22 : Step148KThetaM22) (hM12 : Step148KThetaM12) :
    Step148KThetaOmega := by
  intro G _ _ A c L h Y hY hs hYB B Q e K Le hP he hLe
  rcases (h.chosen136.2 e he Le hLe).1 with hJ | hL | hA | hM | hM'
  · exact hHJ G A c L h Y hY hs hYB B Q e K Le hP he hLe hJ
  · exact hL3 G A c L h Y hY hs hYB B Q e K Le hP he hLe hL
  · exact hA7 G A c L h Y hY hs hYB B Q e K Le hP he hLe hA
  · exact hM22 G A c L h Y hY hs hYB B Q e K Le hP he hLe hM
  · exact hM12 G A c L h Y hY hs hYB B Q e K Le hP he hLe hM'

theorem step148KType_of_theta_types
    (hθ : Step148KTheta)
    (hHJ : Step148KThetaHJ) (hL3 : Step148KThetaL3) (hA7 : Step148KThetaA7)
    (hM22 : Step148KThetaM22) (hM12 : Step148KThetaM12) (hON : Step148KThetaON) :
    Step148KType :=
  step148KType_of_theta hθ (step148KThetaOmega_of hHJ hL3 hA7 hM22 hM12) hON

theorem step148KThetaHJ_of_omega (h : Step148KThetaOmega) : Step148KThetaHJ :=
  fun G _ _ A c L hS Y hY hs hYB B Q e K Le hP he hLe _ =>
    h G A c L hS Y hY hs hYB B Q e K Le hP he hLe

theorem step148KThetaL3_of_omega (h : Step148KThetaOmega) : Step148KThetaL3 :=
  fun G _ _ A c L hS Y hY hs hYB B Q e K Le hP he hLe _ =>
    h G A c L hS Y hY hs hYB B Q e K Le hP he hLe

theorem step148KThetaA7_of_omega (h : Step148KThetaOmega) : Step148KThetaA7 :=
  fun G _ _ A c L hS Y hY hs hYB B Q e K Le hP he hLe _ =>
    h G A c L hS Y hY hs hYB B Q e K Le hP he hLe

theorem step148KThetaM22_of_omega (h : Step148KThetaOmega) : Step148KThetaM22 :=
  fun G _ _ A c L hS Y hY hs hYB B Q e K Le hP he hLe _ =>
    h G A c L hS Y hY hs hYB B Q e K Le hP he hLe

theorem step148KThetaM12_of_omega (h : Step148KThetaOmega) : Step148KThetaM12 :=
  fun G _ _ A c L hS Y hY hs hYB B Q e K Le hP he hLe _ =>
    h G A c L hS Y hY hs hYB B Q e K Le hP he hLe

end CFSG.RankThree.PartTwo.Sec14
