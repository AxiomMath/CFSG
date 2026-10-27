module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeTableZDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.TwE6
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelA
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelD
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelOuterD
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6CompLabel
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.OuterDispatch
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTypeA
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.PerfectCover CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

private theorem tzClass_twA_ne_A : LargeEvenLieTag.twA ≠ LargeEvenLieTag.A := by decide
private theorem tzClass_twA_ne_B : LargeEvenLieTag.twA ≠ LargeEvenLieTag.B := by decide
private theorem tzClass_twA_ne_C : LargeEvenLieTag.twA ≠ LargeEvenLieTag.C := by decide
private theorem tzClass_twA_ne_D : LargeEvenLieTag.twA ≠ LargeEvenLieTag.D := by decide
private theorem tzClass_twA_ne_twD : LargeEvenLieTag.twA ≠ LargeEvenLieTag.twD := by decide
private theorem tzClass_twA_ne_triD4 : LargeEvenLieTag.twA ≠ LargeEvenLieTag.triD4 := by decide
private theorem tzClass_two_ne_three : (2 : ℕ) ≠ 3 := by omega

private theorem tzClass_eq_twA_two_of_iso {lab : LargeEvenLabel} {m : ℕ}
    (h : GGLabelIso lab ⟨.twA, 2, m⟩) : lab = ⟨.twA, 2, m⟩ := by
  rcases h with h | h | h | h | h | h | h | h
  · exact h
  · rcases h.2.1 with hB | hB
    · exact absurd (by simpa using hB) tzClass_twA_ne_B
    · exact absurd (by simpa using hB) tzClass_twA_ne_C
  · exact absurd (congrArg LargeEvenLabel.tag h.2) tzClass_twA_ne_A
  · exact absurd (congrArg LargeEvenLabel.tag h.2) tzClass_twA_ne_D
  · exact absurd (congrArg LargeEvenLabel.rank h.2) tzClass_two_ne_three
  · exact absurd (congrArg LargeEvenLabel.tag h.2) tzClass_twA_ne_twD
  · exact absurd (congrArg LargeEvenLabel.tag h.2) tzClass_twA_ne_A
  · exact absurd (congrArg LargeEvenLabel.tag h.1) tzClass_twA_ne_twD

private theorem tzClass_three_eq_of_two_pow {n : ℕ} (hn : 1 ≤ n) {s : ℕ}
    (h : 2 ^ (3 * n) = 2 ^ (n * s)) : s = 3 := by
  have h1 : 3 * n = n * s := Nat.pow_right_injective (le_refl 2) h
  nlinarith [hn]

theorem tableZ_classA2
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    {n : ℕ} (hn : 1 ≤ n) (hq : S.D.q = 2 ^ n)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hΛ : LargeEvenInLambda2 ⟨.twA, 2, 3 * n⟩)
    (hlab : GGHasLabel ⟨.twA, 2, 3 * n⟩ (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) :
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 3 ∧
      (componentRoots (rootCharHom a) i).ncard = 6 ∧
      ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[3]) := by
  classical
  have h3L : ((3 : ℕ) : L) ≠ 0 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.natCast_ne_zero_of_ringChar_ne Nat.prime_three
      (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_ne_of_pow_eq_one Nat.prime_three hap h1)
  have hTp : rootDiagUnit Tag.E6 a ^ 3 = 1 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · obtain ⟨lab, hdeg, hrank, htagA, -, hRL⟩ :=
      rationalLabel_typeA S Nat.prime_three hT hap h1 i hA hQS
    obtain ⟨hlabΛ, hlabHas⟩ := hRL
    have hiso : GGLabelIso lab ⟨.twA, 2, 3 * n⟩ :=
      ggLabelRigidInput_holds lab ⟨.twA, 2, 3 * n⟩ _ hlabΛ hΛ hlabHas hlab
    have hlabeq : lab = ⟨.twA, 2, 3 * n⟩ := tzClass_eq_twA_two_of_iso hiso
    have hlabn : lab.n = 3 * n := by rw [hlabeq]
    have hlabrank : lab.rank = 2 := by rw [hlabeq]
    have hs3 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 3 := by
      apply tzClass_three_eq_of_two_pow hn
      calc 2 ^ (3 * n) = 2 ^ lab.n := by rw [hlabn]
        _ = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := hdeg
        _ = (2 ^ n) ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := by rw [hq]
        _ = 2 ^ (n * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by rw [pow_mul]
    have hncard6 : (componentRoots (rootCharHom a) i).ncard = 6 := by
      rw [hA.2, ← hrank, hlabrank]
    have htk : twistKind S.ρ (rootCharHom a) i ≠ .inner := by
      intro hinner
      have htag : lab.tag = .A := htagA hinner
      rw [hlabeq] at htag
      exact tzClass_twA_ne_A (by simpa using htag)
    have hni : ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[
          componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)]) := by
      intro hti
      exact htk (by unfold twistKind; rw [if_pos hti])
    rw [hs3] at hni
    exact ⟨hs3, hncard6, hni⟩
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_cand_of_class
        CFSG.HardMathSupport.Timmesfeld.CrossChar.kacE6
        CFSG.HardMathSupport.Timmesfeld.CrossChar.facts_E6
        CFSG.HardMathSupport.Timmesfeld.CrossChar.e6_tree
        CFSG.HardMathSupport.Timmesfeld.CrossChar.e6_adj
        CFSG.HardMathSupport.Timmesfeld.CrossChar.e6_check
        CFSG.HardMathSupport.Timmesfeld.CrossChar.e6_lt
        CFSG.HardMathSupport.Timmesfeld.CrossChar.e6_card
        S Nat.prime_three h3L hTp i
    have hshape := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.e6_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD | hE
    · exact (hA hA').elim
    · exfalso
      by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[
            componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)])
      · obtain ⟨lab, -, htagD, -, hRL⟩ :=
          rationalLabel_innerD_E6 S Nat.prime_three h3L hT hTp i hD hinner hQS
        obtain ⟨hlabΛ, hlabHas⟩ := hRL
        have hiso : GGLabelIso lab ⟨.twA, 2, 3 * n⟩ :=
          ggLabelRigidInput_holds lab ⟨.twA, 2, 3 * n⟩ _ hlabΛ hΛ hlabHas hlab
        have hlabeq : lab = ⟨.twA, 2, 3 * n⟩ := tzClass_eq_twA_two_of_iso hiso
        rw [hlabeq] at htagD
        exact tzClass_twA_ne_D (by simpa using htagD)
      · obtain ⟨lab, -, hc1, hc2, hc3, hRL⟩ :=
          rationalLabel_outerD S Nat.prime_three hT hap h1 i hD hinner hQS
        obtain ⟨hlabΛ, hlabHas⟩ := hRL
        have hiso : GGLabelIso lab ⟨.twA, 2, 3 * n⟩ :=
          ggLabelRigidInput_holds lab ⟨.twA, 2, 3 * n⟩ _ hlabΛ hΛ hlabHas hlab
        have hlabeq : lab = ⟨.twA, 2, 3 * n⟩ := tzClass_eq_twA_two_of_iso hiso
        have hk := twistKind_outerD S.ρ (rootCharHom a) i hD hinner
        rcases hk with hk2 | ⟨hkexc, hr4⟩
        · by_cases hr : compRank (componentRoots (rootCharHom a) i) = 4
          · rcases hc2 hk2 hr with hD4 | htri
            · rw [hlabeq] at hD4
              exact tzClass_twA_ne_twD (by simpa using hD4.1)
            · rw [hlabeq] at htri
              exact tzClass_twA_ne_triD4 (by simpa using htri)
          · obtain ⟨htag, -⟩ := hc1 hk2 hr
            rw [hlabeq] at htag
            exact tzClass_twA_ne_twD (by simpa using htag)
        · rcases hc3 hkexc hr4 with hD4 | htri
          · rw [hlabeq] at hD4
            exact tzClass_twA_ne_twD (by simpa using hD4.1)
          · rw [hlabeq] at htri
            exact tzClass_twA_ne_triD4 (by simpa using htri)
    · exact (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.false_of_e6Class_E
        S Nat.prime_three h3L hTp h1 i hE.1 hE.2).elim

private theorem tzClass_triD4_ne_A : LargeEvenLieTag.triD4 ≠ LargeEvenLieTag.A := by decide
private theorem tzClass_triD4_ne_B : LargeEvenLieTag.triD4 ≠ LargeEvenLieTag.B := by decide
private theorem tzClass_triD4_ne_C : LargeEvenLieTag.triD4 ≠ LargeEvenLieTag.C := by decide
private theorem tzClass_triD4_ne_D : LargeEvenLieTag.triD4 ≠ LargeEvenLieTag.D := by decide
private theorem tzClass_triD4_ne_twA : LargeEvenLieTag.triD4 ≠ LargeEvenLieTag.twA := by decide
private theorem tzClass_triD4_ne_twD : LargeEvenLieTag.triD4 ≠ LargeEvenLieTag.twD := by decide

private theorem tzClass_eq_triD4_of_iso {lab : LargeEvenLabel} {m : ℕ}
    (h : GGLabelIso lab ⟨.triD4, 0, m⟩) : lab = ⟨.triD4, 0, m⟩ := by
  rcases h with h | h | h | h | h | h | h | h
  · exact h
  · rcases h.2.1 with hB | hB
    · exact absurd (by simpa using hB) tzClass_triD4_ne_B
    · exact absurd (by simpa using hB) tzClass_triD4_ne_C
  · exact absurd (congrArg LargeEvenLabel.tag h.2) tzClass_triD4_ne_A
  · exact absurd (congrArg LargeEvenLabel.tag h.2) tzClass_triD4_ne_D
  · exact absurd (congrArg LargeEvenLabel.tag h.2) tzClass_triD4_ne_twA
  · exact absurd (congrArg LargeEvenLabel.tag h.2) tzClass_triD4_ne_twD
  · exact absurd (congrArg LargeEvenLabel.tag h.2) tzClass_triD4_ne_A
  · exact absurd (congrArg LargeEvenLabel.tag h.1) tzClass_triD4_ne_twD

private theorem tzClass_one_eq_of_two_pow {n : ℕ} (hn : 1 ≤ n) {s : ℕ}
    (h : 2 ^ n = 2 ^ (n * s)) : s = 1 := by
  have h1 : n = n * s := Nat.pow_right_injective (le_refl 2) h
  nlinarith [hn]

theorem tableZ_classTriD4
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    {n : ℕ} (hn : 1 ≤ n) (hq : S.D.q = 2 ^ n)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hlab : GGHasLabel ⟨.triD4, 0, n⟩ (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) :
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 ∧
      compRank (componentRoots (rootCharHom a) i) = 4 ∧
      (componentRoots (rootCharHom a) i).ncard = 24 ∧
      ¬ twistInner (componentRoots (rootCharHom a) i)
        (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) := by
  classical
  have h3L : ((3 : ℕ) : L) ≠ 0 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.natCast_ne_zero_of_ringChar_ne Nat.prime_three
      (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_ne_of_pow_eq_one Nat.prime_three hap h1)
  have hTp : rootDiagUnit Tag.E6 a ^ 3 = 1 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.rootDiagUnit_pow_eq_one_of_forall hap
  have hΛ : LargeEvenInLambda2 ⟨.triD4, 0, n⟩ := by
    show 1 ≤ n ∧ (0 : ℕ) = 0
    exact ⟨hn, rfl⟩
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · obtain ⟨lab, -, hrank, -, -, hRL⟩ :=
      rationalLabel_typeA S Nat.prime_three hT hap h1 i hA hQS
    obtain ⟨hlabΛ, hlabHas⟩ := hRL
    have hiso : GGLabelIso lab ⟨.triD4, 0, n⟩ :=
      ggLabelRigidInput_holds lab ⟨.triD4, 0, n⟩ _ hlabΛ hΛ hlabHas hlab
    have hlabeq : lab = ⟨.triD4, 0, n⟩ := tzClass_eq_triD4_of_iso hiso
    have hrank0 : lab.rank = 0 := by rw [hlabeq]
    exact absurd hA.1 (by omega)
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_cand_of_class
        CFSG.HardMathSupport.Timmesfeld.CrossChar.kacE6
        CFSG.HardMathSupport.Timmesfeld.CrossChar.facts_E6
        CFSG.HardMathSupport.Timmesfeld.CrossChar.e6_tree
        CFSG.HardMathSupport.Timmesfeld.CrossChar.e6_adj
        CFSG.HardMathSupport.Timmesfeld.CrossChar.e6_check
        CFSG.HardMathSupport.Timmesfeld.CrossChar.e6_lt
        CFSG.HardMathSupport.Timmesfeld.CrossChar.e6_card
        S Nat.prime_three h3L hTp i
    have hshape := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.e6_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD | hE
    · exact (hA hA').elim
    · by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)])
      · obtain ⟨lab, -, htagD, -, hRL⟩ :=
          rationalLabel_innerD_E6 S Nat.prime_three h3L hT hTp i hD hinner hQS
        obtain ⟨hlabΛ, hlabHas⟩ := hRL
        have hiso : GGLabelIso lab ⟨.triD4, 0, n⟩ :=
          ggLabelRigidInput_holds lab ⟨.triD4, 0, n⟩ _ hlabΛ hΛ hlabHas hlab
        have hlabeq : lab = ⟨.triD4, 0, n⟩ := tzClass_eq_triD4_of_iso hiso
        rw [hlabeq] at htagD
        exact absurd (by simpa using htagD) tzClass_triD4_ne_D
      · obtain ⟨lab, hdeg, hc1, -, -, hRL⟩ :=
          rationalLabel_outerD S Nat.prime_three hT hap h1 i hD hinner hQS
        obtain ⟨hlabΛ, hlabHas⟩ := hRL
        have hiso : GGLabelIso lab ⟨.triD4, 0, n⟩ :=
          ggLabelRigidInput_holds lab ⟨.triD4, 0, n⟩ _ hlabΛ hΛ hlabHas hlab
        have hlabeq : lab = ⟨.triD4, 0, n⟩ := tzClass_eq_triD4_of_iso hiso
        have hlabn : lab.n = n := by rw [hlabeq]
        have hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 := by
          apply tzClass_one_eq_of_two_pow hn
          calc 2 ^ n = 2 ^ lab.n := by rw [hlabn]
            _ = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := hdeg
            _ = (2 ^ n) ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := by rw [hq]
            _ = 2 ^ (n * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by
              rw [pow_mul]
        have hk := twistKind_outerD S.ρ (rootCharHom a) i hD hinner
        have hr4 : compRank (componentRoots (rootCharHom a) i) = 4 := by
          rcases hk with hk2 | ⟨-, hr4⟩
          · by_cases hr : compRank (componentRoots (rootCharHom a) i) = 4
            · exact hr
            · obtain ⟨htag, -⟩ := hc1 hk2 hr
              rw [hlabeq] at htag
              exact absurd (by simpa using htag) tzClass_triD4_ne_twD
          · exact hr4
        have hncard24 : (componentRoots (rootCharHom a) i).ncard = 24 := by
          rw [hD.2, hr4]
        have hni : ¬ twistInner (componentRoots (rootCharHom a) i)
            (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) := by
          rw [hs1, Function.iterate_one] at hinner
          exact hinner
        exact ⟨hs1, hr4, hncard24, hni⟩
    · exact (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.false_of_e6Class_E
        S Nat.prime_three h3L hTp h1 i hE.1 hE.2).elim

end CFSG.StandardType.TablePThreeKG

end
