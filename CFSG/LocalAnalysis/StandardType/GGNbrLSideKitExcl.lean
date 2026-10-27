module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideDefs
public import CFSG.LocalAnalysis.StandardType.MarkingDict
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
import CFSG.LocalAnalysis.SeitzReduction.CrossChar
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import all CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.EmptyFaithful.S146zYFacts
public import CFSG.Quasithin.EmptyFaithful.S146zYRes
public import CFSG.Quasithin.H13.NQCoreP134Main
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs
public import Certificates.Certificate8026Base

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def GGNbrLSideClsDet : Prop :=
  ∀ {X : Type} [Group X] {lab : LargeEvenLabel}, LargeEvenInLambda2 lab →
    CFSG.LocalAnalysis.GLTheoremA.IsClsLab lab → MarkedModel lab X →
      ∀ {t : StatedLieTag} {n f' : ℕ}, CFSG.Blueprint.LieModel X t n 2 f' →
        t = markTag lab ∧ n = markRank lab ∧ f' = markDeg lab

private theorem lieModel_PSL_of_projectiveSL {X : Type} [Group X] {n p f : ℕ} {K : Type}
    [Field K] [Finite K] (hadm : CFSG.Open.StatedLieAdmissible .PSL n p f)
    (hK : Nat.card K = p ^ f) (e : X ≃* projectiveSL n K) :
    CFSG.Blueprint.LieModel X .PSL n p f := by
  refine Or.inl ⟨?_, hadm, K, inferInstance, inferInstance, hK, ⟨?_⟩⟩
  · decide
  · exact e.trans
      ((CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
          n K).symm.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K))

private theorem lieOrderNumerator_PSL_three (Q : ℕ) :
    CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL 3 Q =
      Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) := by
  simp [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator, Finset.prod_Icc_succ_top,
    show (3 : ℕ) * (3 - 1) / 2 = 3 from rfl]

private theorem lt_25920_of_odd_order {X d Q : ℕ} (hQ : 5 ≤ Q) (hd : d ≤ 3)
    (h : X * d = Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1))) : 25920 < X := by
  have hQ2 : 24 ≤ Q ^ 2 - 1 := by
    have h : 25 ≤ Q ^ 2 := by
      calc 25 = 5 * 5 := by norm_num
        _ ≤ Q * Q := Nat.mul_le_mul hQ hQ
        _ = Q ^ 2 := (pow_two Q).symm
    omega
  have hQ3 : 124 ≤ Q ^ 3 - 1 := by
    have h : 125 ≤ Q ^ 3 := by
      calc 125 = 5 * 5 * 5 := by norm_num
        _ ≤ Q * Q * Q := Nat.mul_le_mul (Nat.mul_le_mul hQ hQ) hQ
        _ = Q ^ 3 := by ring
    omega
  have h5 : 5 ^ 3 ≤ Q ^ 3 := Nat.pow_le_pow_left hQ 3
  have hRHS : 5 ^ 3 * (24 * 124) ≤ Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) :=
    Nat.mul_le_mul h5 (Nat.mul_le_mul hQ2 hQ3)
  have hbound : 5 ^ 3 * (24 * 124) ≤ X * d := by rw [h]; exact hRHS
  have hX3 : 5 ^ 3 * (24 * 124) ≤ X * 3 := hbound.trans (Nat.mul_le_mul_left X hd)
  have : (372000 : ℕ) ≤ X * 3 := by
    have : (5 : ℕ) ^ 3 * (24 * 124) = 372000 := by norm_num
    omega
  omega

theorem ggNbrLSideExcl (hDet : GGNbrLSideClsDet)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {X : Type} [Group X] {F : Type} [Field F] [Finite F] (hF4 : 4 ≤ Nat.card F)
    (e : X ≃* projectiveSL 3 F) {t : StatedLieTag} {m f : ℕ}
    (hX : CFSG.Blueprint.LieModel X t m 2 f) :
    t = .PSL ∧ m = 3 ∧ Nat.card F = 2 ^ f := by
  by_cases h2 : ∃ g : ℕ, Nat.card F = 2 ^ g
  ·
    obtain ⟨g, hg⟩ := h2
    have hg1 : 1 ≤ g := by
      rcases Nat.eq_zero_or_pos g with hg0 | hpos
      · rw [hg0, pow_zero] at hg; omega
      · exact hpos
    let lab : LargeEvenLabel := ⟨.A, 2, g⟩
    have hl : LargeEvenInLambda2 lab := by
      refine ⟨hg1, by norm_num, ?_⟩
      intro h
      exact absurd h (by norm_num)
    have hcls : CFSG.LocalAnalysis.GLTheoremA.IsClsLab lab := by
      unfold CFSG.LocalAnalysis.GLTheoremA.IsClsLab
      exact Or.inl rfl
    have hadm : StatedLieAdmissible .PSL 3 2 g := by
      refine ⟨Nat.prime_two, hg1, by norm_num, ?_, ?_⟩
      · rintro h; simp only [Prod.mk.injEq] at h; exact absurd h.1 (by norm_num)
      · rintro h; simp only [Prod.mk.injEq] at h; exact absurd h.1 (by norm_num)
    have hM : MarkedModel lab X := by
      show CFSG.Blueprint.LieModel X .PSL 3 2 g
      exact lieModel_PSL_of_projectiveSL hadm hg e
    obtain ⟨ht, hm, hf'⟩ := hDet hl hcls hM hX
    have hfg : f = g := hf'
    refine ⟨ht, hm, ?_⟩
    rw [hg, hfg]
  ·
    exfalso
    haveI : Fintype F := Fintype.ofFinite F
    obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' F
    rw [← Nat.card_eq_fintype_card] at hcard
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact h2 ⟨(n : ℕ), hcard⟩
    have hg1 : 1 ≤ (n : ℕ) := by have := n.pos; omega
    have hadm : StatedLieAdmissible .PSL 3 p (n : ℕ) := by
      refine ⟨hp, hg1, by norm_num, ?_, ?_⟩
      · rintro h; simp only [Prod.mk.injEq] at h; exact absurd h.1 (by norm_num)
      · rintro h; simp only [Prod.mk.injEq] at h; exact absurd h.1 (by norm_num)
    have hmodel : CFSG.Blueprint.LieModel X .PSL 3 p (n : ℕ) :=
      lieModel_PSL_of_projectiveSL hadm hcard e
    have hodd : CFSG.Blueprint.OddLieType X :=
      ⟨.PSL, 3, p, (n : ℕ), hp, hp2, hadm, hmodel⟩
    have hoddOrder := (hO X .PSL 3 p (n : ℕ) hadm hmodel).2.1
    rw [lieOrderNumerator_PSL_three] at hoddOrder
    have hQ5 : 5 ≤ p ^ (n : ℕ) := by
      have hQ4 : 4 ≤ p ^ (n : ℕ) := by rw [← hcard]; exact hF4
      have hoddQ : Odd (p ^ (n : ℕ)) := (hp.odd_of_ne_two hp2).pow
      rcases hoddQ with ⟨k, hk⟩
      omega
    have hd3 : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL 3 (p ^ (n : ℕ)) ≤ 3 := by
      show Nat.gcd 3 (p ^ (n : ℕ) - 1) ≤ 3
      exact Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 _)
    have hXgt : 25920 < Nat.card X := lt_25920_of_odd_order hQ5 hd3 hoddOrder
    rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType hO hX hodd with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have h60 : Nat.card X = 60 := by
        have hadm' : StatedLieAdmissible .PSL 2 2 2 := by
          refine ⟨Nat.prime_two, by norm_num, by norm_num, ?_, ?_⟩
          · rintro h; simp only [Prod.mk.injEq] at h; exact absurd h.2 (by norm_num)
          · rintro h; simp only [Prod.mk.injEq] at h; exact absurd h.2 (by norm_num)
        have h := (hO X .PSL 2 2 2 hadm' hX).2.1
        have hd : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL 2 (2 ^ 2) = 1 := by
          decide
        have hn : CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL 2 (2 ^ 2) = 60 := by
          decide
        rw [hd, mul_one, hn] at h
        exact h
      omega
    · have h168 : Nat.card X = 168 := by
        have hadm' : StatedLieAdmissible .PSL 3 2 1 := by
          refine ⟨Nat.prime_two, by norm_num, by norm_num, ?_, ?_⟩
          · rintro h; simp only [Prod.mk.injEq] at h; exact absurd h.1 (by norm_num)
          · rintro h; simp only [Prod.mk.injEq] at h; exact absurd h.1 (by norm_num)
        have h := (hO X .PSL 3 2 1 hadm' hX).2.1
        have hd : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL 3 (2 ^ 1) = 1 := by
          decide
        have hn : CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL 3 (2 ^ 1) = 168 := by
          decide
        rw [hd, mul_one, hn] at h
        exact h
      omega
    · have h25920 : Nat.card X = 25920 := by
        have hadm' : StatedLieAdmissible .PSU 4 2 1 := by
          refine ⟨Nat.prime_two, by norm_num, by norm_num, ?_⟩
          rintro h; simp only [Prod.mk.injEq] at h; exact absurd h.1 (by norm_num)
        have h := (hO X .PSU 4 2 1 hadm' hX).2.1
        have hd : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSU 4 (2 ^ 1) = 1 := by
          decide
        have hn : CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSU 4 (2 ^ 1) = 25920 := by
          decide
        rw [hd, mul_one, hn] at h
        exact h
      omega

end CFSG.StandardType
