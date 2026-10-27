module

public import CFSG.RankThree.PartTwo.Sec8.Hering418Model
public import CFSG.RankThree.PartTwo.Sec4.Item413Orders
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
public import CFSG.Models.PGL
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineGroups
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSL
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF418.Type418
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec6.Item65One

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderDivisor)
open CFSG.HardMathSupport.Lang.Coordinator (OuterFixedOrderBoundAt)

theorem inner_of_outerBound {Y : Type} [Group Y] [Finite Y] {t : StatedLieTag} {n p f : ℕ}
    (hb : OuterFixedOrderBoundAt t) (hadm : StatedLieAdmissible t n p f)
    (hmodel : CFSG.Blueprint.LieModel Y t n p f) (ht : t ≠ .Tits)
    (hdiv : ¬ 3 ∣ lieOrderDivisor t n (p ^ f)) (hD4 : ¬ (t = .POmegaPlus ∧ n = 4 ∧ 3 = 3))
    (htri : t ≠ .trialityD4) (hf : ¬ 3 ∣ f) {α : MulAut Y} (hα : α ^ 3 = 1) :
    α ∈ (MulAut.conj : Y →* MulAut Y).range := by
  by_contra hout
  rcases hb Y n p f hadm hmodel ht 3 Nat.prime_three (by norm_num) hdiv hD4 α hα hout with
    ⟨f₀, hf0, -⟩ | ⟨h, -, -⟩
  · exact hf ⟨f₀, hf0⟩
  · exact htri h

theorem inner_of_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : ∀ τ : MulAut Y, τ ^ 3 = 1 → τ ∈ (MulAut.conj : Y →* MulAut Y).range)
    {σ : MulAut X} (hσ : σ ^ 3 = 1) : σ ∈ (MulAut.conj : X →* MulAut X).range := by
  have h : (MulAut.congr e σ) ^ 3 = 1 := by rw [← map_pow, hσ, map_one]
  exact (KFacts.isInnerAut_congr e σ).mp (hY _ h)

theorem inner_projSL {n p f : ℕ} [Fact p.Prime] (hadm : StatedLieAdmissible .PSL n p f)
    (hdiv : ¬ 3 ∣ Nat.gcd n (p ^ f - 1)) (hf : ¬ 3 ∣ f) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* projSL n (GaloisField p f)) {α : MulAut Y} (hα : α ^ 3 = 1) :
    α ∈ (MulAut.conj : Y →* MulAut Y).range :=
  inner_of_outerBound (t := .PSL) (n := n) (p := p) (f := f)
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.outerFixedOrderBoundAt_PSL hadm
    (Or.inl ⟨by decide, CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm e⟩)
    (by decide) hdiv (fun h => absurd h.1 (by decide)) (by decide) hf hα

theorem inner_projSU {n p f : ℕ} [Fact p.Prime] (hadm : StatedLieAdmissible .PSU n p f)
    (hdiv : ¬ 3 ∣ Nat.gcd n (p ^ f + 1)) (hf : ¬ 3 ∣ f) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* projSU n p f) {α : MulAut Y} (hα : α ^ 3 = 1) :
    α ∈ (MulAut.conj : Y →* MulAut Y).range :=
  inner_of_outerBound (t := .PSU) (n := n) (p := p) (f := f)
    CFSG.HardMathSupport.Lang.Coordinator.outerFixedOrderBoundAt_PSU hadm
    (Or.inl ⟨by decide, CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm e⟩)
    (by decide) hdiv (fun h => absurd h.1 (by decide)) (by decide) hf hα

section CardCfg

variable {G : Type} [Group G] [Finite G] {L K : Subgroup G} {a b : G}

theorem Cfg.false_of_card (c : Cfg L K a b) (hT : Type418Arith (K ⧸ aschbacherSolvableCore 3 K))
    (hαI : c.alpha ∈ innBar L) (hβI : c.beta ∈ innBar L) {M : ℕ}
    (hM : Nat.card (L ⧸ aschbacherSolvableCore 3 L) ∣ M) (hM' : ¬ 3 ^ 4 ∣ M ∨ ¬ 7 ∣ M) :
    False := by
  obtain ⟨-, h81, h7⟩ := exists_centralizer_of_inner c.hKL c.hKb c.ha3 c.hb3 c.hab c.haL c.hbL
    c.hβ1 c.haK c.hout hT hαI hβI
  have hdvd : Nat.card ↥(innBar L ⊓ Subgroup.centralizer {rho L ⟨b, c.hbL⟩}) ∣ M := by
    refine ((Subgroup.card_dvd_of_le inf_le_left).trans ?_).trans hM
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange
      (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →*
        MulAut (L ⧸ aschbacherSolvableCore 3 L))).toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  rcases hM' with h | h
  · exact h (h81.trans hdvd)
  · exact h (h7.trans hdvd)

end CardCfg

section Model


theorem kF418ModelOn_of_card {P : ∀ (X : Type) [Group X], Prop}
    (hinner : ∀ (X : Type) [Group X] [Finite X], P X → ∀ σ : MulAut X, σ ^ 3 = 1 →
      σ ∈ (MulAut.conj : X →* MulAut X).range)
    (hcard : ∀ (X : Type) [Group X] [Finite X], P X →
      ∃ M : ℕ, Nat.card X ∣ M ∧ (¬ 3 ^ 4 ∣ M ∨ ¬ 7 ∣ M)) : KF418ModelOn P := by
  intro G _ _ L hL hl a b ha3 hb3 hab hb1 habz haN hbN hbC haC K hK n hn htype hKa
  exfalso
  have c := Cfg.of_model hK ha3 hb3 hab haN hbN hbC haC hKa
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  have hT := type418Arith_of hn hKq htype
  obtain ⟨M, hM, hM'⟩ := hcard _ hl
  exact c.false_of_card hT (hinner _ hl _ c.alpha_pow_three) (hinner _ hl _ c.beta_pow_three)
    hM hM'

end Model

theorem card_SL_galoisField (n p e : ℕ) [Fact p.Prime] [NeZero n] (he : e ≠ 0) :
    Nat.card (Matrix.SpecialLinearGroup (Fin n) (GaloisField p e)) =
      (∏ i : Fin n, ((p ^ e) ^ n - (p ^ e) ^ (i : ℕ))) / (p ^ e - 1) := by
  have : Fintype (GaloisField p e) := Fintype.ofFinite _
  rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, GaloisField.card p e he]

theorem card_projSU_three_three_dvd {e : ℕ} (he : 1 ≤ e) :
    Nat.card (projSU 3 3 e) ∣ (3 ^ e) ^ 3 * (((3 ^ e) ^ 2 - 1) * ((3 ^ e) ^ 3 + 1)) := by
  rw [← KFacts.KS14.card_projSU_three_mul_gcd 3 e he]
  exact Dvd.intro _ rfl

theorem not_dvd_projSL_five_two : ¬ 3 ^ 4 ∣ Nat.card (projSL 5 (GaloisField 2 1)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (projSL 5 (GaloisField 2 1)) :=
    Finite.of_equiv _ (Sec4.projSLEquivPSLn 5 (GaloisField 2 1)).symm.toEquiv
  intro h
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have h1 := h.trans (Sec4.card_projSL_dvd 5 (GaloisField 2 1))
  rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, GaloisField.card 2 1 (by norm_num)] at h1
  norm_num [Fin.prod_univ_succ] at h1

theorem not_dvd_projSL_three_three : ¬ 3 ^ 4 ∣ Nat.card (projSL 3 (GaloisField 3 1)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (projSL 3 (GaloisField 3 1)) :=
    Finite.of_equiv _ (Sec4.projSLEquivPSLn 3 (GaloisField 3 1)).symm.toEquiv
  intro h
  have : Fintype (GaloisField 3 1) := Fintype.ofFinite _
  have h1 := h.trans (Sec4.card_projSL_dvd 3 (GaloisField 3 1))
  rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, GaloisField.card 3 1 (by norm_num)] at h1
  norm_num [Fin.prod_univ_succ] at h1

theorem not_seven_dvd_projSL_four_three : ¬ 7 ∣ Nat.card (projSL 4 (GaloisField 3 1)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (projSL 4 (GaloisField 3 1)) :=
    Finite.of_equiv _ (Sec4.projSLEquivPSLn 4 (GaloisField 3 1)).symm.toEquiv
  intro h
  have : Fintype (GaloisField 3 1) := Fintype.ofFinite _
  have h1 := h.trans (Sec4.card_projSL_dvd 4 (GaloisField 3 1))
  rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, GaloisField.card 3 1 (by norm_num)] at h1
  norm_num [Fin.prod_univ_succ] at h1

theorem not_dvd_projSU_three_three : ¬ 3 ^ 4 ∣ Nat.card (projSU 3 3 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField 3 (2 * 1)) = 9 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  have hSU : Nat.card (CFSG.Assembly.LowTwoRank.StatedSU 3 (3 ^ 1) (GaloisField 3 (2 * 1))) =
      6048 := by simpa using CFSG.LinearGroups.UnitaryThreeOverNine.card_statedSU hK
  have : Finite (CFSG.Assembly.LowTwoRank.StatedSU 3 (3 ^ 1) (GaloisField 3 (2 * 1))) :=
    Nat.finite_of_card_ne_zero (by rw [hSU]; norm_num)
  have : Finite (projSU 3 3 1) :=
    Finite.of_equiv _ (Sec4.projSUEquivStatedProj 3 3 1).symm.toEquiv
  intro h
  have h1 := h.trans (Sec4.card_projSU_dvd 3 3 1)
  rw [hSU] at h1
  norm_num at h1

theorem not_dvd_projSU_five_four : ¬ 3 ^ 4 ∣ Nat.card (projSU 5 2 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := Sec4.unitaryFieldData_galoisField 2 2 (by norm_num)
  have hSU := CFSG.RankThree.PartTwo.Census.card_statedSU_five_four hU
  have : Finite (CFSG.Assembly.LowTwoRank.StatedSU 5 (2 ^ 2) (GaloisField 2 (2 * 2))) :=
    Nat.finite_of_card_ne_zero (by rw [hSU]; norm_num)
  have : Finite (projSU 5 2 2) :=
    Finite.of_equiv _ (Sec4.projSUEquivStatedProj 5 2 2).symm.toEquiv
  intro h
  have h1 := h.trans (Sec4.card_projSU_dvd 5 2 2)
  rw [hSU] at h1
  norm_num at h1

theorem not_seven_dvd_projSU_three_nine : ¬ 7 ∣ Nat.card (projSU 3 3 2) := by
  intro h
  have h1 := h.trans (card_projSU_three_three_dvd (e := 2) (by norm_num))
  norm_num at h1

@[expose] def IsSevenEightByOrders (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSL 5 (GaloisField 2 1)) ∨ Nonempty (X ≃* projSU 5 2 2) ∨
    Nonempty (X ≃* projSL 3 (GaloisField 3 1)) ∨ Nonempty (X ≃* projSU 3 3 1) ∨
    Nonempty (X ≃* projSU 3 3 2) ∨ Nonempty (X ≃* projSL 4 (GaloisField 3 1))

section Final


theorem kF418ModelOn_sevenEight : KF418ModelOn (fun X _ => IsSevenEightByOrders X) := by
  haveI h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine kF418ModelOn_of_card ?_ ?_
  · intro X _ _ hX σ hσ
    rcases hX with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · exact inner_projSL (n := 5) (p := 2) (f := 1)
        ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩ (by decide) (by decide) φ hσ
    · exact inner_projSU (n := 5) (p := 2) (f := 2)
        ⟨Nat.prime_two, by norm_num, by norm_num, by decide⟩ (by decide) (by decide) φ hσ
    · exact inner_projSL (n := 3) (p := 3) (f := 1)
        ⟨Nat.prime_three, le_rfl, by norm_num, by decide, by decide⟩ (by decide) (by decide) φ hσ
    · exact inner_projSU (n := 3) (p := 3) (f := 1)
        ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩ (by decide) (by decide) φ hσ
    · exact inner_projSU (n := 3) (p := 3) (f := 2)
        ⟨Nat.prime_three, by norm_num, by norm_num, by decide⟩ (by decide) (by decide) φ hσ
    · exact inner_projSL (n := 4) (p := 3) (f := 1)
        ⟨Nat.prime_three, le_rfl, by norm_num, by decide, by decide⟩ (by decide) (by decide) φ hσ
  · intro X _ _ hX
    rcases hX with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · exact ⟨_, dvd_of_eq (Nat.card_congr φ.toEquiv), Or.inl not_dvd_projSL_five_two⟩
    · exact ⟨_, dvd_of_eq (Nat.card_congr φ.toEquiv), Or.inl not_dvd_projSU_five_four⟩
    · exact ⟨_, dvd_of_eq (Nat.card_congr φ.toEquiv), Or.inl not_dvd_projSL_three_three⟩
    · exact ⟨_, dvd_of_eq (Nat.card_congr φ.toEquiv), Or.inl not_dvd_projSU_three_three⟩
    · exact ⟨_, dvd_of_eq (Nat.card_congr φ.toEquiv), Or.inr not_seven_dvd_projSU_three_nine⟩
    · exact ⟨_, dvd_of_eq (Nat.card_congr φ.toEquiv), Or.inr not_seven_dvd_projSL_four_three⟩

end Final

end CFSG.RankThree.PartTwo.Sec8.Hering418
