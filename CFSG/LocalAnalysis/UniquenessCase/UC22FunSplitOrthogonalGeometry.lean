module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitAmbient
public import CFSG.ClassicalInvolution.Generic.InductionLocal
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountTwo
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountTwoModel
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountAmbient
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountCommute
import CFSG.ClassicalInvolution.RouteD.MultiModelOrthLayer
import CFSG.ClassicalInvolution.Q3.Q3WAMOrth
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcModel
import CFSG.ClassicalInvolution.ModelFacts.E8D8AdjOrth
import CFSG.ClassicalInvolution.Uniform.U8Basic
import CFSG.ClassicalInvolution.Q3.Q3WASTLift
import CFSG.ClassicalInvolution.RouteD.TwinSmallWitt
public import CFSG.ClassicalInvolution.Asc77.AscIHSectG
public import CFSG.ClassicalInvolution.AschTight.S1911P3a
public import CFSG.ClassicalInvolution.AschTight.S1911P3b
public import CFSG.ClassicalInvolution.AschTight.S1911SecG
public import CFSG.ClassicalInvolution.AschTight.S1916FusStmt
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der69
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Prop67
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.HardMathSupport.Solomon.Coordinator.L3FATArith
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28b
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma58
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFrontier46
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39b
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLieFunFamily
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FunHypOmegaHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFunHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Defs
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.GoldschmidtRankOneUnitary
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.RankThree.SteinbergR3ELinearTwoOddFieldFixed
import CFSG.ClassicalInvolution.Uniform.U5Three2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp13
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aF
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UCR638

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.Blueprint CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.RouteD
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Frames

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem spanOrth_of_commutes_frame_and_twin (h2 : (2 : F) ≠ 0)
    {H A : OFrame Q} (hc : Commutes H.La.range A.La.range)
    (hc' : Commutes H.La.range A.swap.La.range) : SpanOrth H A := by
  rcases spanOrth_or_eq h2 hc with ho | heq
  · exact ho
  · rcases Frame.La_range_eq_or_eq_swap h2 heq.symm with he | he
    · rw [he] at hc
      exact (NonClassical.not_commutes_self_range A hc).elim
    · rw [he] at hc'
      exact (NonClassical.not_commutes_self_range A.swap hc').elim

theorem not_spanOrth_all_frames_of_dim_lt [FiniteDimensional F V]
    {m : ℕ} (A : Fin m → OFrame Q) (horth : ∀ i j, i ≠ j → SpanOrth (A i) (A j))
    (hdim : Module.finrank F V < 4 * (m + 1)) (H : OFrame Q) :
    ¬ ∀ i, SpanOrth H (A i) := by
  intro hH
  let U : Option (Fin m) → Submodule F V
    | none => H.span
    | some i => (A i).span
  have hnd : ∀ k, PolarNondegOn Q (U k) := by
    rintro (_ | i)
    · exact H.polarNondegOn_span
    · exact (A i).polarNondegOn_span
  have hor : ∀ k l, k ≠ l → ∀ x ∈ U k, ∀ y ∈ U l, polar Q x y = 0 := by
    rintro (_ | i) (_ | j) hne x hx y hy
    · exact (hne rfl).elim
    · exact (hH j).polar_zero hx hy
    · exact (hH i).symm.polar_zero hx hy
    · exact (horth i j (fun h => hne (congrArg some h))).polar_zero hx hy
  have hbound := CFSG.ClassicalInvolution.ModelFacts.E8D8.sum_finrank_le_of_orth U hnd hor
  have heq : (∑ k : Option (Fin m), Module.finrank F (U k)) = 4 * (m + 1) := by
    simp only [Fintype.sum_option, U, Frame.finrank_span, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  rw [heq] at hbound
  omega

theorem range_eq_of_commutes_other_twin_frames
    {ι : Type} (h2 : (2 : F) ≠ 0) (A : ι → OFrame Q)
    (hfull : ∀ H : OFrame Q, (∀ i, SpanOrth H (A i)) → False)
    (k : ι) {H : OFrame Q}
    (hc : Commutes H.La.range (A k).swap.La.range)
    (hcL : ∀ i, i ≠ k → Commutes H.La.range (A i).La.range)
    (hcR : ∀ i, i ≠ k → Commutes H.La.range (A i).swap.La.range) :
    H.La.range = (A k).La.range := by
  rcases spanOrth_or_eq h2 hc with ho | heq
  · exfalso
    apply hfull H
    intro i
    by_cases hik : i = k
    · subst i
      intro X Y
      have h := ho X (sigmaLin Y)
      rwa [Frame.incl_swap, sigmaLin_sigmaLin] at h
    · exact spanOrth_of_commutes_frame_and_twin h2 (hcL i hik) (hcR i hik)
  · rw [Frame.La_swap_neg_one] at heq
    rcases Frame.La_range_eq_or_eq_swap h2 heq.symm with h | h
    · exact h
    · rw [h] at hc
      exact (NonClassical.not_commutes_self_range (A k).swap hc).elim

theorem range_eq_of_commutes_other_paired_frames
    {ι : Type} (h2 : (2 : F) ≠ 0) (A : ι → OFrame Q)
    (hfull : ∀ H : OFrame Q, (∀ i, SpanOrth H (A i)) → False)
    (k : ι × Bool) {H : OFrame Q}
    (hc : ∀ j : ι × Bool, j ≠ k →
      Commutes H.La.range (if j.2 then (A j.1).swap.La.range else (A j.1).La.range)) :
    H.La.range = if k.2 then (A k.1).swap.La.range else (A k.1).La.range := by
  rcases k with ⟨k, b⟩
  cases b
  · exact range_eq_of_commutes_other_twin_frames h2 A hfull k
      (hc (k, true) (by simp))
      (fun i hi => hc (i, false) (fun h => hi (congrArg Prod.fst h)))
      (fun i hi => hc (i, true) (fun h => hi (congrArg Prod.fst h)))
  · have hswap : ∀ i, (A i).swap.swap = A i := by
      intro i
      cases A i with
      | mk P P' h => cases P'; rfl
    have hfull' : ∀ H : OFrame Q, (∀ i, SpanOrth H (A i).swap) → False := by
      intro H hH
      apply hfull H
      intro i X Y
      have h := hH i X (sigmaLin Y)
      rwa [Frame.incl_swap, sigmaLin_sigmaLin] at h
    apply range_eq_of_commutes_other_twin_frames h2 (fun i => (A i).swap) hfull' k
    · simpa [hswap] using hc (k, false) (by simp)
    · intro i hi
      simpa using hc (i, true) (fun h => hi (congrArg Prod.fst h))
    · intro i hi
      simpa [hswap] using hc (i, false) (fun h => hi (congrArg Prod.fst h))

theorem commutes_paired_frames {ι : Type} (A : ι → OFrame Q)
    (ho : ∀ i j, i ≠ j → SpanOrth (A i) (A j))
    {i j : ι × Bool} (hij : i ≠ j) :
    Commutes (if i.2 then (A i.1).swap.La.range else (A i.1).La.range)
      (if j.2 then (A j.1).swap.La.range else (A j.1).La.range) := by
  rcases i with ⟨i, bi⟩
  rcases j with ⟨j, bj⟩
  by_cases he : i = j
  · subst j
    cases bi <;> cases bj <;> simp_all
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact (A i).La_comm_La_swap a b
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact ((A i).La_comm_La_swap b a).symm
  · have hx := ho i j he
    cases bi <;> cases bj
    all_goals
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      apply Frame.La_comm_of_orth
      intro X Y
      simp only [Frame.incl_swap]
      exact hx _ _

private theorem frames_have_orthogonal_pairs {ι : Type} (A : ι → OFrame Q)
    (ho : ∀ i j, i ≠ j → SpanOrth (A i) (A j)) :
    ∀ i j : ι × Bool, i ≠ j →
      (if i.2 then (A i.1).P' else (A i.1).P).Orth
        (if j.2 then (A j.1).P' else (A j.1).P) := by
  rintro ⟨i, bi⟩ ⟨j, bj⟩ hij
  by_cases he : i = j
  · subst j
    cases bi <;> cases bj <;> simp_all
    · exact (A i).orth
    · exact (A i).orth.symm
  · obtain ⟨h00, h01, h10, h11⟩ := (ho i j he).orth_pairs
    cases bi <;> cases bj <;> simp_all

theorem not_spanOrth_all_frames_minus [Finite F]
    {n m : ℕ} {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hodd : Odd (Nat.card F)) (hn : 1 ≤ n) (hsize : n ≤ 2 * (m + 1))
    (A : Fin m → OFrame (quadMinus n F b c))
    (ho : ∀ i j, i ≠ j → SpanOrth (A i) (A j))
    (H : OFrame (quadMinus n F b c)) : ¬ ∀ i, SpanOrth H (A i) := by
  intro hH
  let B : Option (Fin m) → OFrame (quadMinus n F b c)
    | none => H
    | some i => A i
  have hB : ∀ i j, i ≠ j → SpanOrth (B i) (B j) := by
    rintro (_ | i) (_ | j) hne
    · exact (hne rfl).elim
    · exact hH j
    · exact (hH i).symm
    · exact ho i j (fun h => hne (congrArg some h))
  obtain ⟨η⟩ : Nonempty (Fin n ↪ Option (Fin m) × Bool) :=
    Function.Embedding.nonempty_of_card_le (by simpa [Nat.mul_comm] using hsize)
  let P : Fin n → HypPair (quadMinus n F b c) :=
    fun i => if (η i).2 then (B (η i).1).P' else (B (η i).1).P
  exact TwinSmall.false_of_pairs_minus hirr hodd hn P
    (fun i j hij => frames_have_orthogonal_pairs B hB _ _ (η.injective.ne hij))

@[expose] noncomputable def oddOrthogonalPairFrame (F : Type) [Field F] (n : ℕ)
    (k : Fin (n / 2)) : OFrame (quadOdd n F) :=
  (oddFrame n F).toHypFrame.toFrame
    (i := ⟨2 * k.val, by omega⟩) (j := ⟨2 * k.val + 1, by omega⟩)
    (Fin.ne_of_val_ne (by simp)) true false

theorem spanOrth_oddOrthogonalPairFrame (F : Type) [Field F] (n : ℕ)
    {i j : Fin (n / 2)} (hij : i ≠ j) :
    SpanOrth (oddOrthogonalPairFrame F n i) (oddOrthogonalPairFrame F n j) := by
  have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
  intro X Y
  exact CFSG.ClassicalInvolution.Balance.Bootstrap.polar_incl_toFrame_of_disjoint
    (oddFrame n F).toHypFrame _ _
    (Fin.ne_of_val_ne (by simpa using hv)) (Fin.ne_of_val_ne (by dsimp; omega))
    (Fin.ne_of_val_ne (by dsimp; omega)) (Fin.ne_of_val_ne (by dsimp; omega))
    true false true false X Y

theorem not_spanOrth_all_oddOrthogonalPairFrame (F : Type) [Field F] (n : ℕ)
    (H : OFrame (quadOdd n F)) :
    ¬ ∀ i, SpanOrth H (oddOrthogonalPairFrame F n i) := by
  apply not_spanOrth_all_frames_of_dim_lt (oddOrthogonalPairFrame F n)
    (fun i j hij => spanOrth_oddOrthogonalPairFrame F n hij)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
    Fintype.card_fin, Fintype.card_unit]
  omega

@[expose] noncomputable def plusOrthogonalPairFrame (F : Type) [Field F] (n : ℕ)
    (hn : 3 ≤ n) (k : Fin (n / 2)) : OFrame (quadPlus n F) :=
  (plusFrame n F hn).toFrame
    (i := ⟨2 * k.val, by omega⟩) (j := ⟨2 * k.val + 1, by omega⟩)
    (Fin.ne_of_val_ne (by simp)) true false

theorem spanOrth_plusOrthogonalPairFrame (F : Type) [Field F] (n : ℕ) (hn : 3 ≤ n)
    {i j : Fin (n / 2)} (hij : i ≠ j) :
    SpanOrth (plusOrthogonalPairFrame F n hn i) (plusOrthogonalPairFrame F n hn j) := by
  have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
  intro X Y
  exact CFSG.ClassicalInvolution.Balance.Bootstrap.polar_incl_toFrame_of_disjoint
    (plusFrame n F hn) _ _
    (Fin.ne_of_val_ne (by simpa using hv)) (Fin.ne_of_val_ne (by dsimp; omega))
    (Fin.ne_of_val_ne (by dsimp; omega)) (Fin.ne_of_val_ne (by dsimp; omega))
    true false true false X Y

theorem not_spanOrth_all_plusOrthogonalPairFrame (F : Type) [Field F] (n : ℕ) (hn : 3 ≤ n)
    (H : OFrame (quadPlus n F)) : ¬ ∀ i, SpanOrth H (plusOrthogonalPairFrame F n hn i) := by
  apply not_spanOrth_all_frames_of_dim_lt (plusOrthogonalPairFrame F n hn)
    (fun i j hij => spanOrth_plusOrthogonalPairFrame F n hn hij)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  omega

@[expose] noncomputable def minusOrthogonalPairFrame (F : Type) [Field F] (n : ℕ) (b c : F)
    (k : Fin ((n - 1) / 2)) : OFrame (quadMinus n F b c) :=
  (Twisted.minusFrame n b c).toHypFrame.toFrame
    (i := ⟨2 * k.val, by omega⟩) (j := ⟨2 * k.val + 1, by omega⟩)
    (Fin.ne_of_val_ne (by simp)) true false

theorem spanOrth_minusOrthogonalPairFrame (F : Type) [Field F] (n : ℕ) (b c : F)
    {i j : Fin ((n - 1) / 2)} (hij : i ≠ j) :
    SpanOrth (minusOrthogonalPairFrame F n b c i) (minusOrthogonalPairFrame F n b c j) := by
  have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
  intro X Y
  exact CFSG.ClassicalInvolution.Balance.Bootstrap.polar_incl_toFrame_of_disjoint
    (Twisted.minusFrame n b c).toHypFrame _ _
    (Fin.ne_of_val_ne (by simpa using hv)) (Fin.ne_of_val_ne (by dsimp; omega))
    (Fin.ne_of_val_ne (by dsimp; omega)) (Fin.ne_of_val_ne (by dsimp; omega))
    true false true false X Y

theorem not_spanOrth_all_minusOrthogonalPairFrame (F : Type) [Field F] [Finite F]
    (n : ℕ) (hn : 1 ≤ n) {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hodd : Odd (Nat.card F)) (H : OFrame (quadMinus n F b c)) :
    ¬ ∀ i, SpanOrth H (minusOrthogonalPairFrame F n b c i) := by
  exact not_spanOrth_all_frames_minus hirr hodd hn (by omega)
    (minusOrthogonalPairFrame F n b c)
    (fun i j hij => spanOrth_minusOrthogonalPairFrame F n b c hij) H

end Frames
theorem exists_paired_frame_modelFund_pOmegaOdd
    {p n e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaOdd n p e) :
    ∃ R : Fin (n / 2) × Bool → Subgroup (spinGroup (quadOdd n (GaloisField p e))),
      ∀ k, R k ∈ fundamentalSubgroups .POmegaOdd (oddDatum n (GaloisField p e)) ∧
        (R k).map (spinAction (quadOdd n (GaloisField p e))) =
          if k.2 then (oddOrthogonalPairFrame (GaloisField p e) n k.1).swap.La.range
          else (oddOrthogonalPairFrame (GaloisField p e) n k.1).La.range := by
  classical
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hodd : Odd (Nat.card (GaloisField p e)) :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.odd_natCard_galoisField hp2 hadm.2.1
  have hex : ∀ k : Fin (n / 2) × Bool,
      ∃ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum n (GaloisField p e)),
        R.map (spinAction (quadOdd n (GaloisField p e))) =
          if k.2 then (oddOrthogonalPairFrame (GaloisField p e) n k.1).swap.La.range
          else (oddOrthogonalPairFrame (GaloisField p e) n k.1).La.range := by
    intro k
    apply Gaps.exists_map_eq_odd hn3 hodd
    cases k.2
    · exact ⟨_, IsFundamental.of_frame _⟩
    · exact ⟨_, IsFundamental.of_frame_swap _⟩
  choose R hR hmap using hex
  exact ⟨R, fun k => ⟨hR k, hmap k⟩⟩


theorem eq_of_commutes_small_orthogonal_modelFund
    {p : ℕ} [Fact p.Prime] {t : StatedLieTag} {n e : ℕ}
    (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p e)
    (ht : (t = .POmegaOdd ∧ n = 3) ∨ (t = .POmegaMinus ∧ n = 4))
    {R A B : Subgroup (modelUniv t n p e Fact.out).K}
    (hR : R ∈ ModelFund p t n e) (hA : A ∈ ModelFund p t n e)
    (hB : B ∈ ModelFund p t n e) (cRA : Commutes R A) (cRB : Commutes R B) :
    A = B := by
  have hfund : IsFundTag t := by
    rcases ht with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> trivial
  have htwo : FunTwoType t n := by
    rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [FunTwoType]
  have hnc : ¬ Commutes R R := by
    intro hc
    rcases CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups
        hp2 hfund hadm hR with ⟨⟨eR⟩⟩ | ⟨_, ⟨eR⟩⟩
    all_goals
      obtain ⟨a, ha, b, hb, hab⟩ := F14.exists_noncommuting_map_of_equiv_sl2
        (MonoidHom.id _) (by simp) eR
      exact hab (hc a ha b hb)
  have hgeo : A = B ∨ Commutes A B := by
    by_cases hq : 5 ≤ p ^ e
    · rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact modelLayer_pOmegaOdd hp2 hq R hR A hA B hB cRA cRB
      · exact modelLayer_pOmegaMinus hp2 hq hadm R hR A hA B hB cRA cRB
    · obtain ⟨rfl, rfl⟩ := Nat.prime_three.pow_eq_iff.mp
        ((CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.eq_three_or_five_le_of_odd_prime_pow
          Fact.out hp2 hadm.2.1).resolve_right hq)
      rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact CFSG.ClassicalInvolution.Q3.Q3W.modelLayer_pOmegaOdd3
          R hR A hA B hB cRA cRB
      · exact CFSG.ClassicalInvolution.Q3.Q3W.modelLayer_pOmegaMinus3
          R hR A hA B hB cRA cRB
  rcases hgeo with h | cAB
  · exact h
  · by_contra hAB
    have hRA : R ≠ A := fun h => hnc (h ▸ cRA)
    have hRB : R ≠ B := fun h => hnc (h ▸ cRB)
    exact no_three_commuting_modelFund_of_funTwo hp2 hadm htwo
      hR hA hB hRA hRB hAB cRA cRB cAB


theorem eq_modelFund_of_map_eq {p n e : ℕ} [hp : Fact p.Prime]
    {t : StatedLieTag} (hp2 : p ≠ 2) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) {X : Type} [Group X]
    (φ : (modelUniv t n p e hp.out).K →* X)
    (hker : φ.ker ≤ center (modelUniv t n p e hp.out).K)
    {R S : Subgroup (modelUniv t n p e hp.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D)
    (hS : S ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D)
    (he : R.map φ = S.map φ) : R = S := by
  by_cases hq : 5 ≤ p ^ e
  · have perf : ∀ T ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D, ⁅T, T⁆ = T := by
      intro T hT
      refine le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => ?_)
        (CFSG.ClassicalInvolution.ModelFacts.fundPerfect_core t n p e hp2 hfund hadm (by omega) T hT)
      exact T.mul_mem (T.mul_mem (T.mul_mem ha hb) (T.inv_mem ha)) (T.inv_mem hb)
    exact CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect φ hker
      (perf R hR) (perf S hS) he
  · obtain ⟨rfl, rfl⟩ := Nat.prime_three.pow_eq_iff.mp
      ((CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.eq_three_or_five_le_of_odd_prime_pow
        hp.out hp2 hadm.2.1).resolve_right hq)
    have : Finite (modelUniv t n 3 1 hp.out).K :=
      CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hp2 hp.out hfund hadm
    have hcop := CFSG.ClassicalInvolution.Q3.Q3W.ker_not_dvd_three_model hfund hadm φ hker
    have hk3 : ∀ x ∈ φ.ker, x ^ 3 = 1 → x = 1 := by
      intro x hx hx3
      have hord : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
      rcases (Nat.dvd_prime Nat.prime_three).mp hord with h | h
      · exact orderOf_eq_one_iff.mp h
      · exact (hcop x hx (by rw [h])).elim
    have gen : ∀ T ∈ fundamentalSubgroups t (modelUniv t n 3 1 hp.out).D,
        CFSG.ClassicalInvolution.ModelFacts.Gen3 T := by
      intro T hT
      rcases CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups
          hp2 hfund hadm hT with ⟨⟨eT⟩⟩ | ⟨_, ⟨eT⟩⟩
      · exact CFSG.ClassicalInvolution.ModelFacts.gen3_of_equiv_sl2 eT
      · exact CFSG.ClassicalInvolution.ModelFacts.gen3_of_equiv_sl2 eT
    exact CFSG.ClassicalInvolution.Uniform.eq_of_map_eq_of_gen3 φ hker hk3
      (gen R hR) (gen S hS) he

section PairedModels

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
  {p n e m : ℕ} [hp : Fact p.Prime] {t : StatedLieTag}

theorem exists_full_paired_model_frame_funSet
    (hp2 : p ≠ 2) (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (hX : LieModel X t n p e) (hA1 : ¬ (t = .PSL ∧ n = 2)) (hm : 0 < m)
    (π : (modelUniv t n p e hp.out).K →* (V ≃ₗ[F] V))
    (hπker : π.ker ≤ center (modelUniv t n p e hp.out).K)
    (hπmap : ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D,
      ∃ H : OFrame Q, R.map π = H.La.range)
    (A : Fin m → OFrame Q) (horth : ∀ i j, i ≠ j → SpanOrth (A i) (A j))
    (hfull : ∀ H : OFrame Q, (∀ i, SpanOrth H (A i)) → False)
    (R : Fin m × Bool → Subgroup (modelUniv t n p e hp.out).K)
    (hR : ∀ k, R k ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D ∧
      (R k).map π = if k.2 then (A k.1).swap.La.range else (A k.1).La.range)
    (h2 : (2 : F) ≠ 0)
    (ψ : (modelUniv t n p e hp.out).K →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ center (modelUniv t n p e hp.out).K) (P : Sylow 2 X) :
    ∃ c : X, F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X) =
      Set.range (fun k => (R k).map ((MulAut.conj c).toMonoidHom.comp ψ)) := by
  have hA : ∀ k, IsFundamentalOver (p ^ e) ((R k).map ψ) := fun k =>
    ⟨t, n, p, e, hp.out, hp2, rfl, hfund, hadm, ψ, hψ, hker, R k, (hR k).1, rfl⟩
  obtain ⟨hZ, _, hL2, _⟩ := fundamental_ambient_of_lieModel hp.out hp2 hadm hX hA1
    (hA (⟨0, hm⟩, false))
  have hcModel : ∀ i j, i ≠ j → Commutes (R i) (R j) := by
    intro i j hij
    apply commutes_modelFund_of_commutes_map hp2 hfund hadm π hπker (hR i).1
    rw [(hR i).2, (hR j).2]
    exact commutes_paired_frames A horth hij
  have hcψ : ∀ i j, i ≠ j → Commutes ((R i).map ψ) ((R j).map ψ) :=
    fun i j hij => CFSG.ClassicalInvolution.RouteD.commutes_map ψ (hcModel i j hij)
  have hnorm : ∀ i j, (R j).map ψ ≤ normalizer ((R i).map ψ : Set X) := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
      exact Subgroup.le_normalizer
    · have hcent : (R j).map ψ ≤ centralizer ((R i).map ψ : Set X) :=
        fun a ha => Subgroup.mem_centralizer_iff.mpr (fun b hb => hcψ i j hij b hb a ha)
      exact hcent.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨c, hc⟩ := F14.exists_conj_family_mem_funSet (𝔉 := fundPred (p ^ e))
    (fun g _ h => isFundamentalOver_map_mulEquiv (MulAut.conj g) h)
    (fun k => (R k).map ψ) hA hnorm P
  let ψc := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ center (modelUniv t n p e hp.out).K := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hx)
  have hc' : ∀ k, (R k).map ψc ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X) := by
    intro k
    simpa only [ψc, Subgroup.map_map] using hc k
  have hdesc : ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n p f ∧
      p ^ e = p ^ f ∧ LieModel (X ⧸ center X) t n p f :=
    ⟨t, n, e, hadm, rfl, hX.quotient_center hZ⟩
  refine ⟨c, ?_⟩
  ext L
  constructor
  · intro hL
    by_contra hnot
    have hne : ∀ k, L ≠ (R k).map ψc := fun k h => hnot ⟨k, h.symm⟩
    obtain ⟨RL, hRL, hLR, _⟩ := exists_mem_fundamentalSubgroups_of_isFundamentalOver_general
      hp.out hp2 hadm hX hfund hA1 hL2 ψc hψc hkerC hL.1
    obtain ⟨H, hH⟩ := hπmap RL hRL
    have hcRL : ∀ k, Commutes (RL.map π) ((R k).map π) := by
      intro k
      apply CFSG.ClassicalInvolution.RouteD.commutes_map
      apply commutes_modelFund_of_commutes_map hp2 hfund hadm ψc hkerC hRL
      rw [← hLR]
      have hh := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.funSet_commute_of_lieModel
        hp.out hp2 hdesc hL2 P hL (hc' k) (hne k)
      exact fun a ha b hb => (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hh ha) b hb).symm
    apply hfull H
    intro j
    apply spanOrth_of_commutes_frame_and_twin h2
    · have hmap : (R (j, false)).map π = (A j).La.range := by simpa using (hR (j, false)).2
      simpa only [hH, hmap] using hcRL (j, false)
    · have hmap : (R (j, true)).map π = (A j).swap.La.range := by simpa using (hR (j, true)).2
      simpa only [hH, hmap] using hcRL (j, true)
  · rintro ⟨k, rfl⟩
    exact hc' k

private theorem centralizingLayer_funSet_eq_of_paired_model_frame
    (hp2 : p ≠ 2) (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (hX : LieModel X t n p e) (hA1 : ¬ (t = .PSL ∧ n = 2)) (hm : 0 < m)
    (π : (modelUniv t n p e hp.out).K →* (V ≃ₗ[F] V))
    (hπker : π.ker ≤ center (modelUniv t n p e hp.out).K)
    (hπmap : ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D,
      ∃ H : OFrame Q, R.map π = H.La.range)
    (A : Fin m → OFrame Q) (horth : ∀ i j, i ≠ j → SpanOrth (A i) (A j))
    (hfull : ∀ H : OFrame Q, (∀ i, SpanOrth H (A i)) → False)
    (R : Fin m × Bool → Subgroup (modelUniv t n p e hp.out).K)
    (hR : ∀ k, R k ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D ∧
      (R k).map π = if k.2 then (A k.1).swap.La.range else (A k.1).La.range)
    (h2 : (2 : F) ≠ 0) (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    centralizingLayer {L : Subgroup X | IsFundamentalOver (p ^ e) L}
      {x : X | ∃ L ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X),
        L ≠ K ∧ x ∈ L} = K := by
  obtain ⟨ψ, hψ, hker⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    t n p e hp.out hp2 hfund hadm X hX
  obtain ⟨c, hfull'⟩ := exists_full_paired_model_frame_funSet hp2 hfund hadm hX hA1 hm
    π hπker hπmap A horth hfull R hR h2 ψ hψ hker P
  let ψc := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ center (modelUniv t n p e hp.out).K := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hx)
  have hk : K ∈ Set.range (fun k => (R k).map ψc) := hfull' ▸ hK
  obtain ⟨k, hKmap⟩ := hk
  change (R k).map ψc = K at hKmap
  obtain ⟨hZ, _, hL2, _⟩ := fundamental_ambient_of_lieModel hp.out hp2 hadm hX hA1 hK.1
  have hdesc : ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n p f ∧
      p ^ e = p ^ f ∧ LieModel (X ⧸ center X) t n p f :=
    ⟨t, n, e, hadm, rfl, hX.quotient_center hZ⟩
  have hcR : ∀ i j, i ≠ j → Commutes (R i) (R j) := by
    intro i j hij
    apply commutes_modelFund_of_commutes_map hp2 hfund hadm π hπker (hR i).1
    rw [(hR i).2, (hR j).2]
    exact commutes_paired_frames A horth hij
  have hinj : Function.Injective (fun j => (R j).map ψc) := by
    intro i j heq
    by_contra hij
    rcases CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups
        hp2 hfund hadm (hR i).1 with ⟨⟨eR⟩⟩ | ⟨_, ⟨eR⟩⟩
    all_goals exact F14.map_ne_of_commuting_of_equiv_sl2 ψc hkerC eR (hcR i j hij) heq
  apply le_antisymm
  · refine iSup₂_le fun L hL => ?_
    obtain ⟨RL, hRL, hLR, _⟩ := exists_mem_fundamentalSubgroups_of_isFundamentalOver_general
      hp.out hp2 hadm hX hfund hA1 hL2 ψc hψc hkerC hL.1
    obtain ⟨H, hH⟩ := hπmap RL hRL
    have hcomm : ∀ j : Fin m × Bool, j ≠ k →
        Commutes H.La.range (if j.2 then (A j.1).swap.La.range else (A j.1).La.range) := by
      intro j hj
      have hne : (R j).map ψc ≠ K := fun h => hj (hinj (h.trans hKmap.symm))
      have hcL : Commutes (RL.map ψc) ((R j).map ψc) := by
        rw [← hLR]
        intro a ha b hb
        exact (Subgroup.mem_centralizer_iff.mp (hL.2 ha) b
          ⟨(R j).map ψc, hfull'.symm ▸ ⟨j, rfl⟩, hne, hb⟩).symm
      have hc := CFSG.ClassicalInvolution.RouteD.commutes_map π
        (commutes_modelFund_of_commutes_map hp2 hfund hadm ψc hkerC hRL hcL)
      simpa only [hH, (hR j).2] using hc
    have hEq : RL.map π = (R k).map π := by
      rw [hH, (hR k).2]
      exact range_eq_of_commutes_other_paired_frames h2 A hfull k hcomm
    have hEq' := eq_modelFund_of_map_eq hp2 hfund hadm π hπker hRL (hR k).1 hEq
    rw [hLR, hEq', hKmap]
  · refine le_centralizingLayer ⟨hK.1, ?_⟩
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    rintro b ⟨L, hL, hLK, hb⟩
    have hc := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.funSet_commute_of_lieModel
      hp.out hp2 hdesc hL2 P hL hK hLK
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc hb) a ha).symm

end PairedModels

theorem plus_model_data {p n e : ℕ} [hp : Fact p.Prime] (hn : 3 ≤ n) :
    ∃ η : (modelUniv .POmegaPlus n p e hp.out).K ≃* spinGroup (quadPlus n (GaloisField p e)),
      ∀ R : Subgroup (modelUniv .POmegaPlus n p e hp.out).K,
        R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n p e hp.out).D ↔
        R.map η.toMonoidHom ∈ fundamentalSubgroups .POmegaPlus (plusDatum n (GaloisField p e) hn) := by
  have h : modelUniv .POmegaPlus n p e hp.out =
      ⟨spinGroup (quadPlus n (GaloisField p e)), plusDatum n (GaloisField p e) hn⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus hn
  generalize modelUniv .POmegaPlus n p e hp.out = M at h ⊢
  subst h
  exact ⟨MulEquiv.refl _, fun R => by simp⟩

theorem centralizingLayer_funSet_eq_of_pOmegaPlus
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p n e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaPlus n p e) (hX : LieModel X .POmegaPlus n p e)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    centralizingLayer {L : Subgroup X | IsFundamentalOver (p ^ e) L}
      {x : X | ∃ L ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X),
        L ≠ K ∧ x ∈ L} = K := by
  classical
  let F := GaloisField p e
  let Q := quadPlus n F
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  have hodd : Odd (Nat.card F) :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.odd_natCard_galoisField hp2 hadm.2.1
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  obtain ⟨η, hη⟩ := plus_model_data (p := p) (e := e) hn3
  let π := (spinAction Q).comp η.toMonoidHom
  have hπker : π.ker ≤ center (modelUniv .POmegaPlus n p e hp.out).K := by
    intro x hx
    have hy : η x ∈ center (spinGroup Q) :=
      ker_spinAction_le_center Q (by simpa only [MonoidHom.mem_ker, π, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom] using hx)
    rw [Subgroup.mem_center_iff] at hy ⊢
    intro y
    apply η.injective
    simpa only [map_mul] using hy (η y)
  have hsc : FundamentalSingleClass .POmegaPlus (plusDatum n F hn3) := by
    have hm := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaPlus n p e
      hp.out trivial hadm (by decide) (by decide)
    have he := CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus (p := p) (f := e) hn3
    change FundamentalSingleClass .POmegaPlus
      (CFSG.ClassicalInvolution.ModelFacts.modelUniv .POmegaPlus n p e hp.out).D at hm
    rw [he] at hm
    exact hm
  have hπmap : ∀ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n p e hp.out).D,
      ∃ H : OFrame Q, R.map π = H.La.range := by
    intro R hR
    have hR' := (hη R).mp hR
    obtain ⟨i, H, hH, _⟩ := Gaps.map_mem_fundSet hn3 hsc hR'
    exact ⟨H, by simpa only [π, Subgroup.map_map] using hH⟩
  let A := plusOrthogonalPairFrame F n hn3
  have hex : ∀ k : Fin (n / 2) × Bool,
      ∃ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n p e hp.out).D,
        R.map π = if k.2 then (A k.1).swap.La.range else (A k.1).La.range := by
    intro k
    have hg : (if k.2 then (A k.1).swap.La.range else (A k.1).La.range) ∈ Gaps.fundSet Q := by
      cases k.2
      · exact ⟨_, IsFundamental.of_frame _⟩
      · exact ⟨_, IsFundamental.of_frame_swap _⟩
    obtain ⟨S, hS, hmap⟩ := Gaps.exists_map_eq hn3 hodd hg
    let R := S.map η.symm.toMonoidHom
    have hRmap : R.map η.toMonoidHom = S := by
      simp [R, Subgroup.map_map]
    refine ⟨R, (hη R).mpr (hRmap.symm ▸ hS), ?_⟩
    change R.map ((spinAction Q).comp η.toMonoidHom) = _
    rw [← Subgroup.map_map, hRmap]
    exact hmap
  choose R hR hmap using hex
  exact centralizingLayer_funSet_eq_of_paired_model_frame hp2 (by trivial) hadm hX
    (by simp) (by omega : 0 < n / 2) π hπker hπmap A
    (fun i j hij => spanOrth_plusOrthogonalPairFrame F n hn3 hij)
    (fun H h => not_spanOrth_all_plusOrthogonalPairFrame F n hn3 H h)
    R (fun k => ⟨hR k, hmap k⟩) h2 P hK

theorem centralizingLayer_funSet_eq_of_pOmegaMinus
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p n e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaMinus n p e) (hX : LieModel X .POmegaMinus n p e)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    centralizingLayer {L : Subgroup X | IsFundamentalOver (p ^ e) L}
      {x : X | ∃ L ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X),
        L ≠ K ∧ x ∈ L} = K := by
  classical
  let F := GaloisField p e
  let b := (CFSG.LieType.Universal.minusCoeffs p e).1
  let c := (CFSG.LieType.Universal.minusCoeffs p e).2
  let Q := quadMinus n F b c
  let π : (modelUniv .POmegaMinus n p e hp.out).K →* (_ ≃ₗ[F] _) := spinAction Q
  have hπker : π.ker ≤ center (modelUniv .POmegaMinus n p e hp.out).K := ker_spinAction_le_center Q
  have hn4 : 4 ≤ n := hadm.2.2
  have hodd : Odd (Nat.card F) :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.odd_natCard_galoisField hp2 hadm.2.1
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hcorr :
      (∀ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n p e hp.out).D,
        R.map π ∈ Gaps.fundSet Q) ∧
      ∀ L ∈ Gaps.fundSet Q,
        ∃ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n p e hp.out).D,
          R.map π = L := by
    by_cases hq : 5 ≤ p ^ e
    · exact Exotic.fundCorr_minus hp2 hq hadm
    · have hq3 := (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.eq_three_or_five_le_of_odd_prime_pow
        hp.out hp2 hadm.2.1).resolve_right hq
      exact Exotic.fundCorr_minus3 hq3 hadm
  have hπmap : ∀ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n p e hp.out).D,
      ∃ H : OFrame Q, R.map π = H.La.range := by
    intro R hR
    obtain ⟨i, H, hH, _⟩ := hcorr.1 R hR
    exact ⟨H, hH⟩
  let A := minusOrthogonalPairFrame F n b c
  have hex : ∀ k : Fin ((n - 1) / 2) × Bool,
      ∃ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n p e hp.out).D,
        R.map π = if k.2 then (A k.1).swap.La.range else (A k.1).La.range := by
    intro k
    apply hcorr.2
    cases k.2
    · exact ⟨_, IsFundamental.of_frame _⟩
    · exact ⟨_, IsFundamental.of_frame_swap _⟩
  choose R hR hmap using hex
  exact centralizingLayer_funSet_eq_of_paired_model_frame hp2 (by trivial) hadm hX
    (by simp) (by omega : 0 < (n - 1) / 2) π hπker hπmap A
    (fun i j hij => spanOrth_minusOrthogonalPairFrame F n b c hij)
    (fun H h => not_spanOrth_all_minusOrthogonalPairFrame F n (by omega)
      (CFSG.LieType.Universal.minusCoeffs_irr p e) hodd H h)
    R (fun k => ⟨hR k, hmap k⟩) h2 P hK

theorem exists_full_paired_frame_funSet_pOmegaOdd
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p n e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaOdd n p e) (hX : LieModel X .POmegaOdd n p e)
    (ψ : spinGroup (quadOdd n (GaloisField p e)) →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ center (spinGroup (quadOdd n (GaloisField p e)))) (P : Sylow 2 X) :
    ∃ (R : Fin (n / 2) × Bool → Subgroup (spinGroup (quadOdd n (GaloisField p e)))) (c : X),
      (∀ k, R k ∈ fundamentalSubgroups .POmegaOdd (oddDatum n (GaloisField p e)) ∧
        (R k).map (spinAction (quadOdd n (GaloisField p e))) =
          if k.2 then (oddOrthogonalPairFrame (GaloisField p e) n k.1).swap.La.range
          else (oddOrthogonalPairFrame (GaloisField p e) n k.1).La.range) ∧
      F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X) =
        Set.range (fun k => (R k).map ((MulAut.conj c).toMonoidHom.comp ψ)) := by
  let F := GaloisField p e
  let Q := quadOdd n F
  let π : (modelUniv .POmegaOdd n p e hp.out).K →* (_ ≃ₗ[F] _) := spinAction Q
  have hn3 : 3 ≤ n := hadm.2.2.1
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hsc : FundamentalSingleClass .POmegaOdd (oddDatum n F) :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaOdd n p e
      hp.out trivial hadm (by decide) (by decide)
  have hπmap : ∀ R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n p e hp.out).D,
      ∃ H : OFrame Q, R.map π = H.La.range := by
    intro R hR
    obtain ⟨i, H, hH, _⟩ := Gaps.map_mem_fundSet_odd hn3 hsc hR
    exact ⟨H, hH⟩
  obtain ⟨R₀, hR₀⟩ := exists_paired_frame_modelFund_pOmegaOdd hp2 hadm
  let R : Fin (n / 2) × Bool → Subgroup (modelUniv .POmegaOdd n p e hp.out).K := R₀
  have hR : ∀ k, R k ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n p e hp.out).D ∧
      (R k).map π = if k.2 then (oddOrthogonalPairFrame F n k.1).swap.La.range
        else (oddOrthogonalPairFrame F n k.1).La.range := hR₀
  obtain ⟨c, hfull⟩ := exists_full_paired_model_frame_funSet hp2 (by trivial) hadm hX
    (by simp) (by omega : 0 < n / 2) π (ker_spinAction_le_center Q) hπmap
    (oddOrthogonalPairFrame F n) (fun i j hij => spanOrth_oddOrthogonalPairFrame F n hij)
    (fun H h => not_spanOrth_all_oddOrthogonalPairFrame F n H h) R hR h2 ψ hψ hker P
  exact ⟨R₀, c, hR₀, hfull⟩

theorem centralizingLayer_funSet_eq_of_pOmegaOdd
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p n e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaOdd n p e) (hX : LieModel X .POmegaOdd n p e)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    centralizingLayer {L : Subgroup X | IsFundamentalOver (p ^ e) L}
      {x : X | ∃ L ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X),
        L ≠ K ∧ x ∈ L} = K := by
  let F := GaloisField p e
  let Q := quadOdd n F
  let π : (modelUniv .POmegaOdd n p e hp.out).K →* (_ ≃ₗ[F] _) := spinAction Q
  have hn3 : 3 ≤ n := hadm.2.2.1
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hsc : FundamentalSingleClass .POmegaOdd (oddDatum n F) :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaOdd n p e
      hp.out trivial hadm (by decide) (by decide)
  have hπmap : ∀ R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n p e hp.out).D,
      ∃ H : OFrame Q, R.map π = H.La.range := by
    intro R hR
    obtain ⟨i, H, hH, _⟩ := Gaps.map_mem_fundSet_odd hn3 hsc hR
    exact ⟨H, hH⟩
  obtain ⟨R₀, hR₀⟩ := exists_paired_frame_modelFund_pOmegaOdd hp2 hadm
  let R : Fin (n / 2) × Bool → Subgroup (modelUniv .POmegaOdd n p e hp.out).K := R₀
  have hR : ∀ k, R k ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n p e hp.out).D ∧
      (R k).map π = if k.2 then (oddOrthogonalPairFrame F n k.1).swap.La.range
        else (oddOrthogonalPairFrame F n k.1).La.range := hR₀
  exact centralizingLayer_funSet_eq_of_paired_model_frame hp2 (by trivial) hadm hX
    (by simp) (by omega : 0 < n / 2) π (ker_spinAction_le_center Q) hπmap
    (oddOrthogonalPairFrame F n) (fun i j hij => spanOrth_oddOrthogonalPairFrame F n hij)
    (fun H h => not_spanOrth_all_oddOrthogonalPairFrame F n H h) R hR h2 P hK

theorem centralizingLayer_funSet_eq_of_orthogonal
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hadm : StatedLieAdmissible t n p e) (hX : LieModel X t n p e)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    centralizingLayer {L : Subgroup X | IsFundamentalOver (p ^ e) L}
      {x : X | ∃ L ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X),
        L ≠ K ∧ x ∈ L} = K := by
  rcases ht with rfl | rfl | rfl
  · exact centralizingLayer_funSet_eq_of_pOmegaOdd hp2 hadm hX P hK
  · exact centralizingLayer_funSet_eq_of_pOmegaPlus hp2 hadm hX P hK
  · exact centralizingLayer_funSet_eq_of_pOmegaMinus hp2 hadm hX P hK

theorem centralizingLayer_funSet_eq_of_small_orthogonal
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p e) (hX : LieModel X t n p e)
    (ht : (t = .POmegaOdd ∧ n = 3) ∨ (t = .POmegaMinus ∧ n = 4))
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    centralizingLayer {L : Subgroup X | IsFundamentalOver (p ^ e) L}
      {x : X | ∃ L ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X),
        L ≠ K ∧ x ∈ L} = K := by
  have hfund : IsFundTag t := by
    rcases ht with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> trivial
  have htwo : FunTwoType t n := by
    rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [FunTwoType]
  have hA1 : ¬ (t = .PSL ∧ n = 2) := by
    rcases ht with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
  obtain ⟨hZ, _, hL2, _⟩ := fundamental_ambient_of_lieModel hp.out hp2 hadm hX hA1 hK.1
  have hdesc : ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n p f ∧
      p ^ e = p ^ f ∧ LieModel (X ⧸ center X) t n p f :=
    ⟨t, n, e, hadm, rfl, hX.quotient_center hZ⟩
  have hcount := ncard_funSet_eq_two_of_funTwoType hp.out hp2 hadm hX htwo P
  obtain ⟨J, hJ, hJK⟩ : ∃ J ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X), J ≠ K := by
    obtain ⟨A, B, hAB, hΔ⟩ := Set.ncard_eq_two.mp hcount
    by_cases hAK : A = K
    · exact ⟨B, hΔ ▸ Set.mem_insert_of_mem _ (Set.mem_singleton B), by simpa [hAK] using hAB.symm⟩
    · exact ⟨A, hΔ ▸ Set.mem_insert A _, hAK⟩
  obtain ⟨ψ, hψ, hker⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    t n p e hp.out hp2 hfund hadm X hX
  have hreal : ∀ {L : Subgroup X}, IsFundamentalOver (p ^ e) L →
      ∃ R ∈ ModelFund p t n e, L = R.map ψ := by
    intro L hL
    obtain ⟨R, hR, hLR, _⟩ := exists_mem_fundamentalSubgroups_of_isFundamentalOver_general
      hp.out hp2 hadm hX hfund hA1 hL2 ψ hψ hker hL
    exact ⟨R, hR, hLR⟩
  obtain ⟨RJ, hRJ, hJmap⟩ := hreal hJ.1
  obtain ⟨RK, hRK, hKmap⟩ := hreal hK.1
  have cJK : Commutes J K := by
    have hc := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.funSet_commute_of_lieModel
      hp.out hp2 hdesc hL2 P hJ hK hJK
    exact fun a ha b hb => (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc ha) b hb).symm
  have cModel : Commutes RJ RK := commutes_modelFund_of_commutes_map
    hp2 hfund hadm ψ hker hRJ (by simpa only [← hJmap, ← hKmap] using cJK)
  apply le_antisymm
  · refine iSup₂_le fun L hL => ?_
    obtain ⟨RL, hRL, hLmap⟩ := hreal hL.1
    have cJL : Commutes J L := by
      intro a ha b hb
      exact Subgroup.mem_centralizer_iff.mp (hL.2 hb) a ⟨J, hJ, hJK, ha⟩
    have cModel' : Commutes RJ RL := commutes_modelFund_of_commutes_map
      hp2 hfund hadm ψ hker hRJ (by simpa only [← hJmap, ← hLmap] using cJL)
    have heq := eq_of_commutes_small_orthogonal_modelFund hp2 hadm ht hRJ hRK hRL cModel cModel'
    rw [hLmap, ← heq, ← hKmap]
  · refine le_centralizingLayer ⟨hK.1, ?_⟩
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    rintro b ⟨L, hL, hLK, hb⟩
    have hc := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.funSet_commute_of_lieModel
      hp.out hp2 hdesc hL2 P hL hK hLK
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc hb) a ha).symm

end CFSG.LocalAnalysis.UniquenessCase.UC22
