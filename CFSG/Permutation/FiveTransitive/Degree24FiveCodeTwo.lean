module

public import CFSG.Permutation.FiveTransitive.Degree24FiveCode

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG

namespace FiveTransitive.Degree24

local instance fivePrime : Fact (Nat.Prime 5) :=
  ⟨by norm_num⟩

@[expose] def twoFiveWord
    (u v : FiveVector) (x : Fin 2 → ZMod 5) :
    FiveVector :=
  fun i => x 0 * u i + x 1 * v i

@[expose] def twoFiveWeightCount
    (u v : FiveVector) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin 2 → ZMod 5 =>
    fiveWeight (twoFiveWord u v x) = k).card

@[expose] def twoFiveActiveCoordinates
    (u v : FiveVector) : ℕ :=
  (Finset.univ.filter fun i : Fin 4 =>
    ∃ x : Fin 2 → ZMod 5,
      twoFiveWord u v x i ≠ 0).card

inductive FiveProjectiveColumn
  | zero
  | finite (s : ZMod 5)
  | vertical
deriving DecidableEq, Fintype

@[expose] def FiveProjectiveColumn.eval
    (c : FiveProjectiveColumn)
    (x : Fin 2 → ZMod 5) : ZMod 5 :=
  match c with
  | .zero => 0
  | .finite s => x 0 + x 1 * s
  | .vertical => x 1

def FiveProjectiveColumn.kernelVector
    (c : FiveProjectiveColumn) : Fin 2 → ZMod 5 :=
  match c with
  | .zero => ![1, 0]
  | .finite s => ![-s, 1]
  | .vertical => ![1, 0]

@[simp] theorem fiveProjectiveColumn_eval_zero
    (c : FiveProjectiveColumn) :
    c.eval (fun _ => 0) = 0 := by
  cases c <;> simp [FiveProjectiveColumn.eval]

private theorem fiveProjectiveColumn_kernelVector_ne_zero
    (c : FiveProjectiveColumn) :
    c.kernelVector ≠ 0 := by
  cases c with
  | zero =>
      intro h
      have hcoord := congrFun h 0
      norm_num [FiveProjectiveColumn.kernelVector] at hcoord
  | finite s =>
      intro h
      have hcoord := congrFun h 1
      norm_num [FiveProjectiveColumn.kernelVector] at hcoord
  | vertical =>
      intro h
      have hcoord := congrFun h 0
      norm_num [FiveProjectiveColumn.kernelVector] at hcoord

@[simp] theorem fiveProjectiveColumn_eval_kernelVector
    (c : FiveProjectiveColumn) :
    c.eval c.kernelVector = 0 := by
  cases c <;>
    simp [FiveProjectiveColumn.eval,
      FiveProjectiveColumn.kernelVector]

def fiveProjectivize
    (a b : ZMod 5) : FiveProjectiveColumn :=
  if a = 0 then
    if b = 0 then .zero else .vertical
  else
    .finite (b * a⁻¹)

private def twoFiveProjectiveWord
    (c : Fin 4 → FiveProjectiveColumn)
    (x : Fin 2 → ZMod 5) :
    FiveVector :=
  fun i => (c i).eval x

private def twoFiveProjectiveWeightCount
    (c : Fin 4 → FiveProjectiveColumn)
    (k : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin 2 → ZMod 5 =>
    fiveWeight (twoFiveProjectiveWord c x) = k).card

private def twoFiveProjectiveActiveCoordinates
    (c : Fin 4 → FiveProjectiveColumn) : ℕ :=
  (Finset.univ.filter fun i : Fin 4 =>
    ∃ x : Fin 2 → ZMod 5,
      twoFiveProjectiveWord c x i ≠ 0).card

private def twoFiveProjectiveSpans
    (c : Fin 4 → FiveProjectiveColumn) : Prop :=
  ∃ i j : Fin 4,
    c i ≠ .zero ∧ c j ≠ .zero ∧ c i ≠ c j

private theorem twoFiveProjective_not_spans_kernel
    (c : Fin 4 → FiveProjectiveColumn)
    (hnot : ¬twoFiveProjectiveSpans c) :
    ∃ x : Fin 2 → ZMod 5,
      x ≠ 0 ∧ twoFiveProjectiveWord c x = 0 := by
  classical
  by_cases hall : ∀ i, c i = .zero
  · refine
      ⟨FiveProjectiveColumn.zero.kernelVector,
        fiveProjectiveColumn_kernelVector_ne_zero
          .zero, ?_⟩
    funext i
    rw [twoFiveProjectiveWord, hall i]
    exact fiveProjectiveColumn_eval_kernelVector
      .zero
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    refine
      ⟨(c i).kernelVector,
        fiveProjectiveColumn_kernelVector_ne_zero
          (c i), ?_⟩
    funext j
    rw [twoFiveProjectiveWord]
    by_cases hj : c j = .zero
    · rw [hj]
      rfl
    · have hji : c j = c i := by
        by_contra hne
        exact hnot
          ⟨i, j, hi, hj,
            fun hij => hne hij.symm⟩
      rw [hji]
      exact fiveProjectiveColumn_eval_kernelVector
        (c i)

private def fiveProjectiveKernel
    (x : Fin 2 → ZMod 5) : FiveProjectiveColumn :=
  if x 1 = 0 then
    .vertical
  else
    .finite (-x 0 * (x 1)⁻¹)

private theorem fiveProjectiveKernel_ne_zero
    (x : Fin 2 → ZMod 5) :
    fiveProjectiveKernel x ≠ .zero := by
  unfold fiveProjectiveKernel
  split <;> intro h <;> contradiction

private theorem fiveProjectiveColumn_eval_eq_zero_iff
    (c : FiveProjectiveColumn)
    (x : Fin 2 → ZMod 5) (hx : x ≠ 0) :
    c.eval x = 0 ↔
      c = .zero ∨ c = fiveProjectiveKernel x := by
  cases c with
  | zero =>
      simp [FiveProjectiveColumn.eval]
  | vertical =>
      by_cases hxone : x 1 = 0
      · simp [FiveProjectiveColumn.eval,
          fiveProjectiveKernel, hxone]
      · simp [FiveProjectiveColumn.eval,
          fiveProjectiveKernel, hxone]
  | finite s =>
      by_cases hxone : x 1 = 0
      · have hxzero : x 0 ≠ 0 := by
          intro hxzero
          apply hx
          funext i
          fin_cases i
          · exact hxzero
          · exact hxone
        simp [FiveProjectiveColumn.eval,
          fiveProjectiveKernel, hxone, hxzero]
      · have hkernel :
            fiveProjectiveKernel x =
              .finite (-x 0 * (x 1)⁻¹) := by
          simp [fiveProjectiveKernel, hxone]
        constructor
        · intro heval
          change x 0 + x 1 * s = 0 at heval
          right
          rw [hkernel]
          apply congrArg FiveProjectiveColumn.finite
          apply mul_right_cancel₀ hxone
          calc
            s * x 1 = x 1 * s := mul_comm _ _
            _ = -x 0 := by
              linear_combination heval
            _ = (-x 0 * (x 1)⁻¹) * x 1 := by
              rw [mul_assoc,
                inv_mul_cancel₀ hxone, mul_one]
        · rintro (hzero | hfinite)
          · cases hzero
          · rw [hkernel] at hfinite
            have hs :=
              FiveProjectiveColumn.finite.inj hfinite
            rw [hs]
            calc
              x 0 + x 1 *
                    (-x 0 * (x 1)⁻¹) =
                  x 0 + (-x 0) *
                    (x 1 * (x 1)⁻¹) := by
                ring
              _ = 0 := by
                rw [mul_inv_cancel₀ hxone,
                  mul_one, add_neg_cancel]

private def projectiveMultiplicity
    (c : Fin 4 → FiveProjectiveColumn)
    (d : FiveProjectiveColumn) : ℕ :=
  (Finset.univ.filter fun i : Fin 4 =>
    c i = d).card

private def projectiveActiveCoordinates
    (c : Fin 4 → FiveProjectiveColumn) : ℕ :=
  (Finset.univ.filter fun i : Fin 4 =>
    c i ≠ .zero).card

private def projectivePatternWeight
    (c : Fin 4 → FiveProjectiveColumn)
    (d : FiveProjectiveColumn) : ℕ :=
  projectiveActiveCoordinates c -
    projectiveMultiplicity c d

private def projectivePatternWeightCount
    (c : Fin 4 → FiveProjectiveColumn)
    (k : ℕ) : ℕ :=
  4 * ((Finset.univ.erase
    FiveProjectiveColumn.zero).filter fun d =>
      projectivePatternWeight c d = k).card

private theorem exists_fiveProjectiveColumn_eval_ne_zero_iff
    (d : FiveProjectiveColumn) :
    (∃ x : Fin 2 → ZMod 5, d.eval x ≠ 0) ↔
      d ≠ .zero := by
  constructor
  · rintro ⟨x, hx⟩ rfl
    exact hx rfl
  · intro hd
    cases d with
    | zero => exact False.elim (hd rfl)
    | finite s =>
        refine ⟨![1, 0], ?_⟩
        norm_num [FiveProjectiveColumn.eval]
    | vertical =>
        refine ⟨![0, 1], ?_⟩
        norm_num [FiveProjectiveColumn.eval]

private theorem twoFiveProjectiveActiveCoordinates_eq_pattern
    (c : Fin 4 → FiveProjectiveColumn) :
    twoFiveProjectiveActiveCoordinates c =
      projectiveActiveCoordinates c := by
  unfold twoFiveProjectiveActiveCoordinates
  unfold projectiveActiveCoordinates
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _
  simpa only [twoFiveProjectiveWord] using
    (exists_fiveProjectiveColumn_eval_ne_zero_iff (c i))

private theorem fiveWeight_twoFiveProjectiveWord_eq_pattern
    (c : Fin 4 → FiveProjectiveColumn)
    (x : Fin 2 → ZMod 5) (hx : x ≠ 0) :
    fiveWeight (twoFiveProjectiveWord c x) =
      projectivePatternWeight c
        (fiveProjectiveKernel x) := by
  classical
  let A :=
    Finset.univ.filter fun i : Fin 4 =>
      c i ≠ .zero
  let M :=
    Finset.univ.filter fun i : Fin 4 =>
      c i = fiveProjectiveKernel x
  have hMsub : M ⊆ A := by
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_univ i, ?_⟩
    rw [hi.2]
    exact fiveProjectiveKernel_ne_zero x
  have hsupport :
      (Finset.univ.filter fun i : Fin 4 =>
        (c i).eval x ≠ 0) = A \ M := by
    ext i
    simp only [Finset.mem_filter,
      Finset.mem_univ, true_and,
      Finset.mem_sdiff, A, M]
    have hz :=
      fiveProjectiveColumn_eval_eq_zero_iff
        (c i) x hx
    constructor
    · intro hne
      exact
        ⟨fun hzero =>
            hne (hz.mpr (Or.inl hzero)),
          fun hkernel =>
            hne (hz.mpr (Or.inr hkernel))⟩
    · rintro ⟨hzero, hkernel⟩ heval
      rcases hz.mp heval with heq | heq
      · exact hzero heq
      · exact hkernel heq
  unfold fiveWeight
  unfold twoFiveProjectiveWord
  unfold projectivePatternWeight
  unfold projectiveActiveCoordinates
  unfold projectiveMultiplicity
  rw [hsupport, Finset.card_sdiff,
    Finset.inter_eq_left.mpr hMsub]

private def fiveProjectiveKernelFiber
    (d : FiveProjectiveColumn) :
    Finset (Fin 2 → ZMod 5) :=
  Finset.univ.filter fun x =>
    x ≠ 0 ∧ fiveProjectiveKernel x = d

private theorem fiveProjectiveKernelFiber_card
    (d : FiveProjectiveColumn) (hd : d ≠ .zero) :
    (fiveProjectiveKernelFiber d).card = 4 := by
  cases d with
  | zero => exact False.elim (hd rfl)
  | finite s =>
      let R :=
        Finset.univ.filter fun r : ZMod 5 =>
          r ≠ 0
      have hRcard : R.card = 4 := by
        unfold R
        rw [Finset.filter_ne',
          Finset.card_erase_of_mem
            (Finset.mem_univ (0 : ZMod 5)),
          Finset.card_univ, ZMod.card]
      calc
        (fiveProjectiveKernelFiber
            (.finite s)).card = R.card := by
          apply Finset.card_bij
              (fun x _ => x 1)
          · intro x hx
            simp only [fiveProjectiveKernelFiber,
              Finset.mem_filter, Finset.mem_univ,
              true_and] at hx
            simp only [R, Finset.mem_filter,
              Finset.mem_univ, true_and]
            intro hxone
            have hkernel := hx.2
            simp [fiveProjectiveKernel,
              hxone] at hkernel
          · intro x hx y hy hxy
            simp only [fiveProjectiveKernelFiber,
              Finset.mem_filter, Finset.mem_univ,
              true_and] at hx hy
            have hevalx :
                (FiveProjectiveColumn.finite s).eval x =
                  0 :=
              (fiveProjectiveColumn_eval_eq_zero_iff
                (.finite s) x hx.1).mpr
                  (Or.inr hx.2.symm)
            have hevaly :
                (FiveProjectiveColumn.finite s).eval y =
                  0 :=
              (fiveProjectiveColumn_eval_eq_zero_iff
                (.finite s) y hy.1).mpr
                  (Or.inr hy.2.symm)
            change x 0 + x 1 * s = 0 at hevalx
            change y 0 + y 1 * s = 0 at hevaly
            have hzero : x 0 = y 0 := by
              calc
                x 0 = -(x 1 * s) :=
                  eq_neg_of_add_eq_zero_left hevalx
                _ = -(y 1 * s) := by rw [hxy]
                _ = y 0 :=
                  neg_eq_of_add_eq_zero_left hevaly
            funext i
            fin_cases i
            · exact hzero
            · exact hxy
          · intro r hr
            rw [Finset.mem_filter] at hr
            let x : Fin 2 → ZMod 5 :=
              ![-r * s, r]
            have hxne : x ≠ 0 := by
              intro hxzero
              have hcoord := congrFun hxzero 1
              exact hr.2 (by
                simpa [x] using hcoord)
            have heval :
                (FiveProjectiveColumn.finite s).eval x =
                  0 := by
              simp [FiveProjectiveColumn.eval, x]
            have hkernel :
                fiveProjectiveKernel x =
                  .finite s := by
              rcases
                  (fiveProjectiveColumn_eval_eq_zero_iff
                    (.finite s) x hxne).mp heval with
                hzero | hkernel
              · cases hzero
              · exact hkernel.symm
            refine ⟨x, ?_, ?_⟩
            · simp only [fiveProjectiveKernelFiber,
                Finset.mem_filter, Finset.mem_univ,
                true_and]
              exact ⟨hxne, hkernel⟩
            · rfl
        _ = 4 := hRcard
  | vertical => decide

private theorem twoFiveProjectiveWeightCount_eq_pattern
    (c : Fin 4 → FiveProjectiveColumn)
    (k : ℕ) (hk : k ≠ 0) :
    twoFiveProjectiveWeightCount c k =
      projectivePatternWeightCount c k := by
  classical
  let U :=
    Finset.univ.filter fun x : Fin 2 → ZMod 5 =>
      x ≠ 0
  let S :=
    U.filter fun x =>
      fiveWeight (twoFiveProjectiveWord c x) = k
  let D :=
    Finset.univ.erase FiveProjectiveColumn.zero
  have hremove :
      (Finset.univ.filter fun x : Fin 2 → ZMod 5 =>
        fiveWeight (twoFiveProjectiveWord c x) = k) =
        S := by
    ext x
    simp only [Finset.mem_filter,
      Finset.mem_univ, true_and, S, U]
    constructor
    · intro hweight
      refine ⟨?_, hweight⟩
      intro hxzero
      subst x
      have hzero :
          fiveWeight
              (twoFiveProjectiveWord c
                (0 : Fin 2 → ZMod 5)) = 0 := by
        have hword :
            twoFiveProjectiveWord c
                (0 : Fin 2 → ZMod 5) = 0 := by
          funext i
          change (c i).eval
              (0 : Fin 2 → ZMod 5) = 0
          rw [Pi.zero_def]
          exact fiveProjectiveColumn_eval_zero (c i)
        rw [hword]
        simp [fiveWeight]
      rw [hzero] at hweight
      exact hk hweight.symm
    · exact fun h => h.2
  have hmaps :
      ∀ x ∈ S,
        fiveProjectiveKernel x ∈ D := by
    intro x hx
    simp [D, fiveProjectiveKernel_ne_zero]
  have hcardFiber :
      S.card =
        ∑ d ∈ D,
          (S.filter fun x =>
            fiveProjectiveKernel x = d).card :=
    Finset.card_eq_sum_card_fiberwise
      (f := fiveProjectiveKernel)
      (s := S) (t := D) hmaps
  have hfiber (d : FiveProjectiveColumn)
      (hd : d ∈ D) :
      (S.filter fun x =>
          fiveProjectiveKernel x = d).card =
        if projectivePatternWeight c d = k then
          4
        else
          0 := by
    have hdne : d ≠ .zero := by
      simpa [D] using hd
    by_cases hpattern :
        projectivePatternWeight c d = k
    · rw [if_pos hpattern,
        ← fiveProjectiveKernelFiber_card d hdne]
      congr 1
      ext x
      simp only [Finset.mem_filter,
        Finset.mem_univ, true_and,
        S, U, fiveProjectiveKernelFiber]
      constructor
      · rintro ⟨⟨hxne, hweight⟩, hkernel⟩
        exact ⟨hxne, hkernel⟩
      · rintro ⟨hxne, hkernel⟩
        refine ⟨⟨hxne, ?_⟩, hkernel⟩
        rw [fiveWeight_twoFiveProjectiveWord_eq_pattern
          c x hxne, hkernel, hpattern]
    · rw [if_neg hpattern]
      rw [Finset.card_eq_zero]
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨x, hx⟩
      simp only [Finset.mem_filter,
        Finset.mem_univ, true_and,
        S, U] at hx
      apply hpattern
      rw [← hx.2,
        ← fiveWeight_twoFiveProjectiveWord_eq_pattern
          c x hx.1.1]
      exact hx.1.2
  unfold twoFiveProjectiveWeightCount
  rw [hremove, hcardFiber]
  calc
    (∑ d ∈ D,
        (S.filter fun x =>
          fiveProjectiveKernel x = d).card) =
        ∑ d ∈ D,
          if projectivePatternWeight c d = k then
            4
          else
            0 := by
      apply Finset.sum_congr rfl
      intro d hd
      exact hfiber d hd
    _ =
        4 * (D.filter fun d =>
          projectivePatternWeight c d = k).card := by
      rw [← Finset.sum_filter]
      simp
      omega
    _ = projectivePatternWeightCount c k := by
      rfl

private def projectiveDirectionCount
    (c : Fin 4 → FiveProjectiveColumn) : ℕ :=
  ((Finset.univ.filter fun i : Fin 4 =>
      c i ≠ .zero).image c).card

private def projectivePatternDistribution
    (c : Fin 4 → FiveProjectiveColumn) : Prop :=
  0 < projectivePatternWeightCount c 1 ∨
    (projectiveActiveCoordinates c = 3 ∧
      projectivePatternWeightCount c 2 = 12 ∧
      projectivePatternWeightCount c 3 = 12) ∨
    (projectiveActiveCoordinates c = 4 ∧
      ((projectivePatternWeightCount c 2 = 8 ∧
          projectivePatternWeightCount c 3 = 0) ∨
        (projectivePatternWeightCount c 2 = 4 ∧
          projectivePatternWeightCount c 3 = 8) ∨
        (projectivePatternWeightCount c 2 = 0 ∧
          projectivePatternWeightCount c 3 = 16)))

private def fourProjectiveColumns
    (a b c d : FiveProjectiveColumn) :
    Fin 4 → FiveProjectiveColumn :=
  ![a, b, c, d]

private theorem fourProjectiveColumns_pattern_distribution :
    ∀ a b c d : FiveProjectiveColumn,
      2 ≤ projectiveDirectionCount
          (fourProjectiveColumns a b c d) →
        projectivePatternDistribution
          (fourProjectiveColumns a b c d) := by
  unfold projectivePatternDistribution
  decide +kernel

private theorem projectiveDirectionCount_two_le_of_spans
    (c : Fin 4 → FiveProjectiveColumn)
    (hspans : twoFiveProjectiveSpans c) :
    2 ≤ projectiveDirectionCount c := by
  classical
  rcases hspans with ⟨i, j, hi, hj, hij⟩
  have himem :
      c i ∈
        (Finset.univ.filter fun k : Fin 4 =>
          c k ≠ .zero).image c := by
    apply Finset.mem_image.mpr
    exact
      ⟨i, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hi⟩, rfl⟩
  have hjmem :
      c j ∈
        (Finset.univ.filter fun k : Fin 4 =>
          c k ≠ .zero).image c := by
    apply Finset.mem_image.mpr
    exact
      ⟨j, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hj⟩, rfl⟩
  have hone :
      1 <
        ((Finset.univ.filter fun k : Fin 4 =>
          c k ≠ .zero).image c).card :=
    Finset.one_lt_card.mpr
      ⟨c i, himem, c j, hjmem, hij⟩
  change 2 ≤
    ((Finset.univ.filter fun k : Fin 4 =>
      c k ≠ .zero).image c).card
  omega

private theorem projectivePattern_weight_distribution
    (c : Fin 4 → FiveProjectiveColumn)
    (hspans : twoFiveProjectiveSpans c) :
    projectivePatternDistribution c := by
  have hdirections :=
    projectiveDirectionCount_two_le_of_spans c hspans
  have hc :
      c = fourProjectiveColumns
        (c 0) (c 1) (c 2) (c 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc] at hdirections ⊢
  exact fourProjectiveColumns_pattern_distribution
    (c 0) (c 1) (c 2) (c 3) hdirections

private theorem twoFiveProjectiveCode_weight_distribution
    (c : Fin 4 → FiveProjectiveColumn)
    (hspans : twoFiveProjectiveSpans c) :
    0 < twoFiveProjectiveWeightCount c 1 ∨
      (twoFiveProjectiveActiveCoordinates c = 3 ∧
        twoFiveProjectiveWeightCount c 2 = 12 ∧
        twoFiveProjectiveWeightCount c 3 = 12) ∨
      (twoFiveProjectiveActiveCoordinates c = 4 ∧
        ((twoFiveProjectiveWeightCount c 2 = 8 ∧
            twoFiveProjectiveWeightCount c 3 = 0) ∨
          (twoFiveProjectiveWeightCount c 2 = 4 ∧
            twoFiveProjectiveWeightCount c 3 = 8) ∨
          (twoFiveProjectiveWeightCount c 2 = 0 ∧
            twoFiveProjectiveWeightCount c 3 = 16))) := by
  have hdistribution :=
    projectivePattern_weight_distribution c hspans
  unfold projectivePatternDistribution at hdistribution
  rw [← twoFiveProjectiveActiveCoordinates_eq_pattern c,
    ← twoFiveProjectiveWeightCount_eq_pattern c 1
      (by norm_num),
    ← twoFiveProjectiveWeightCount_eq_pattern c 2
      (by norm_num),
    ← twoFiveProjectiveWeightCount_eq_pattern c 3
      (by norm_num)] at hdistribution
  exact hdistribution

theorem fiveProjectivize_eval_eq_iff
    (a b : ZMod 5) (x y : Fin 2 → ZMod 5) :
    (fiveProjectivize a b).eval x =
        (fiveProjectivize a b).eval y ↔
      x 0 * a + x 1 * b =
        y 0 * a + y 1 * b := by
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      simp [fiveProjectivize, FiveProjectiveColumn.eval]
    · rw [show fiveProjectivize 0 b =
          .vertical by
        simp [fiveProjectivize, hb]]
      simp only [FiveProjectiveColumn.eval,
        mul_zero, zero_add]
      constructor
      · intro h
        exact congrArg (fun z => z * b) h
      · intro h
        exact mul_right_cancel₀ hb h
  · simp only [fiveProjectivize, if_neg ha,
      FiveProjectiveColumn.eval]
    have hrewrite (z : Fin 2 → ZMod 5) :
        (z 0 + z 1 * (b * a⁻¹)) * a =
          z 0 * a + z 1 * b := by
      calc
        (z 0 + z 1 * (b * a⁻¹)) * a =
            z 0 * a + z 1 * b * (a⁻¹ * a) := by
          ring
        _ = z 0 * a + z 1 * b := by
          rw [inv_mul_cancel₀ ha, mul_one]
    rw [← hrewrite x, ← hrewrite y]
    constructor
    · intro h
      exact congrArg (fun z => z * a) h
    · intro h
      exact mul_right_cancel₀ ha h

theorem twoFiveCode_weight_distribution
    (u v : FiveVector)
    (hinjective :
      Function.Injective (twoFiveWord u v)) :
    0 < twoFiveWeightCount u v 1 ∨
      (twoFiveActiveCoordinates u v = 3 ∧
        twoFiveWeightCount u v 2 = 12 ∧
        twoFiveWeightCount u v 3 = 12) ∨
      (twoFiveActiveCoordinates u v = 4 ∧
        ((twoFiveWeightCount u v 2 = 8 ∧
            twoFiveWeightCount u v 3 = 0) ∨
          (twoFiveWeightCount u v 2 = 4 ∧
            twoFiveWeightCount u v 3 = 8) ∨
          (twoFiveWeightCount u v 2 = 0 ∧
            twoFiveWeightCount u v 3 = 16))) := by
  let c : Fin 4 → FiveProjectiveColumn :=
    fun i => fiveProjectivize (u i) (v i)
  have heval (x y : Fin 2 → ZMod 5) :
      twoFiveProjectiveWord c x =
          twoFiveProjectiveWord c y ↔
        twoFiveWord u v x = twoFiveWord u v y := by
    constructor
    · intro h
      funext i
      exact
        (fiveProjectivize_eval_eq_iff
          (u i) (v i) x y).mp
            (congrFun h i)
    · intro h
      funext i
      exact
        (fiveProjectivize_eval_eq_iff
          (u i) (v i) x y).mpr
            (congrFun h i)
  have hinjectiveProjective :
      Function.Injective
        (twoFiveProjectiveWord c) := by
    intro x y hxy
    exact hinjective ((heval x y).mp hxy)
  have hspans : twoFiveProjectiveSpans c := by
    by_contra hnot
    obtain ⟨x, hxne, hxzero⟩ :=
      twoFiveProjective_not_spans_kernel c hnot
    apply hxne
    apply hinjectiveProjective
    rw [hxzero]
    funext i
    exact (fiveProjectiveColumn_eval_zero (c i)).symm
  have hweight (x : Fin 2 → ZMod 5) :
      fiveWeight (twoFiveProjectiveWord c x) =
        fiveWeight (twoFiveWord u v x) := by
    unfold fiveWeight
    congr 1
    ext i
    simp only [Finset.mem_filter,
      Finset.mem_univ, true_and]
    change
      (fiveProjectivize (u i) (v i)).eval x ≠ 0 ↔
        x 0 * u i + x 1 * v i ≠ 0
    simpa using
      not_congr
        (fiveProjectivize_eval_eq_iff
          (u i) (v i) x (fun _ => 0))
  have hcount (k : ℕ) :
      twoFiveProjectiveWeightCount c k =
        twoFiveWeightCount u v k := by
    unfold twoFiveProjectiveWeightCount
    unfold twoFiveWeightCount
    congr 1
    ext x
    simp only [Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [hweight]
  have hactive :
      twoFiveProjectiveActiveCoordinates c =
        twoFiveActiveCoordinates u v := by
    unfold twoFiveProjectiveActiveCoordinates
    unfold twoFiveActiveCoordinates
    congr 1
    ext i
    simp only [Finset.mem_filter,
      Finset.mem_univ, true_and]
    apply exists_congr
    intro x
    change
      (fiveProjectivize (u i) (v i)).eval x ≠ 0 ↔
        x 0 * u i + x 1 * v i ≠ 0
    simpa using
      not_congr
        (fiveProjectivize_eval_eq_iff
          (u i) (v i) x (fun _ => 0))
  have hclassification :=
    twoFiveProjectiveCode_weight_distribution
      c hspans
  rwa [hactive, hcount 1, hcount 2,
    hcount 3] at hclassification

end FiveTransitive.Degree24

end CFSG
