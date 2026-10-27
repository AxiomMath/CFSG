module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteLower
public import CFSG.ClassicalInvolution.Solomon73.YamakiPres
public import CFSG.Mathlib.Decide.Bounded

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
open CFSG.ClassicalInvolution.Solomon73.Yamaki

@[expose] def tmW7_xWordRaw : Fin 12 → List (Fin 7) :=
  ![[3, 4, 5, 6, 1, 5, 3, 4, 2, 3, 0, 2, 1, 3,
      4, 5, 4, 6, 3, 4, 1, 2, 3, 4, 1, 5, 0, 2,
      3, 4, 0, 2, 1, 3],
    [3, 6, 4, 5, 1, 3, 2, 4, 3, 1, 0, 2, 3, 4,
      1, 5, 3, 4, 2, 3, 1, 6, 0, 2, 3, 4, 2, 3,
      0, 2, 1, 3, 0, 1],
    [4, 5, 0, 6, 2, 3, 4, 5, 1, 3, 2, 4, 3, 1,
      0, 2, 3, 4, 1, 5, 3, 4, 2, 3, 1, 6, 0, 2,
      3, 4, 2, 3, 1, 5, 0, 2, 3, 4, 0, 2, 0, 1],
    [1, 6, 3, 4, 1, 5, 3, 4, 2, 3, 0, 2, 1, 3,
      4, 5, 2, 3, 1, 6, 0, 2, 3, 4, 0, 2, 1, 3,
      0, 1],
    [3, 4, 1, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5,
      3, 4, 2, 3, 0, 2, 1, 3, 0, 4, 2, 3, 0, 2,
      1, 3],
    [3, 6, 4, 5, 1, 3, 2, 4, 3, 1, 0, 2, 3, 4,
      5, 6, 2, 5, 3, 4, 3, 5, 1, 2, 3, 4, 2, 3,
      1, 5, 0, 2, 3, 4, 2, 3, 0, 2, 1, 3, 0, 1],
    [4, 5, 1, 6, 0, 2, 3, 4, 1, 5, 3, 4, 2, 3,
      0, 2, 1, 3, 4, 5, 2, 3, 1, 6, 0, 2, 3, 4,
      1, 5, 0, 2, 3, 4, 0, 2, 0, 1],
    [4, 5, 0, 6, 2, 3, 4, 5, 1, 3, 2, 4, 3, 1,
      0, 2, 3, 4, 5, 6, 2, 3, 4, 5, 1, 2, 3, 4,
      2, 3, 1, 5, 0, 2, 3, 4, 2, 3, 1, 5, 0, 2,
      3, 4, 1, 3, 0, 2, 0, 1],
    [6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 0, 2, 3, 4,
      1, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 1, 6,
      0, 2, 3, 4, 0, 5, 2, 3, 0, 4, 2, 3, 0, 2,
      0, 1],
    [5, 6, 2, 3, 4, 5, 1, 3, 2, 4, 3, 1, 0, 2,
      3, 4, 5, 6, 3, 4, 1, 5, 3, 4, 2, 3, 0, 2,
      1, 3, 4, 5, 0, 2, 3, 4, 2, 3, 0, 2, 1, 3,
      1, 2],
    [2, 3, 4, 5, 1, 6, 0, 2, 3, 4, 1, 5, 3, 4,
      2, 3, 0, 2, 1, 3, 4, 5, 2, 3, 1, 6, 0, 2,
      3, 4, 1, 5, 0, 2, 3, 4, 0, 2, 1, 3, 0, 2],
    [6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 0, 2, 3, 4,
      1, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 1, 6,
      0, 2, 3, 4, 1, 5, 3, 4, 2, 3, 1, 4, 0, 2,
      3, 4, 1, 5, 0, 2, 3, 4, 1, 3, 0, 2, 1, 3,
      0, 1]]

@[expose] def tmW7_xWord (i : Fin 12) : List (Fin Tag.E7.rank) :=
  (tmW7_xWordRaw i).map (Fin.cast (by decide : 7 = Tag.E7.rank))

@[expose] noncomputable def tmW7_x (i : Fin 12) : WeylGroup Tag.E7 :=
  wordW Tag.E7 (tmW7_xWord i)

theorem tmW7_wordW_append {τ : Tag} (l₁ l₂ : List (Fin τ.rank)) :
    wordW τ (l₁ ++ l₂) = wordW τ l₁ * wordW τ l₂ := by
  simp only [wordW, List.map_append, List.prod_append]

theorem tmW7_wordW_prod_map {τ : Tag} {ι : Type*} (w : ι → List (Fin τ.rank)) (l : List ι) :
    (l.map fun i => wordW τ (w i)).prod = wordW τ (l.flatMap w) := by
  induction l with
  | nil => simp [wordW]
  | cons i l ih => rw [List.map_cons, List.prod_cons, List.flatMap_cons, tmW7_wordW_append, ih]

theorem tmW7_xWord_even : ∀ i : Fin 12, Even (tmW7_xWord i).length := by decide

private def tmW7_xMat : Fin 12 → Fin Tag.E7.rank → Fin Tag.E7.rank → ℤ :=
  ![
      ![![0, 0, 0, 0, 1, 0, 0],
        ![1, 1, 2, 2, 1, 0, 0],
        ![1, 2, 2, 3, 2, 2, 1],
        ![-2, -2, -3, -4, -3, -2, -1],
        ![1, 0, 0, 0, 0, 0, 0],
        ![0, 0, 1, 1, 1, 1, 1],
        ![0, 0, 0, 0, 0, 0, -1]],
      ![![0, 0, 0, 0, -1, 0, 0],
        ![0, -1, 0, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 1, 1],
        ![0, 0, -1, -1, -1, -1, -1],
        ![-1, 0, 0, 0, 0, 0, 0],
        ![2, 2, 3, 4, 3, 2, 1],
        ![-1, -2, -2, -4, -3, -2, -1]],
      ![![0, 0, 0, 0, 0, 0, -1],
        ![0, -1, 0, 0, 0, 0, 0],
        ![0, 0, 0, 0, 0, -1, 0],
        ![1, 2, 2, 3, 2, 2, 1],
        ![-1, -2, -2, -4, -3, -2, -1],
        ![0, 0, -1, 0, 0, 0, 0],
        ![-1, 0, 0, 0, 0, 0, 0]],
      ![![-1, 0, 0, 0, 0, 0, 0],
        ![-1, -1, -2, -2, -1, 0, 0],
        ![1, 0, 1, 1, 1, 1, 1],
        ![0, 0, 0, 0, 0, -1, -1],
        ![0, 0, 0, 0, -1, 0, 0],
        ![1, 2, 2, 3, 3, 2, 1],
        ![-1, -2, -2, -4, -3, -2, -1]],
      ![![0, 0, 0, 0, 1, 0, 0],
        ![0, -1, 0, 0, 0, 0, 0],
        ![0, 0, 0, 0, 0, 1, 0],
        ![-1, 0, -1, -1, -1, -1, 0],
        ![1, 0, 0, 0, 0, 0, 0],
        ![0, 0, 1, 0, 0, 0, 0],
        ![1, 2, 2, 4, 3, 2, 1]],
      ![![-1, 0, 0, 0, 0, 0, 0],
        ![0, -1, 0, 0, 0, 0, 0],
        ![1, 1, 1, 2, 2, 2, 1],
        ![-1, -1, -2, -3, -2, -2, -1],
        ![0, 0, 0, 0, -1, 0, 0],
        ![1, 1, 2, 2, 2, 1, 1],
        ![0, 0, 0, 0, 0, 0, -1]],
      ![![0, 0, 0, -1, -1, -1, -1],
        ![0, -1, -1, -2, -2, -1, 0],
        ![0, 0, -1, 0, 0, 0, 0],
        ![1, 2, 3, 4, 3, 2, 1],
        ![-1, -2, -2, -3, -2, -1, -1],
        ![0, 0, 0, 0, 0, -1, 0],
        ![-1, 0, -1, -1, -1, 0, 0]],
      ![![-1, -1, -1, -2, -1, -1, -1],
        ![0, -1, 0, 0, 0, 0, 0],
        ![0, 0, -1, 0, 0, 0, 0],
        ![0, 1, 1, 1, 1, 1, 1],
        ![0, -1, -1, -2, -2, -1, -1],
        ![0, 0, 0, 0, 0, -1, 0],
        ![0, 1, 1, 2, 1, 1, 0]],
      ![![-1, 0, 0, 0, 0, 0, 0],
        ![-1, -2, -2, -3, -2, -1, 0],
        ![0, 0, -1, 0, 0, 0, 0],
        ![1, 1, 2, 2, 2, 1, 0],
        ![0, 0, 0, 0, -1, 0, 0],
        ![0, 0, 0, 0, 0, -1, 0],
        ![-1, -1, -2, -3, -2, -1, -1]],
      ![![1, 1, 2, 2, 2, 1, 1],
        ![0, -1, 0, 0, 0, 0, 0],
        ![0, -1, -1, -2, -2, -1, -1],
        ![-1, 0, -1, -1, -1, -1, 0],
        ![1, 1, 1, 2, 2, 2, 1],
        ![-1, -1, -1, -2, -1, -1, -1],
        ![1, 1, 1, 2, 1, 0, 0]],
      ![![1, 2, 2, 3, 2, 1, 0],
        ![1, 1, 1, 2, 1, 1, 1],
        ![-1, -2, -2, -3, -3, -2, -1],
        ![0, 0, 0, -1, 0, 0, 0],
        ![0, 0, 0, 1, 1, 1, 0],
        ![0, 0, 0, 0, 0, -1, 0],
        ![-1, 0, -1, -1, -1, 0, 0]],
      ![![-1, 0, -1, -1, -1, 0, 0],
        ![0, -1, -1, -1, -1, 0, 0],
        ![0, 0, 0, 1, 1, 0, 0],
        ![0, 0, 0, -1, 0, 0, 0],
        ![0, 0, 1, 1, 0, 0, 0],
        ![0, 0, -1, -1, -1, -1, 0],
        ![0, 0, 0, 0, 0, 0, -1]]]

private theorem tmW7_rank : 7 = Tag.E7.rank := by decide

private def tmW7_idx : Fin 7 → Fin Tag.E7.rank := finCongr tmW7_rank

private def tmW7_mulVec7 (c : Fin Tag.E7.rank → Fin Tag.E7.rank → ℤ)
    (v : Fin Tag.E7.rank → ℤ) : Fin Tag.E7.rank → ℤ :=
  fun a => v (tmW7_idx 0) * c (tmW7_idx 0) a + v (tmW7_idx 1) * c (tmW7_idx 1) a +
    v (tmW7_idx 2) * c (tmW7_idx 2) a + v (tmW7_idx 3) * c (tmW7_idx 3) a +
    v (tmW7_idx 4) * c (tmW7_idx 4) a + v (tmW7_idx 5) * c (tmW7_idx 5) a +
    v (tmW7_idx 6) * c (tmW7_idx 6) a

private theorem tmW7_reflect_add {τ : Tag} (i : Fin τ.rank) (u v : Fin τ.rank → ℤ) :
    reflect τ i (u + v) = reflect τ i u + reflect τ i v := by
  ext a
  simp only [reflect, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, Pi.single_apply]
  by_cases h : a = i
  · simp [h]
    ring
  · simp [h]

private def tmW7_reflectHom {τ : Tag} (i : Fin τ.rank) :
    (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ) where
  toFun := reflect τ i
  map_zero' := by simp [reflect]
  map_add' := tmW7_reflect_add i

private theorem tmW7_reflectHom_apply {τ : Tag} (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    tmW7_reflectHom i v = reflect τ i v := rfl

private theorem tmW7_wordAct_append {τ : Tag} (a b : List (Fin τ.rank))
    (v : Fin τ.rank → ℤ) :
    TableBExc.wordAct τ (a ++ b) v =
      TableBExc.wordAct τ a (TableBExc.wordAct τ b v) := by
  simp only [TableBExc.wordAct, List.foldr_append]

private theorem tmW7_wordAct_sum {τ : Tag} (w : List (Fin τ.rank)) {ι : Type*}
    (s : Finset ι) (c : ι → ℤ) (u : ι → Fin τ.rank → ℤ) :
    TableBExc.wordAct τ w (∑ k ∈ s, c k • u k) =
      ∑ k ∈ s, c k • TableBExc.wordAct τ w (u k) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      simp only [TableBExc.wordAct, List.foldr_cons] at ih ⊢
      rw [ih, ← tmW7_reflectHom_apply, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, tmW7_reflectHom_apply]

private theorem tmW7_wordAct_eq_sum {τ : Tag} (w : List (Fin τ.rank))
    (v : Fin τ.rank → ℤ) :
    TableBExc.wordAct τ w v =
      fun a => ∑ k, v k * TableBExc.wordAct τ w (Pi.single k 1) a := by
  have hv : v = ∑ k : Fin τ.rank, v k • (Pi.single k 1 : Fin τ.rank → ℤ) := by
    ext a
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [tmW7_wordAct_sum]
  ext a
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

private theorem tmW7_xMat_spec :
    ∀ i : Fin 12, ∀ k : Fin Tag.E7.rank,
      TableBExc.wordAct Tag.E7 (tmW7_xWord i) (Pi.single k 1) = tmW7_xMat i k := by
  decide +kernel

private theorem tmW7_wordAct_eq_mulVec7 (i : Fin 12) (v : Fin Tag.E7.rank → ℤ) :
    TableBExc.wordAct Tag.E7 (tmW7_xWord i) v = tmW7_mulVec7 (tmW7_xMat i) v := by
  rw [tmW7_wordAct_eq_sum]
  ext a
  rw [← Equiv.sum_comp (finCongr tmW7_rank)
    (fun k : Fin Tag.E7.rank => v k *
      TableBExc.wordAct Tag.E7 (tmW7_xWord i) (Pi.single k 1) a)]
  rw [Fin.sum_univ_seven]
  simp only [tmW7_mulVec7, tmW7_idx, tmW7_xMat_spec]

@[expose] def tmW7_expand (r : List (Fin 12 × Bool)) : List (Fin Tag.E7.rank) :=
  r.flatMap fun l => tmW7_xWord l.1

private def tmW7_fastAct (r : List (Fin 12 × Bool)) (v : Fin Tag.E7.rank → ℤ) :
    Fin Tag.E7.rank → ℤ :=
  r.foldr (fun l v => tmW7_mulVec7 (tmW7_xMat l.1) v) v

private theorem tmW7_wordAct_expand (r : List (Fin 12 × Bool))
    (v : Fin Tag.E7.rank → ℤ) :
    TableBExc.wordAct Tag.E7 (tmW7_expand r) v = tmW7_fastAct r v := by
  induction r generalizing v with
  | nil => rfl
  | cons l r ih =>
      rw [show tmW7_expand (l :: r) = tmW7_xWord l.1 ++ tmW7_expand r from rfl]
      rw [tmW7_wordAct_append, ih v, tmW7_wordAct_eq_mulVec7]
      rfl

private def tmW7_relFast (r : List (Fin 12 × Bool)) : Bool :=
  (List.finRange Tag.E7.rank).all fun j =>
    decide (tmW7_fastAct r (Pi.single j 1) = Pi.single j 1)

private theorem tmW7_relFast_all : (yamakiRels ()).all tmW7_relFast = true := by
  decide +kernel

private theorem tmW7_involCheck :
    ∀ i : Fin 12, ∀ j : Fin Tag.E7.rank,
      tmW7_mulVec7 (tmW7_xMat i) (tmW7_mulVec7 (tmW7_xMat i) (Pi.single j 1)) =
        Pi.single j 1 := by
  decide +kernel

theorem tmW7_x_mul_self (i : Fin 12) : tmW7_x i * tmW7_x i = 1 := by
  apply ext_single
  intro j
  rw [tmW7_x, mul_smul, wordW_smul, wordW_smul, one_smul]
  rw [tmW7_wordAct_eq_mulVec7, tmW7_wordAct_eq_mulVec7]
  exact tmW7_involCheck i j

theorem tmW7_wordW_expand_eq_one (r : List (Fin 12 × Bool)) (hr : r ∈ yamakiRels) :
    wordW Tag.E7 (tmW7_expand r) = 1 := by
  have h := (List.all_eq_true.mp tmW7_relFast_all) r hr
  apply ext_single
  intro j
  rw [wordW_smul, one_smul, tmW7_wordAct_expand]
  exact of_decide_eq_true ((List.all_eq_true.mp h) j (List.mem_finRange j))

theorem tmW7_x_rel (r : List (Fin 12 × Bool)) (hr : r ∈ yamakiRels) :
    FreeGroup.lift tmW7_x (FreeGroup.mk r) = 1 := by
  rw [CFSG.ClassicalInvolution.Solomon73.Yamaki.lift_mk_eq_prod tmW7_x_mul_self r]
  simp only [tmW7_x]
  rw [tmW7_wordW_prod_map]
  exact tmW7_wordW_expand_eq_one r hr

end CFSG.StandardType.FrameRoute

end
