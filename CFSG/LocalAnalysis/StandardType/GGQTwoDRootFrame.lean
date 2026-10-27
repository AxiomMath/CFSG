module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.StandardType.QTwo

open scoped symmDiff

@[expose] def IsDRootVec {κ : Type} [DecidableEq κ] (v : κ → ZMod 3) : Prop :=
  ∃ i j : κ, i ≠ j ∧ ∃ a b : ZMod 3, (a = 1 ∨ a = -1) ∧ (b = 1 ∨ b = -1) ∧
    v = Pi.single i a + Pi.single j b

private def supp {κ : Type} [Fintype κ] (v : κ → ZMod 3) : Finset κ :=
  Finset.univ.filter fun c => v c ≠ 0

private lemma eq_zero_of_not_mem_supp {κ : Type} [Fintype κ] {v : κ → ZMod 3} {c : κ}
    (h : c ∉ supp v) : v c = 0 := by
  by_contra hc
  exact h (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩)

private def bForm {κ : Type} [Fintype κ] (v w : κ → ZMod 3) : ZMod 3 :=
  ∑ c, v c * w c

private def qForm {κ : Type} [Fintype κ] (v : κ → ZMod 3) : ZMod 3 :=
  bForm v v

private lemma bForm_zero {κ : Type} [Fintype κ] (v : κ → ZMod 3) : bForm v 0 = 0 := by
  simp [bForm]

private lemma bForm_sum {κ : Type} [Fintype κ] {ι' : Type}
    (v : κ → ZMod 3) (s : Finset ι') (f : ι' → κ → ZMod 3) :
    bForm v (∑ a ∈ s, f a) = ∑ a ∈ s, bForm v (f a) := by
  simp only [bForm, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

private lemma bForm_smul {κ : Type} [Fintype κ] (v : κ → ZMod 3) (t : ZMod 3)
    (w : κ → ZMod 3) : bForm v (t • w) = t * bForm v w := by
  simp only [bForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

private lemma bForm_single_single {κ : Type} [Fintype κ] [DecidableEq κ]
    (i j : κ) (a b : ZMod 3) :
    bForm (Pi.single i a) (Pi.single j b) = if i = j then a * b else 0 := by
  rw [bForm, Finset.sum_eq_single i]
  · by_cases h : i = j
    · subst h
      simp
    · simp [h]
  · intro c _ hc
    rw [Pi.single_eq_of_ne hc, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private lemma qForm_single {κ : Type} [Fintype κ] [DecidableEq κ]
    (i : κ) (a : ZMod 3) : qForm (Pi.single i a) = a * a := by
  rw [qForm, bForm_single_single, if_pos rfl]

private lemma sq_eq_one_of_ne_zero (x : ZMod 3) (hx : x ≠ 0) : x * x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl
  · decide

private lemma qForm_add {κ : Type} [Fintype κ] (v w : κ → ZMod 3) :
    qForm (v + w) = qForm v + qForm w + 2 * bForm v w := by
  simp only [qForm, bForm, Pi.add_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  ring

private lemma qForm_sub {κ : Type} [Fintype κ] (v w : κ → ZMod 3) :
    qForm (v - w) = qForm v + qForm w - 2 * bForm v w := by
  simp only [qForm, bForm, Pi.sub_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  ring

private lemma qForm_eq_card_supp {κ : Type} [Fintype κ] [DecidableEq κ]
    (v : κ → ZMod 3) : qForm v = ((supp v).card : ZMod 3) := by
  classical
  have hzero : ∀ c ∈ (Finset.univ : Finset κ), c ∉ supp v → v c * v c = 0 := by
    intro c _ hc
    rw [eq_zero_of_not_mem_supp hc, zero_mul]
  rw [qForm, bForm,
    ← Finset.sum_subset
      (Finset.filter_subset (fun c => v c ≠ 0) (Finset.univ : Finset κ)) hzero]
  rw [Finset.sum_congr rfl (fun c hc =>
    sq_eq_one_of_ne_zero (v c) (Finset.mem_filter.mp hc).2)]
  rw [Finset.sum_const]
  simp only [supp]
  simp

private lemma qForm_eq_two_of_isDRootVec {κ : Type} [Fintype κ] [DecidableEq κ]
    {v : κ → ZMod 3} (hv : IsDRootVec v) : qForm v = 2 := by
  obtain ⟨i, j, hij, a, b, ha, hb, rfl⟩ := hv
  rw [qForm_add, qForm_single i a, qForm_single j b,
    bForm_single_single, if_neg hij]
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

private lemma supp_single_add_single {κ : Type} [Fintype κ] [DecidableEq κ]
    {i j : κ} (hij : i ≠ j) {a b : ZMod 3} (ha : a = 1 ∨ a = -1)
    (hb : b = 1 ∨ b = -1) :
    supp (Pi.single i a + Pi.single j b) = {i, j} := by
  ext c
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    by_contra hc
    have hci : c ≠ i := fun hi => hc (Or.inl hi)
    have hcj : c ≠ j := fun hj => hc (Or.inr hj)
    rw [Pi.single_eq_of_ne hci, Pi.single_eq_of_ne hcj, zero_add] at h
    exact h rfl
  · intro hc
    rcases hc with rfl | rfl
    · have ha0 : a ≠ 0 := by rcases ha with rfl | rfl <;> decide
      simpa [Pi.single_eq_same, Pi.single_eq_of_ne hij] using ha0
    · have hb0 : b ≠ 0 := by rcases hb with rfl | rfl <;> decide
      simpa [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)] using hb0

private lemma card_supp_of_isDRootVec {κ : Type} [Fintype κ] [DecidableEq κ]
    {v : κ → ZMod 3} (hv : IsDRootVec v) : (supp v).card = 2 := by
  obtain ⟨i, j, hij, a, b, ha, hb, rfl⟩ := hv
  rw [supp_single_add_single hij ha hb, Finset.card_pair hij]

private lemma add_sub_indicator (x y : ZMod 3) :
    (if x + y ≠ 0 then (1 : ℕ) else 0) + (if x - y ≠ 0 then 1 else 0) =
      2 * (if (x ≠ 0 ∧ y = 0) ∨ (y ≠ 0 ∧ x = 0) then 1 else 0) +
        (if x ≠ 0 ∧ y ≠ 0 then 1 else 0) := by
  revert x y
  decide

private lemma card_supp_add_sub {κ : Type} [Fintype κ] [DecidableEq κ]
    (v w : κ → ZMod 3) :
    (supp (v + w)).card + (supp (v - w)).card =
      2 * ((supp v) ∆ (supp w)).card + ((supp v) ∩ (supp w)).card := by
  classical
  have hSymm : (supp v) ∆ (supp w) =
      Finset.univ.filter (fun c => (v c ≠ 0 ∧ w c = 0) ∨ (w c ≠ 0 ∧ v c = 0)) := by
    ext c
    simp [supp, Finset.mem_symmDiff]
  have hInter : (supp v) ∩ (supp w) =
      Finset.univ.filter (fun c => v c ≠ 0 ∧ w c ≠ 0) := by
    ext c
    simp [supp]
  rw [hSymm, hInter]
  simp only [supp, Finset.card_filter]
  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  simpa only [Pi.add_apply, Pi.sub_apply] using add_sub_indicator (v c) (w c)

private lemma card_add_eq_card_symmDiff_add_two_card_inter {κ : Type}
    [DecidableEq κ] (A B : Finset κ) :
    A.card + B.card = (A ∆ B).card + 2 * (A ∩ B).card := by
  have hdisj : Disjoint (A \ B) (B \ A) :=
    (Finset.disjoint_sdiff (s := B) (t := A)).symm.mono_right Finset.sdiff_subset
  have h1 : (A ∆ B).card = (A \ B).card + (B \ A).card := by
    rw [Finset.symmDiff_def]
    exact Finset.card_union_of_disjoint hdisj
  have h2 : A.card = (A \ B).card + (A ∩ B).card :=
    (Finset.card_sdiff_add_card_inter A B).symm
  have h3 : B.card = (B \ A).card + (A ∩ B).card := by
    rw [Finset.inter_comm A B]
    exact (Finset.card_sdiff_add_card_inter B A).symm
  omega

private lemma support_case_arith {κ : Type} [DecidableEq κ] {A B : Finset κ}
    (hA : A.card = 1 ∨ A.card = 4) (hB : B.card = 1 ∨ B.card = 4)
    (h : 2 * (A ∆ B).card + (A ∩ B).card = 4) :
    (A.card = 1 ∧ B.card = 1 ∧ Disjoint A B) ∨
    (A.card = 4 ∧ B.card = 4 ∧ A = B) := by
  have h2 : A.card + B.card = (A ∆ B).card + 2 * (A ∩ B).card :=
    card_add_eq_card_symmDiff_add_two_card_inter A B
  have hleA : (A ∩ B).card ≤ A.card := Finset.card_le_card Finset.inter_subset_left
  have hleB : (A ∩ B).card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · refine Or.inl ⟨hA, hB, ?_⟩
    have hr : (A ∩ B).card = 0 := by omega
    rw [Finset.disjoint_iff_inter_eq_empty]
    exact Finset.card_eq_zero.mp hr
  · omega
  · omega
  · refine Or.inr ⟨hA, hB, ?_⟩
    have hr : (A ∩ B).card = 4 := by omega
    exact (Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)).symm.trans
      (Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega))

private lemma exists_fin_five_ne (i j : Fin 5) :
    ∃ k : Fin 5, k ≠ i ∧ k ≠ j := by
  revert i j
  decide

private lemma exists_ne_ne_of_card_eq_five {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = 5) (a b : ι) : ∃ c : ι, c ≠ a ∧ c ≠ b := by
  let e : ι ≃ Fin 5 := Fintype.equivFinOfCardEq hι
  obtain ⟨k, hki, hkj⟩ := exists_fin_five_ne (e a) (e b)
  exact ⟨e.symm k, fun h => hki (by simpa using congrArg e h),
    fun h => hkj (by simpa using congrArg e h)⟩

private lemma eq_one_or_neg_one_of_ne_zero {x : ZMod 3} (hx : x ≠ 0) :
    x = 1 ∨ x = -1 := by
  revert hx
  revert x
  decide

private lemma eq_single_of_supp_eq_singleton {κ : Type} [Fintype κ] [DecidableEq κ]
    {v : κ → ZMod 3} {c : κ} (h : supp v = {c}) : v = Pi.single c (v c) := by
  funext x
  by_cases hx : x = c
  · subst hx
    simp
  · have hxS : x ∉ supp v := by
      rw [h]
      simp [hx]
    rw [eq_zero_of_not_mem_supp hxS, Pi.single_eq_of_ne hx]

private lemma qForm_add_eq_two_of_isDRootVec {κ : Type} [Fintype κ] [DecidableEq κ]
    {v w : κ → ZMod 3} (h₁ : IsDRootVec (v + w)) (h₂ : IsDRootVec (v - w)) :
    qForm v + qForm w = 2 := by
  have h1 : qForm (v + w) = 2 := qForm_eq_two_of_isDRootVec h₁
  have h2 : qForm (v - w) = 2 := qForm_eq_two_of_isDRootVec h₂
  have h3 : qForm (v + w) + qForm (v - w) = 2 * (qForm v + qForm w) := by
    rw [qForm_add, qForm_sub]
    ring
  rw [h1, h2] at h3
  have h4 : (2 : ZMod 3) * (qForm v + qForm w) = 1 := by
    rw [← h3]
    decide
  have haux : ∀ x : ZMod 3, (2 : ZMod 3) * x = 1 → x = 2 := by decide
  exact haux _ h4

private lemma eq_one_of_pair_add_eq_two {ι : Type*} [Fintype ι] {q : ι → ZMod 3}
    (hι : Fintype.card ι = 5) (hpair : ∀ a b : ι, a ≠ b → q a + q b = 2) :
    ∀ a : ι, q a = 1 := by
  have hconst : ∀ a b : ι, q a = q b := by
    intro a b
    by_cases hab : a = b
    · subst hab
      rfl
    · obtain ⟨c, hca, hcb⟩ := exists_ne_ne_of_card_eq_five hι a b
      have h1 : q a + q c = 2 := hpair a c hca.symm
      have h2 : q b + q c = 2 := hpair b c hcb.symm
      calc q a = q a + q c - q c := by ring
        _ = q b + q c - q c := by rw [h1, h2]
        _ = q b := by ring
  intro a
  obtain ⟨b, hba⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card ι) a
  have h2 : q a + q b = 2 := hpair a b hba.symm
  rw [← hconst a b] at h2
  have h3 : (2 : ZMod 3) * q a = 2 := by
    simpa [two_mul] using h2
  have haux : ∀ x : ZMod 3, (2 : ZMod 3) * x = 2 → x = 1 := by decide
  exact haux _ h3

private lemma bForm_eq_zero_of_isDRootVec_add_sub {κ : Type} [Fintype κ] [DecidableEq κ]
    {v w : κ → ZMod 3} (h₁ : IsDRootVec (v + w)) (h₂ : IsDRootVec (v - w)) :
    bForm v w = 0 := by
  have h1 : qForm (v + w) = 2 := qForm_eq_two_of_isDRootVec h₁
  have h2 : qForm (v - w) = 2 := qForm_eq_two_of_isDRootVec h₂
  have h3 : qForm (v + w) - qForm (v - w) = 4 * bForm v w := by
    rw [qForm_add, qForm_sub]
    ring
  rw [h1, h2] at h3
  have h4 : (4 : ZMod 3) * bForm v w = 0 := by
    rw [← h3]
    decide
  rwa [show (4 : ZMod 3) = 1 by decide, one_mul] at h4

private lemma linearIndependent_of_pair_bForm_eq_zero {ι κ : Type} [Fintype ι] [Fintype κ]
    {u : ι → κ → ZMod 3} (horth : ∀ a b : ι, a ≠ b → bForm (u a) (u b) = 0)
    (hnorm : ∀ a : ι, qForm (u a) = 1) : LinearIndependent (ZMod 3) u := by
  rw [linearIndependent_iff']
  intro s t hst b hb
  have hpair := congrArg (bForm (u b)) hst
  simp only [bForm_sum, bForm_smul, bForm_zero] at hpair
  rw [Finset.sum_eq_single b] at hpair
  · have hq : bForm (u b) (u b) = 1 := by simpa [qForm] using hnorm b
    rw [hq, mul_one] at hpair
    exact hpair
  · intro a _ hne
    rw [horth b a hne.symm, mul_zero]
  · intro hb'
    exact absurd hb hb'

private lemma card_eq_five_of_linearIndependent {ι κ : Type} [Fintype ι] [Fintype κ]
    {u : ι → κ → ZMod 3} (hι : Fintype.card ι = 5) (hκ : Fintype.card κ ≤ 5)
    (hli : LinearIndependent (ZMod 3) u) : Fintype.card κ = 5 := by
  have hcard := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, hι] at hcard
  omega

private lemma card_supp_eq_one_or_four {κ : Type} [Fintype κ] [DecidableEq κ]
    {v : κ → ZMod 3} (hq : qForm v = 1) (hcard : Fintype.card κ = 5) :
    (supp v).card = 1 ∨ (supp v).card = 4 := by
  have hcast : ((supp v).card : ZMod 3) = 1 := by
    rw [← qForm_eq_card_supp, hq]
  have hle : (supp v).card ≤ 5 := by
    calc (supp v).card ≤ Fintype.card κ := Finset.card_le_univ _
      _ = 5 := hcard
  set n : ℕ := (supp v).card with hn
  have hcast' : (n : ZMod 3) = 1 := by rw [hn]; exact hcast
  have hle' : n ≤ 5 := by rw [hn]; exact hle
  interval_cases n
  · exact absurd hcast' (by decide)
  · exact Or.inl rfl
  · exact absurd hcast' (by decide)
  · exact absurd hcast' (by decide)
  · exact Or.inr rfl
  · exact absurd hcast' (by decide)

private lemma supp_disjoint_or_eq_of_isDRootVec_add_sub {κ : Type} [Fintype κ]
    [DecidableEq κ] {v w : κ → ZMod 3} (hv : (supp v).card = 1 ∨ (supp v).card = 4)
    (hw : (supp w).card = 1 ∨ (supp w).card = 4)
    (h₁ : IsDRootVec (v + w)) (h₂ : IsDRootVec (v - w)) :
    ((supp v).card = 1 ∧ (supp w).card = 1 ∧ Disjoint (supp v) (supp w)) ∨
      ((supp v).card = 4 ∧ (supp w).card = 4 ∧ supp v = supp w) := by
  have hcard := card_supp_add_sub v w
  rw [card_supp_of_isDRootVec h₁, card_supp_of_isDRootVec h₂] at hcard
  have h : 2 * ((supp v) ∆ (supp w)).card + ((supp v) ∩ (supp w)).card = 4 := by
    omega
  exact support_case_arith hv hw h

private lemma linearIndependent_restrict_of_supp_subset {ι κ : Type} [Fintype κ]
    {u : ι → κ → ZMod 3} {S : Finset κ} (hli : LinearIndependent (ZMod 3) u)
    (hS : ∀ b : ι, supp (u b) ⊆ S) :
    LinearIndependent (ZMod 3) (fun b : ι => fun c : ↥S => u b c) := by
  classical
  rw [linearIndependent_iff'] at hli
  rw [linearIndependent_iff']
  intro s t hst b hb
  apply hli s t ?_ b hb
  funext c
  by_cases hc : c ∈ S
  · have hpt := congrFun hst ⟨c, hc⟩
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hpt
  · have hzero : ∀ x : ι, u x c = 0 := by
      intro x
      exact eq_zero_of_not_mem_supp (fun hmem => hc (hS x hmem))
    simp [Finset.sum_apply, Pi.smul_apply, hzero]

private lemma not_exists_card_supp_eq_four {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq κ] {u : ι → κ → ZMod 3} (hι : Fintype.card ι = 5)
    (hli : LinearIndependent (ZMod 3) u)
    (hsupp : ∀ a : ι, (supp (u a)).card = 1 ∨ (supp (u a)).card = 4)
    (hcases : ∀ a b : ι, a ≠ b →
      ((supp (u a)).card = 1 ∧ (supp (u b)).card = 1 ∧
        Disjoint (supp (u a)) (supp (u b))) ∨
      ((supp (u a)).card = 4 ∧ (supp (u b)).card = 4 ∧
        supp (u a) = supp (u b))) :
    ¬ ∃ a : ι, (supp (u a)).card = 4 := by
  rintro ⟨a0, ha0⟩
  let S : Finset κ := supp (u a0)
  have hS_card : S.card = 4 := ha0
  have hsupp_eq : ∀ b : ι, supp (u b) = S := by
    intro b
    by_cases hb : b = a0
    · subst hb
      rfl
    · rcases hcases a0 b (Ne.symm hb) with ⟨h1a, _, _⟩ | ⟨_, _, heq⟩
      · omega
      · exact heq.symm
  have hliS : LinearIndependent (ZMod 3) (fun b : ι => fun c : ↥S => u b c) :=
    linearIndependent_restrict_of_supp_subset hli
      (fun b => by rw [hsupp_eq b])
  have hdim : Module.finrank (ZMod 3) (↥S → ZMod 3) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, hS_card]
  have hle : Fintype.card ι ≤ 4 := by
    have h := hliS.fintype_card_le_finrank
    rwa [hdim] at h
  omega

private lemma exists_forall_supp_eq_singleton {ι κ : Type} [Fintype κ] [DecidableEq κ]
    {u : ι → κ → ZMod 3} (hsupp_one : ∀ a : ι, (supp (u a)).card = 1) :
    ∃ πfun : ι → κ, ∀ a : ι, supp (u a) = {πfun a} :=
  ⟨fun a => (Finset.card_eq_one.mp (hsupp_one a)).choose,
    fun a => (Finset.card_eq_one.mp (hsupp_one a)).choose_spec⟩

private lemma injective_of_forall_supp_eq_singleton {ι κ : Type} [Fintype κ]
    [DecidableEq κ] {u : ι → κ → ZMod 3}
    (hsupp_one : ∀ a : ι, (supp (u a)).card = 1)
    (hcases : ∀ a b : ι, a ≠ b →
      ((supp (u a)).card = 1 ∧ (supp (u b)).card = 1 ∧
        Disjoint (supp (u a)) (supp (u b))) ∨
      ((supp (u a)).card = 4 ∧ (supp (u b)).card = 4 ∧
        supp (u a) = supp (u b)))
    {πfun : ι → κ} (hπ_spec : ∀ a : ι, supp (u a) = {πfun a}) :
    Function.Injective πfun := by
  intro a b hab
  by_contra hne
  rcases hcases a b hne with ⟨_, _, hdisj⟩ | ⟨h4a, _, _⟩
  · have hempty : supp (u a) ∩ supp (u b) = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.mp hdisj
    have hmem : πfun b ∈ supp (u a) ∩ supp (u b) := by
      rw [hπ_spec a, hπ_spec b, hab]
      simp
    rw [hempty] at hmem
    simpa using hmem
  · rw [hsupp_one a] at h4a
    omega

private lemma exists_equiv_of_forall_supp_eq_singleton {ι κ : Type} [Fintype ι]
    [Fintype κ] [DecidableEq κ] {u : ι → κ → ZMod 3} (hι : Fintype.card ι = 5)
    (hcardκ : Fintype.card κ = 5)
    (hsupp_one : ∀ a : ι, (supp (u a)).card = 1)
    (hcases : ∀ a b : ι, a ≠ b →
      ((supp (u a)).card = 1 ∧ (supp (u b)).card = 1 ∧
        Disjoint (supp (u a)) (supp (u b))) ∨
      ((supp (u a)).card = 4 ∧ (supp (u b)).card = 4 ∧
        supp (u a) = supp (u b))) :
    ∃ (π : ι ≃ κ) (s : ι → ZMod 3), (∀ a, s a = 1 ∨ s a = -1) ∧
      ∀ a, u a = Pi.single (π a) (s a) := by
  obtain ⟨πfun, hπ_spec⟩ := exists_forall_supp_eq_singleton hsupp_one
  have hπ_inj : Function.Injective πfun :=
    injective_of_forall_supp_eq_singleton hsupp_one hcases hπ_spec
  have hbij : Function.Bijective πfun :=
    (Fintype.bijective_iff_injective_and_card πfun).mpr
      ⟨hπ_inj, by rw [hι, hcardκ]⟩
  let π : ι ≃ κ := Equiv.ofBijective πfun hbij
  let s : ι → ZMod 3 := fun a => u a (πfun a)
  have hs : ∀ a : ι, s a = 1 ∨ s a = -1 := by
    intro a
    apply eq_one_or_neg_one_of_ne_zero
    have hmem : πfun a ∈ supp (u a) := by
      rw [hπ_spec a]
      simp
    exact (Finset.mem_filter.mp hmem).2
  refine ⟨π, s, hs, ?_⟩
  intro a
  have hu : u a = Pi.single (πfun a) (s a) :=
    eq_single_of_supp_eq_singleton (hπ_spec a)
  simpa [π] using hu

theorem exists_equiv_of_isDRootVec_add_sub {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (hι : Fintype.card ι = 5) (hκ : Fintype.card κ ≤ 5) (u : ι → κ → ZMod 3)
    (h : ∀ a b, a ≠ b → IsDRootVec (u a + u b) ∧ IsDRootVec (u a - u b)) :
    ∃ (π : ι ≃ κ) (s : ι → ZMod 3), (∀ a, s a = 1 ∨ s a = -1) ∧
      ∀ a, u a = Pi.single (π a) (s a) := by
  classical
  have hqsum : ∀ a b : ι, a ≠ b → qForm (u a) + qForm (u b) = 2 := fun a b hab =>
    qForm_add_eq_two_of_isDRootVec (h a b hab).1 (h a b hab).2
  have hqone : ∀ a : ι, qForm (u a) = 1 := eq_one_of_pair_add_eq_two hι hqsum
  have hBorth : ∀ a b : ι, a ≠ b → bForm (u a) (u b) = 0 := fun a b hab =>
    bForm_eq_zero_of_isDRootVec_add_sub (h a b hab).1 (h a b hab).2
  have hli : LinearIndependent (ZMod 3) u :=
    linearIndependent_of_pair_bForm_eq_zero hBorth hqone
  have hcardκ : Fintype.card κ = 5 := card_eq_five_of_linearIndependent hι hκ hli
  have hsupp : ∀ a : ι, (supp (u a)).card = 1 ∨ (supp (u a)).card = 4 := fun a =>
    card_supp_eq_one_or_four (hqone a) hcardκ
  have hcases : ∀ a b : ι, a ≠ b →
      ((supp (u a)).card = 1 ∧ (supp (u b)).card = 1 ∧
        Disjoint (supp (u a)) (supp (u b))) ∨
      ((supp (u a)).card = 4 ∧ (supp (u b)).card = 4 ∧
        supp (u a) = supp (u b)) := fun a b hab =>
    supp_disjoint_or_eq_of_isDRootVec_add_sub (hsupp a) (hsupp b)
      (h a b hab).1 (h a b hab).2
  have hno4 : ¬ ∃ a : ι, (supp (u a)).card = 4 :=
    not_exists_card_supp_eq_four hι hli hsupp hcases
  have hsupp_one : ∀ a : ι, (supp (u a)).card = 1 := by
    intro a
    rcases hsupp a with h1 | h4
    · exact h1
    · exact absurd ⟨a, h4⟩ hno4
  exact exists_equiv_of_forall_supp_eq_singleton hι hcardκ hsupp_one hcases

end CFSG.StandardType.QTwo
