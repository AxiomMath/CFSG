module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5Even7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt
public import CFSG.Quasithin.Background.G6Natural
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.A7M

open Equiv Equiv.Perm CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Setup.SL2Modules Module
open scoped commutatorElement

@[expose] def dList : List (Perm (Fin 7)) :=
  [permOf 7 [], permOf 7 [[2,3],[4,5]], permOf 7 [[0,1],[4,5]], permOf 7 [[0,1],[2,3]],
    permOf 7 [[0,2],[1,3]], permOf 7 [[0,2,1,3],[4,5]], permOf 7 [[0,3,1,2],[4,5]],
    permOf 7 [[0,3],[1,2]]]

theorem dList_checks : (dList.all fun a => dList.all fun b => decide (a * b ∈ dList)) = true ∧
    (dList.all fun a => decide (a⁻¹ ∈ dList)) = true ∧ (1 : Perm (Fin 7)) ∈ dList ∧
    (Even7.tGens.all fun g => decide (g ∈ dList)) = true := by
  decide +kernel

theorem dList_facts : (∀ a ∈ dList, ∀ b ∈ dList, a * b ∈ dList) ∧ (∀ a ∈ dList, a⁻¹ ∈ dList) ∧
    (1 : Perm (Fin 7)) ∈ dList ∧ (∀ g ∈ Even7.tGens, g ∈ dList) := by
  obtain ⟨h1, h2, h3, h4⟩ := dList_checks
  simp only [List.all_eq_true, decide_eq_true_eq] at h1 h2 h4
  exact ⟨h1, h2, h3, h4⟩

theorem dList_words : [[], [1, 0, 1], [0], [0, 1, 0, 1], [1], [0, 1], [1, 0], [0, 1, 0]].map
    (evalW Even7.tGens) = dList := by
  decide +kernel

@[expose] def dSub : Subgroup (Perm (Fin 7)) where
  carrier := {x | x ∈ dList}
  mul_mem' ha hb := dList_facts.1 _ ha _ hb
  one_mem' := dList_facts.2.2.1
  inv_mem' ha := dList_facts.2.1 _ ha

theorem D_eq_dSub : Even7.D = dSub := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    exact fun g hg => dList_facts.2.2.2 g hg
  · intro x hx
    have hx' : x ∈ dList := hx
    rw [← dList_words] at hx'
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hx'
    exact evalW_mem_closure _ w

theorem mem_dList_iff {x : Perm (Fin 7)} : x ∈ Even7.D ↔ x ∈ dList := by
  rw [D_eq_dSub]
  rfl

theorem dList_fix_checks : (dList.all fun d => decide (d 6 = 6)) = true ∧
    ((List.finRange 7).all fun i => !(dList.all fun d => decide (d i = i)) || decide (i = 6)) =
      true := by
  decide +kernel

theorem dList_fix_six : (∀ d ∈ dList, d 6 = 6) ∧ ∀ i : Fin 7, (∀ d ∈ dList, d i = i) → i = 6 := by
  obtain ⟨h1, h2⟩ := dList_fix_checks
  simp only [List.all_eq_true, decide_eq_true_eq] at h1
  refine ⟨h1, fun i hi => ?_⟩
  have := (List.all_eq_true.mp h2) i (List.mem_finRange i)
  simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.all_eq_false,
    decide_eq_true_eq] at this
  rcases this with ⟨d, hd, hne⟩ | h
  · exact absurd (hi d hd) (by simpa using hne)
  · exact h

theorem fix_six_of_mem_normalizer {x : Perm (Fin 7)}
    (hx : x ∈ Subgroup.normalizer (Even7.D : Set (Perm (Fin 7)))) : x 6 = 6 := by
  apply dList_fix_six.2
  intro d hd
  have hdD : d ∈ Even7.D := mem_dList_iff.mpr hd
  have h1 : x⁻¹ * d * x⁻¹⁻¹ ∈ Even7.D :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) d).mp hdD
  have h2 := dList_fix_six.1 _ (mem_dList_iff.mp h1)
  rw [inv_inv] at h2
  have h3 : x⁻¹ (d (x 6)) = 6 := by simpa [Perm.mul_apply] using h2
  have h4 := congrArg x h3
  simpa using h4

@[expose] def trList : List (Perm (Fin 7)) := [swap 0 1, swap 2 3, swap 4 5]

theorem swap_norm_checks : ((List.finRange 7).all fun a => (List.finRange 7).all fun b =>
    !(decide (a ≠ b) && dList.all fun d => decide (swap a b * d * (swap a b)⁻¹ ∈ dList)) ||
    decide (swap a b ∈ trList)) = true := by
  decide +kernel

theorem swap_norm_facts : ∀ a b : Fin 7, a ≠ b →
    (∀ d ∈ dList, swap a b * d * (swap a b)⁻¹ ∈ dList) → swap a b ∈ trList := by
  intro a b hab h
  have := List.all_eq_true.mp (List.all_eq_true.mp swap_norm_checks a (List.mem_finRange a)) b
    (List.mem_finRange b)
  simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_false_imp,
    decide_eq_true_eq] at this
  rcases this with h1 | h1
  · exfalso
    have h2 := h1 hab
    simp only [List.all_eq_false, decide_eq_true_eq] at h2
    obtain ⟨d, hd, hnd⟩ := h2
    exact hnd (h d hd)
  · exact h1

theorem mem_trList_of_mem_normalizer {a b : Fin 7} (hab : a ≠ b)
    (hx : swap a b ∈ Subgroup.normalizer (Even7.D : Set (Perm (Fin 7)))) : swap a b ∈ trList :=
  swap_norm_facts a b hab fun d hd => mem_dList_iff.mp
    ((Subgroup.mem_normalizer_iff.mp hx d).mp (mem_dList_iff.mpr hd))

@[expose] def vc : G6.PermMod 7 := Multiplicative.ofAdd (fun i => if i = 6 then 0 else 1)

theorem vc_mem : vc ∈ G6.coreMod 7 := by
  show ∑ i, Multiplicative.toAdd vc i = 0
  decide +kernel

theorem vc_ne_one : vc ≠ 1 := by
  intro h
  have := congrFun (congrArg Multiplicative.toAdd h) 0
  revert this
  decide +kernel

theorem permAct_vc {σ : Perm (Fin 7)} (hσ : σ 6 = 6) : G6.permAct 7 σ vc = vc := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [G6.permAct_apply]
  simp only [vc, toAdd_ofAdd]
  have : σ⁻¹ i = 6 ↔ i = 6 := by
    constructor
    · intro h
      have e : σ (σ⁻¹ i) = i := by simp
      rw [h, hσ] at e
      exact e.symm
    · rintro rfl
      rw [Perm.inv_eq_iff_eq, hσ]
  simp only [this]

@[expose] def stab4 : Subgroup (Perm (Fin 7)) where
  carrier := {σ | ∀ i : Fin 7, (i : ℕ) < 4 ↔ ((σ i : Fin 7) : ℕ) < 4}
  mul_mem' {σ τ} hσ hτ i := (hτ i).trans (hσ (τ i))
  one_mem' i := Iff.rfl
  inv_mem' {σ} hσ i := by
    have := hσ (σ⁻¹ i)
    have e : σ (σ⁻¹ i) = i := by simp
    rw [e] at this
    exact this.symm

theorem permAct_of_fixD {σ : Perm (Fin 7)} (h6 : σ 6 = 6) (h4 : σ ∈ stab4) {m : G6.PermMod 7}
    (hm : ∀ d ∈ Even7.D, G6.permAct 7 d m = m) : G6.permAct 7 σ m = m := by
  have hg1 := hm _ (Subgroup.subset_closure (show permOf 7 [[0,1],[4,5]] ∈ Even7.tGens by decide))
  have hg2 := hm _ (Subgroup.subset_closure (show permOf 7 [[0,2],[1,3]] ∈ Even7.tGens by decide))
  set v := Multiplicative.toAdd m with hv
  have e1 : ∀ i, v ((permOf 7 [[0,1],[4,5]])⁻¹ i) = v i := fun i => by
    have := congrFun (congrArg Multiplicative.toAdd hg1) i
    rwa [G6.permAct_apply] at this
  have e2 : ∀ i, v ((permOf 7 [[0,2],[1,3]])⁻¹ i) = v i := fun i => by
    have := congrFun (congrArg Multiplicative.toAdd hg2) i
    rwa [G6.permAct_apply] at this
  have hp1 : (permOf 7 [[0,1],[4,5]])⁻¹ 0 = 1 ∧ (permOf 7 [[0,1],[4,5]])⁻¹ 4 = 5 ∧
      (permOf 7 [[0,2],[1,3]])⁻¹ 0 = 2 ∧ (permOf 7 [[0,2],[1,3]])⁻¹ 1 = 3 := by
    decide +kernel
  have c01 : v 1 = v 0 := by have := e1 0; rwa [hp1.1] at this
  have c45 : v 5 = v 4 := by have := e1 4; rwa [hp1.2.1] at this
  have c02 : v 2 = v 0 := by have := e2 0; rwa [hp1.2.2.1] at this
  have c13 : v 3 = v 1 := by have := e2 1; rwa [hp1.2.2.2] at this
  have key : ∀ j k : Fin 7, ((j : ℕ) < 4 ↔ (k : ℕ) < 4) → (j = 6 ↔ k = 6) → v j = v k := by
    intro j k h1 h2
    fin_cases j <;> fin_cases k <;> simp_all
  apply Multiplicative.toAdd.injective
  funext i
  rw [G6.permAct_apply]
  refine key _ _ ?_ ?_
  · have := h4 (σ⁻¹ i)
    have e : σ (σ⁻¹ i) = i := by simp
    rw [e] at this
    exact this
  · constructor
    · intro h
      have e : σ (σ⁻¹ i) = i := by simp
      rw [h, h6] at e
      exact e.symm
    · rintro rfl
      rw [Perm.inv_eq_iff_eq, h6]

theorem member_checks : (Even7.L5.all fun g => decide (g 6 = 6)) = true ∧
    (Even7.L6.all fun g => (List.finRange 7).all fun i =>
      decide ((i : ℕ) < 4 ↔ ((g i : Fin 7) : ℕ) < 4)) = true := by
  decide +kernel

theorem fix_six_of_mem_five {x : Perm (Fin 7)} (hx : x ∈ Even7.Lm 5) : x 6 = 6 := by
  have hle : Even7.Lm 5 ≤ MulAction.stabilizer (Perm (Fin 7)) (6 : Fin 7) := by
    rw [Even7.Lm, show (Even7.cert.tGens :: Even7.cert.lat).getD 5 [] = Even7.L5 from rfl,
      Subgroup.closure_le]
    intro g hg
    have := List.all_eq_true.mp member_checks.1 g hg
    simpa using this
  exact hle hx

theorem six_le_stab4 : Even7.Lm 6 ≤ stab4 := by
  rw [Even7.Lm, show (Even7.cert.tGens :: Even7.cert.lat).getD 6 [] = Even7.L6 from rfl,
    Subgroup.closure_le]
  intro g hg i
  have := List.all_eq_true.mp (List.all_eq_true.mp member_checks.2 g hg) i (List.mem_finRange i)
  simpa using this

theorem words_more_ch615 : [[0], [1], [0, 1, 2, 1, 0, 1, 2, 1, 2]].map (evalW Even7.L8) = Even7.L2 ∧
    [[0], [1], [0, 1, 2, 1, 2, 2, 1, 2, 0]].map (evalW Even7.L10) = Even7.L3 ∧
    [[0], [1], [0, 1, 2, 1, 0, 1, 2, 1, 2]].map (evalW Even7.L9) = Even7.L4 := by
  decide +kernel


theorem le_six_of_gen_ch615 {b : ℕ} (hb1 : 1 ≤ b) (hb6 : b ≤ 6) (hb5 : b ≠ 5)
    (hgen : alternatingGroup (Fin 7) ≤ Even7.Lm 5 ⊔ Even7.Lm b) : Even7.Lm b ≤ Even7.Lm 6 := by
  obtain ⟨h2, h3, h4⟩ := words_more_ch615
  have hbig : ∀ j : ℕ, j < 12 → Even7.Lm 5 ⊔ Even7.Lm b ≤ Even7.Lm j →
      Even7.sizes.getD j 0 < 2520 → False := fun j hj hle hlt => by
    have hc := Subgroup.card_le_of_le (hgen.trans hle)
    rw [Even7.card_alt, Even7.card_Lm_ch615 hj] at hc
    omega
  interval_cases b
  · exact Even7.le_six_ch615 (by norm_num) (by norm_num) (by norm_num)
  · exact (hbig 8 (by norm_num) (sup_le (Even7.five_le_ch615 (by norm_num) (by norm_num))
      (Even7.closure_le_of_words_ch615 _ h2)) (by decide)).elim
  · exact (hbig 10 (by norm_num) (sup_le (Even7.five_le_ch615 (by norm_num) (by norm_num))
      (Even7.closure_le_of_words_ch615 _ h3)) (by decide)).elim
  · exact (hbig 9 (by norm_num) (sup_le (Even7.five_le_ch615 (by norm_num) (by norm_num))
      (Even7.closure_le_of_words_ch615 _ h4)) (by decide)).elim
  · exact absurd rfl hb5
  · exact le_rfl


@[expose] def qList : List (Perm (Fin 7)) :=
  [1, swap 0 1 * swap 4 5, swap 0 1 * swap 2 3, swap 2 3 * swap 4 5]

@[expose] def j1List : List (Perm (Fin 7)) := [swap 0 1, swap 2 3]

theorem q_checks : (qList.all fun a => qList.all fun b => decide (a * b ∈ qList)) = true ∧
    (qList.all fun a => decide (a⁻¹ ∈ qList)) = true ∧
    (qList.all fun a => decide (a * a = 1)) = true ∧
    ((Even7.L5 ++ j1List).all fun g => qList.all fun q => decide (g * q * g⁻¹ ∈ qList)) = true ∧
    (Even7.L5.all fun g => j1List.all fun y => decide (⁅g, y⁆ ∈ qList)) = true := by
  decide +kernel

@[expose] def qSub : Subgroup (Perm (Fin 7)) where
  carrier := {x | x ∈ qList}
  mul_mem' {a b} ha hb := by
    have := List.all_eq_true.mp (List.all_eq_true.mp q_checks.1 a ha) b hb
    simpa using this
  one_mem' := by decide
  inv_mem' {a} ha := by
    have := List.all_eq_true.mp q_checks.2.1 a ha
    simpa using this

theorem sq_of_mem_qSub {x : Perm (Fin 7)} (hx : x ∈ qSub) : x * x = 1 := by
  have := List.all_eq_true.mp q_checks.2.2.1 x hx
  simpa using this

theorem mem_normalizer_of_conj_mem_ch615 {G : Type*} [Group G] [Finite G] {Q : Subgroup G} {g : G}
    (h : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) : g ∈ Subgroup.normalizer (Q : Set G) := by
  classical
  let f : Q → Q := fun r => ⟨g * r * g⁻¹, h r r.2⟩
  have hf : Function.Injective f := fun a b hab => by
    have := congrArg Subtype.val hab
    exact Subtype.ext (by simpa [f] using this)
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => h x hx, fun hx => ?_⟩
  obtain ⟨r, hr⟩ := (Finite.injective_iff_surjective.mp hf) ⟨_, hx⟩
  have hr' : g * r * g⁻¹ = g * x * g⁻¹ := congrArg Subtype.val hr
  have : (r : G) = x := mul_left_cancel (mul_right_cancel hr')
  rw [← this]
  exact r.2

theorem commutator_closure_le_ch615 {G : Type*} [Group G] [Finite G] {s t : Set G}
    {Q : Subgroup G} (hs : ∀ x ∈ s, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q)
    (ht : ∀ y ∈ t, ∀ q ∈ Q, y * q * y⁻¹ ∈ Q) (hst : ∀ x ∈ s, ∀ y ∈ t, ⁅x, y⁆ ∈ Q) :
    ⁅Subgroup.closure s, Subgroup.closure t⁆ ≤ Q := by
  have hsN : Subgroup.closure s ≤ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.closure_le]
    exact fun x hx => mem_normalizer_of_conj_mem_ch615 (hs x hx)
  have htN : Subgroup.closure t ≤ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.closure_le]
    exact fun y hy => mem_normalizer_of_conj_mem_ch615 (ht y hy)
  have hconj : ∀ g ∈ Subgroup.normalizer (Q : Set G), ∀ q ∈ Q, g * q * g⁻¹ ∈ Q :=
    fun g hg q hq => (Subgroup.mem_normalizer_iff.mp hg q).mp hq
  have step1 : ∀ x ∈ Subgroup.closure s, ∀ y ∈ t, ⁅x, y⁆ ∈ Q := by
    intro x hx y hy
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hst x hx y hy
    | one => simp
    | mul a b ha hb iha ihb =>
      have e : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Q.mul_mem (hconj a (hsN ha) _ ihb) iha
    | inv a ha iha =>
      have e : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hconj a⁻¹ (Subgroup.inv_mem _ (hsN ha)) _ (Q.inv_mem iha)
  rw [Subgroup.commutator_le]
  intro x hx y hy
  induction hy using Subgroup.closure_induction with
  | mem y hy => exact step1 x hx y hy
  | one => simp
  | mul a b ha hb iha ihb =>
    have e : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Q.mul_mem iha (hconj a (htN ha) _ ihb)
  | inv a ha iha =>
    have e : ⁅x, a⁻¹⁆ = a⁻¹ * ⁅x, a⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hconj a⁻¹ (Subgroup.inv_mem _ (htN ha)) _ (Q.inv_mem iha)

theorem comm_five_le_qSub :
    ⁅Even7.Lm 5, Subgroup.closure {g | g ∈ j1List}⁆ ≤ qSub := by
  rw [Even7.Lm, show (Even7.cert.tGens :: Even7.cert.lat).getD 5 [] = Even7.L5 from rfl]
  obtain ⟨-, -, -, h4, h5⟩ := q_checks
  refine commutator_closure_le_ch615 (fun x hx q hq => ?_) (fun y hy q hq => ?_)
    (fun x hx y hy => ?_)
  · have := List.all_eq_true.mp (List.all_eq_true.mp h4 x (List.mem_append_left _ hx)) q hq
    have h' : x * q * x⁻¹ ∈ qList := by simpa using this
    exact h'
  · have := List.all_eq_true.mp (List.all_eq_true.mp h4 y (List.mem_append_right _ hy)) q hq
    have h' : y * q * y⁻¹ ∈ qList := by simpa using this
    exact h'
  · have := List.all_eq_true.mp (List.all_eq_true.mp h5 x hx) y hy
    have h' : ⁅x, y⁆ ∈ qList := by simpa using this
    exact h'

theorem map_ofSubtype_alt_ch615 :
    (alternatingGroup {x : Fin 7 // x ≠ 6}).map
        (ofSubtype : Perm {x : Fin 7 // x ≠ 6} →* Perm (Fin 7)) =
      alternatingGroup (Fin 7) ⊓ MulAction.stabilizer (Perm (Fin 7)) (6 : Fin 7) := by
  ext g
  rw [Subgroup.mem_map, Subgroup.mem_inf, mem_alternatingGroup, MulAction.mem_stabilizer_iff,
    Perm.smul_def]
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [mem_alternatingGroup] at hf
    exact ⟨by rw [sign_ofSubtype, hf], ofSubtype_apply_of_not_mem f (not_not.2 rfl)⟩
  · rintro ⟨hsign, hα⟩
    have h₁ : ∀ x, g x ≠ 6 ↔ x ≠ 6 :=
      fun x => not_congr ⟨fun h => g.injective (h.trans hα.symm), fun h => by rw [h, hα]⟩
    have h₂ : ∀ x, g x ≠ x → x ≠ 6 := by
      rintro x hx rfl
      exact hx hα
    refine ⟨subtypePerm g h₁, ?_, ofSubtype_subtypePerm h₁ h₂⟩
    rw [mem_alternatingGroup, ← sign_ofSubtype, ofSubtype_subtypePerm h₁ h₂, hsign]

theorem isSimpleGroup_altStab_ch615 :
    IsSimpleGroup
      ↥(alternatingGroup (Fin 7) ⊓ MulAction.stabilizer (Perm (Fin 7)) (6 : Fin 7)) := by
  have : IsSimpleGroup ↥(alternatingGroup {x : Fin 7 // x ≠ 6}) :=
    alternatingGroup.isSimpleGroup (by simp)
  exact (((alternatingGroup {x : Fin 7 // x ≠ 6}).equivMapOfInjective ofSubtype
    ofSubtype_injective).trans (MulEquiv.subgroupCongr map_ofSubtype_alt_ch615)).symm.isSimpleGroup

theorem altStab_checks : (permOf 7 [[0,1,2]]) ^ 3 = 1 ∧ (permOf 7 [[1,2,3]]) ^ 3 = 1 ∧
    permOf 7 [[0,1,2]] 6 = 6 ∧ permOf 7 [[1,2,3]] 6 = 6 ∧
    permOf 7 [[0,1,2]] * permOf 7 [[1,2,3]] ≠ permOf 7 [[1,2,3]] * permOf 7 [[0,1,2]] := by
  decide +kernel

theorem not_isSolvable_altStab_ch615 :
    ¬ Group.IsSolvable
      ↥(alternatingGroup (Fin 7) ⊓ MulAction.stabilizer (Perm (Fin 7)) (6 : Fin 7)) := by
  have := isSimpleGroup_altStab_ch615
  intro h
  obtain ⟨h1, h2, h3, h4, h5⟩ := altStab_checks
  have hm : ∀ x : Perm (Fin 7), x ^ 3 = 1 → x 6 = 6 →
      x ∈ alternatingGroup (Fin 7) ⊓ MulAction.stabilizer (Perm (Fin 7)) (6 : Fin 7) :=
    fun x hx hx6 => ⟨mem_alternatingGroup.mpr (Even7.sign_eq_one_of_pow_ch615 (k := 1) hx), hx6⟩
  have hc := IsSimpleGroup.comm_iff_isSolvable.mpr h ⟨_, hm _ h1 h3⟩ ⟨_, hm _ h2 h4⟩
  exact h5 (congrArg Subtype.val hc)

theorem le_closure_trList_ch615 {A : Subgroup (Perm (Fin 7))} [CFSG.IsElementaryAbelian 2 ↥A]
    {r : ℕ} (hr : Nat.card ↥A = 2 ^ r)
    (hAN : A ≤ Subgroup.normalizer (Even7.D : Set (Perm (Fin 7))))
    (h : 6 ≤ finrank (ZMod 2) ↥(evenWeight (Fin 7) ⊓ fixedVectors A) + r) :
    A ≤ Subgroup.closure {t | t ∈ trList ∧ t ∈ A} := by
  have hE6 : finrank (ZMod 2) (evenWeight (Fin 7)) = 6 := by
    rw [finrank_evenWeight]
    rfl
  obtain ⟨s, hs2, -, -, hAs, -, -⟩ := even_weight_action_inequality_transpositions
    (Ω := Fin 7) (by decide) A hr (by rw [hE6]; exact h)
  have hgen : {σ : Perm (Fin 7) | ∃ Δ ∈ s, ∃ a ∈ Δ, ∃ b ∈ Δ, a ≠ b ∧ σ = swap a b} ⊆
      {t | t ∈ trList ∧ t ∈ A} := by
    rintro σ ⟨Δ, hΔ, a, ha, b, hb, hab, rfl⟩
    have hσA : swap a b ∈ A := by
      rw [hAs]
      exact Subgroup.subset_closure ⟨Δ, hΔ, a, ha, b, hb, hab, rfl⟩
    exact ⟨mem_trList_of_mem_normalizer hab (hAN hσA), hσA⟩
  calc A = Subgroup.closure {σ : Perm (Fin 7) | ∃ Δ ∈ s, ∃ a ∈ Δ, ∃ b ∈ Δ, a ≠ b ∧ σ = swap a b} :=
        hAs
    _ ≤ Subgroup.closure {t | t ∈ trList ∧ t ∈ A} := Subgroup.closure_mono hgen

end CFSG.Quasithin.H13.A7M
