module

public import CFSG.LocalAnalysis.StandardType.FS81.SpMatAlg
public import CFSG.LocalAnalysis.StandardType.FS81.N7MainBasic

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

variable {k : ℕ}

@[expose] def coordRefl (a : Fin k) : Matrix (Fin k) (Fin k) (ZMod 3) :=
  spMat 1 fun i => if i = a then -1 else 1

@[expose] def swapRefl (a b : Fin k) (δ : ZMod 3) : Matrix (Fin k) (Fin k) (ZMod 3) :=
  spMat (Equiv.swap a b) fun l => if l = a ∨ l = b then δ else 1

theorem coordRefl_mulVec (a : Fin k) (v : Fin k → ZMod 3) :
    coordRefl a *ᵥ v = fun i => if i = a then -v i else v i := by
  funext i
  rw [coordRefl, spMat_mulVec]
  change (if i = a then -1 else 1) * v i = (if i = a then -v i else v i)
  by_cases h : i = a
  · subst h
    rw [if_pos rfl, if_pos rfl]
    exact neg_one_mul (v i)
  · simp [h]

theorem swapRefl_symm (a b : Fin k) (δ : ZMod 3) : swapRefl b a δ = swapRefl a b δ := by
  unfold swapRefl
  rw [Equiv.swap_comm]
  congr 1
  funext l
  simp [or_comm]

theorem coordRefl_mul_self (a : Fin k) : coordRefl a * coordRefl a = 1 := by
  rw [coordRefl]
  refine spMat_mul_self 1 _ (by simp) fun j => ?_
  change (if j = a then -1 else 1) * (if j = a then -1 else 1) = 1
  by_cases h : j = a
  · subst j
    rw [if_pos rfl]
    decide
  · simp [h]

theorem coordRefl_ne_one (a : Fin k) : coordRefl a ≠ 1 := by
  intro h
  have e : (-1 : ZMod 3) = 1 := by
    simpa [coordRefl, spMat_apply] using congrFun (congrFun h a) a
  revert e
  decide

theorem coordRefl_injective :
    Function.Injective (coordRefl : Fin k → Matrix (Fin k) (Fin k) (ZMod 3)) := by
  intro a b h
  by_contra hab
  have e : coordRefl a a a = coordRefl b a a := by rw [h]
  simp [coordRefl, spMat_apply, hab] at e
  revert e
  decide

theorem coordRefl_ne_swapRefl {a b : Fin k} (hab : a ≠ b) (c : Fin k) (δ : ZMod 3) :
    coordRefl c ≠ swapRefl a b δ := by
  intro h
  have e : coordRefl c a a = swapRefl a b δ a a := by rw [h]
  rw [coordRefl, swapRefl, spMat_apply, spMat_apply, Equiv.swap_apply_left, if_neg hab] at e
  simp only [Equiv.Perm.one_apply] at e
  by_cases hca : a = c <;> simp [hca] at e <;> revert e <;> decide

theorem swapRefl_ne_neg {a b : Fin k} (hab : a ≠ b) {δ : ZMod 3} (hδ : δ ≠ 0) :
    swapRefl a b δ ≠ swapRefl a b (-δ) := by
  intro h
  have e : δ = -δ := by
    simpa [swapRefl, spMat_apply, Equiv.swap_apply_left] using congrFun (congrFun h b) a
  rcases eq_one_or_of_ne_zero hδ with h1 | h1 <;> rw [h1] at e <;> revert e <;> decide

private theorem monoRefl_axis_coord {a b : Fin k} {δ : ZMod 3} (i : Fin k) :
    (Pi.single a 1 - δ • Pi.single b 1 : Fin k → ZMod 3) i =
      (if i = a then 1 else 0) - δ * (if i = b then 1 else 0) := by
  simp [Pi.sub_apply, Pi.smul_apply, Pi.single_apply]

theorem swapRefl_eq_of_axis {a b c d : Fin k} (hab : a ≠ b) (hcd : c ≠ d) {δ ε γ : ZMod 3}
    (hδ : δ ≠ 0) (hε : ε ≠ 0)
    (h : Pi.single a 1 - δ • Pi.single b 1 = γ • (Pi.single c 1 - ε • Pi.single d 1)) :
    swapRefl a b δ = swapRefl c d ε := by
  have hγ : γ ≠ 0 := by
    intro hγ0
    have e := congrFun h a
    rw [monoRefl_axis_coord, Pi.smul_apply, smul_eq_mul, monoRefl_axis_coord] at e
    simp only [if_true, if_false, if_neg hab, hγ0, zero_mul, mul_zero, sub_zero] at e
    revert e
    decide
  have hc : c = a ∨ c = b := by
    by_contra hc
    rw [not_or] at hc
    have e := congrFun h c
    rw [monoRefl_axis_coord, Pi.smul_apply, smul_eq_mul, monoRefl_axis_coord] at e
    simp only [if_true, if_false, if_neg hc.1, if_neg hc.2, if_neg hcd, mul_zero,
      sub_zero, mul_one, zero_mul] at e
    rcases eq_one_or_of_ne_zero hγ with h1 | h1 <;> rw [h1] at e <;> revert e <;> decide
  have hd : d = a ∨ d = b := by
    by_contra hd
    rw [not_or] at hd
    have e := congrFun h d
    rw [monoRefl_axis_coord, Pi.smul_apply, smul_eq_mul, monoRefl_axis_coord] at e
    simp only [if_true, if_false, if_neg hd.1, if_neg hd.2, if_neg (Ne.symm hcd),
      mul_zero, sub_zero, mul_one, mul_neg, zero_mul] at e
    rcases eq_one_or_of_ne_zero hγ with h1 | h1 <;>
      rcases eq_one_or_of_ne_zero hε with h2 | h2 <;>
      rw [h1, h2] at e <;> revert e <;> decide
  rcases hc with hca | hcb <;> rcases hd with hda | hdb
  · exact absurd (hca.trans hda.symm) hcd
  · subst c
    subst d
    have h1 : γ = 1 := by
      have e := congrFun h a
      rw [monoRefl_axis_coord, Pi.smul_apply, smul_eq_mul, monoRefl_axis_coord] at e
      simp only [if_true, if_false, if_neg hab, mul_zero, sub_zero, mul_one] at e
      rcases eq_one_or_of_ne_zero hγ with h2 | h2 <;> rw [h2] at e ⊢ <;>
        revert e <;> decide
    have h2 : δ = ε := by
      have e := congrFun h b
      rw [monoRefl_axis_coord, Pi.smul_apply, smul_eq_mul, monoRefl_axis_coord] at e
      rw [h1] at e
      simp only [if_true, if_false, if_neg (Ne.symm hab), mul_zero, sub_zero,
        mul_one] at e
      rcases eq_one_or_of_ne_zero hδ with h2 | h2 <;>
        rcases eq_one_or_of_ne_zero hε with h3 | h3 <;>
        rw [h2, h3] at e ⊢ <;> revert e <;> decide
    rw [h2]
  · subst c
    subst d
    rw [swapRefl_symm]
    have h1 : γ = -δ := by
      have e := congrFun h b
      rw [monoRefl_axis_coord, Pi.smul_apply, smul_eq_mul, monoRefl_axis_coord] at e
      simp only [if_true, if_false, if_neg hab, if_neg (Ne.symm hab), mul_zero,
        sub_zero, mul_one] at e
      rcases eq_one_or_of_ne_zero hγ with h2 | h2 <;>
        rcases eq_one_or_of_ne_zero hδ with h3 | h3 <;>
        rw [h2, h3] at e ⊢ <;> revert e <;> decide
    have h2 : δ * ε = 1 := by
      have e := congrFun h a
      rw [monoRefl_axis_coord, Pi.smul_apply, smul_eq_mul, monoRefl_axis_coord, h1] at e
      simp only [if_true, if_false, if_neg hab, mul_zero, sub_zero, mul_one,
        neg_mul, neg_neg] at e
      rcases eq_one_or_of_ne_zero hδ with h2 | h2 <;>
        rcases eq_one_or_of_ne_zero hε with h3 | h3 <;>
        rw [h2, h3] at e ⊢ <;> revert e <;> decide
    have h3 : ε = δ := by
      refine mul_left_cancel₀ hδ ?_
      rw [h2, mul_self_of_ne_zero hδ]
    rw [h3]
  · exact absurd (hcb.trans hdb.symm) hcd

theorem coordRefl_commute (a b : Fin k) : Commute (coordRefl a) (coordRefl b) := by
  show coordRefl a * coordRefl b = coordRefl b * coordRefl a
  rw [coordRefl, coordRefl, spMat_mul, spMat_mul]
  simp only [mul_one]
  congr 1
  funext j
  change (if j = a then -1 else 1) * (if j = b then -1 else 1) =
    (if j = b then -1 else 1) * (if j = a then -1 else 1)
  rw [mul_comm]

private theorem monoRefl_coord_mul_swap_apply (c a b : Fin k) (δ : ZMod 3) (j : Fin k) :
    (coordRefl c * swapRefl a b δ) (Equiv.swap a b j) j =
      (if Equiv.swap a b j = c then -1 else 1) *
        (if j = a ∨ j = b then δ else 1) := by
  rw [coordRefl, swapRefl, spMat_mul]
  simp only [one_mul, spMat_apply, if_pos rfl, if_true, if_false, Equiv.Perm.one_apply]

private theorem monoRefl_swap_mul_coord_apply (c a b : Fin k) (δ : ZMod 3) (j : Fin k) :
    (swapRefl a b δ * coordRefl c) (Equiv.swap a b j) j =
      (if j = a ∨ j = b then δ else 1) * (if j = c then -1 else 1) := by
  rw [coordRefl, swapRefl, spMat_mul, mul_one, spMat_apply, if_pos rfl]
  change (if j = a ∨ j = b then δ else 1) * (if j = c then -1 else 1) =
    (if j = a ∨ j = b then δ else 1) * (if j = c then -1 else 1)
  rfl

theorem coordRefl_commute_swapRefl_iff {a b : Fin k} (hab : a ≠ b) {δ : ZMod 3} (hδ : δ ≠ 0)
    (c : Fin k) : Commute (coordRefl c) (swapRefl a b δ) ↔ c ≠ a ∧ c ≠ b := by
  constructor
  · intro hcomm
    constructor
    · intro hca
      subst c
      have e := congrFun (congrFun hcomm.eq (Equiv.swap a b a)) a
      rw [monoRefl_coord_mul_swap_apply, monoRefl_swap_mul_coord_apply] at e
      simp [hab, Ne.symm hab] at e
      rcases eq_one_or_of_ne_zero hδ with h1 | h1 <;> rw [h1] at e <;>
        revert e <;> decide
    · intro hcb
      subst c
      have e := congrFun (congrFun hcomm.eq (Equiv.swap a b a)) a
      rw [monoRefl_coord_mul_swap_apply, monoRefl_swap_mul_coord_apply] at e
      simp [hab, Ne.symm hab] at e
      rcases eq_one_or_of_ne_zero hδ with h1 | h1 <;> rw [h1] at e <;>
        revert e <;> decide
  · rintro ⟨hca, hcb⟩
    show coordRefl c * swapRefl a b δ = swapRefl a b δ * coordRefl c
    rw [coordRefl, swapRefl, spMat_mul, spMat_mul]
    simp only [one_mul, mul_one]
    congr 1
    funext j
    change (if Equiv.swap a b j = c then -1 else 1) *
        (if j = a ∨ j = b then δ else 1) =
      (if j = a ∨ j = b then δ else 1) * (if j = c then -1 else 1)
    by_cases hja : j = a
    · subst j
      simp [Equiv.swap_apply_left, Ne.symm hca, Ne.symm hcb]
    · by_cases hjb : j = b
      · subst j
        simp [Equiv.swap_apply_right, Ne.symm hca, Ne.symm hcb]
      · rw [Equiv.swap_apply_of_ne_of_ne hja hjb]
        by_cases hjc : j = c
        · subst j
          simp [hca, hcb]
        · simp [hja, hjb, hjc]

private theorem monoRefl_swapRefl_not_commute {a b d : Fin k} (hab : a ≠ b) (had : a ≠ d)
    (hbd : b ≠ d) {δ ε : ZMod 3} (hδ : δ ≠ 0) (hε : ε ≠ 0) :
    ¬ Commute (swapRefl a b δ) (swapRefl a d ε) := by
  intro hcomm
  have e := congrFun (congrFun hcomm.eq b) d
  rw [swapRefl, swapRefl, spMat_mul, spMat_mul, spMat_apply, spMat_apply] at e
  simp [Equiv.swap_apply_def, hab, had, hbd, Ne.symm hab, Ne.symm had, Ne.symm hbd] at e
  rcases eq_one_or_of_ne_zero hδ with h1 | h1 <;>
    rcases eq_one_or_of_ne_zero hε with h2 | h2 <;>
    rw [h1, h2] at e <;> revert e <;> decide

private theorem monoRefl_commute_same (a b : Fin k) (δ ε : ZMod 3) :
    Commute (swapRefl a b δ) (swapRefl a b ε) := by
  show swapRefl a b δ * swapRefl a b ε = swapRefl a b ε * swapRefl a b δ
  have hδ : (fun l => if l = a ∨ l = b then δ else 1) ∘ Equiv.swap a b =
      (fun l => if l = a ∨ l = b then δ else 1) := by
    funext l
    change (if Equiv.swap a b l = a ∨ Equiv.swap a b l = b then δ else 1) =
      (if l = a ∨ l = b then δ else 1)
    by_cases hla : l = a
    · subst l; simp [Equiv.swap_apply_left]
    · by_cases hlb : l = b
      · subst l; simp [Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne hla hlb]
  have hε : (fun l => if l = a ∨ l = b then ε else 1) ∘ Equiv.swap a b =
      (fun l => if l = a ∨ l = b then ε else 1) := by
    funext l
    change (if Equiv.swap a b l = a ∨ Equiv.swap a b l = b then ε else 1) =
      (if l = a ∨ l = b then ε else 1)
    by_cases hla : l = a
    · subst l; simp [Equiv.swap_apply_left]
    · by_cases hlb : l = b
      · subst l; simp [Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne hla hlb]
  rw [swapRefl, swapRefl, spMat_mul, spMat_mul, Equiv.swap_mul_self]
  congr 1
  funext j
  have hδj : (if Equiv.swap a b j = a ∨ Equiv.swap a b j = b then δ else 1) =
      (if j = a ∨ j = b then δ else 1) := by simpa using congrFun hδ j
  have hεj : (if Equiv.swap a b j = a ∨ Equiv.swap a b j = b then ε else 1) =
      (if j = a ∨ j = b then ε else 1) := by simpa using congrFun hε j
  rw [hδj, hεj, mul_comm]

private theorem monoRefl_commute_disjoint {a b c d : Fin k} (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (δ ε : ZMod 3) :
    Commute (swapRefl a b δ) (swapRefl c d ε) := by
  show swapRefl a b δ * swapRefl c d ε = swapRefl c d ε * swapRefl a b δ
  have hperm : Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b := by
    have hca : Equiv.swap c d a = a := Equiv.swap_apply_of_ne_of_ne hac had
    have hcb : Equiv.swap c d b = b := Equiv.swap_apply_of_ne_of_ne hbc hbd
    rw [Equiv.mul_swap_eq_swap_mul (Equiv.swap c d) a b, hca, hcb]
  have hδ : (fun l => if l = a ∨ l = b then δ else 1) ∘ Equiv.swap c d =
      (fun l => if l = a ∨ l = b then δ else 1) := by
    funext l
    change (if Equiv.swap c d l = a ∨ Equiv.swap c d l = b then δ else 1) =
      (if l = a ∨ l = b then δ else 1)
    refine Equiv.apply_swap_eq_self
      (v := fun l => if l = a ∨ l = b then δ else 1) ?_ l
    rw [if_neg (by
        rintro (h | h)
        · exact hac h.symm
        · exact hbc h.symm),
      if_neg (by
        rintro (h | h)
        · exact had h.symm
        · exact hbd h.symm)]
  have hε : (fun l => if l = c ∨ l = d then ε else 1) ∘ Equiv.swap a b =
      (fun l => if l = c ∨ l = d then ε else 1) := by
    funext l
    change (if Equiv.swap a b l = c ∨ Equiv.swap a b l = d then ε else 1) =
      (if l = c ∨ l = d then ε else 1)
    refine Equiv.apply_swap_eq_self
      (v := fun l => if l = c ∨ l = d then ε else 1) ?_ l
    rw [if_neg (by
        rintro (h | h)
        · exact hac h
        · exact had h),
      if_neg (by
        rintro (h | h)
        · exact hbc h
        · exact hbd h)]
  rw [swapRefl, swapRefl, spMat_mul, spMat_mul, hperm]
  congr 1
  funext j
  have hδj : (if Equiv.swap c d j = a ∨ Equiv.swap c d j = b then δ else 1) =
      (if j = a ∨ j = b then δ else 1) := by simpa using congrFun hδ j
  have hεj : (if Equiv.swap a b j = c ∨ Equiv.swap a b j = d then ε else 1) =
      (if j = c ∨ j = d then ε else 1) := by simpa using congrFun hε j
  rw [hδj, hεj, mul_comm]

theorem swapRefl_commute_iff {a b c d : Fin k} (hab : a ≠ b) (hcd : c ≠ d) {δ ε : ZMod 3}
    (hδ : δ ≠ 0) (hε : ε ≠ 0) :
    Commute (swapRefl a b δ) (swapRefl c d ε) ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) ∨ (a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) := by
  constructor
  · rintro hcomm
    by_cases hac : a = c
    · by_cases hbd : b = d
      · exact Or.inl ⟨hac, hbd⟩
      · exfalso
        subst c
        exact monoRefl_swapRefl_not_commute hab hcd hbd hδ hε hcomm
    · by_cases had : a = d
      · by_cases hbc : b = c
        · exact Or.inr (Or.inl ⟨had, hbc⟩)
        · exfalso
          subst d
          rw [← swapRefl_symm c a ε] at hcomm
          exact monoRefl_swapRefl_not_commute hab hac hbc hδ hε hcomm
      · by_cases hbc : b = c
        · exfalso
          subst c
          rw [← swapRefl_symm a b δ] at hcomm
          exact monoRefl_swapRefl_not_commute (Ne.symm hab) hcd had hδ hε hcomm
        · by_cases hbd : b = d
          · exfalso
            subst d
            rw [← swapRefl_symm a b δ, ← swapRefl_symm c b ε] at hcomm
            exact monoRefl_swapRefl_not_commute (Ne.symm hab) hbc hac hδ hε hcomm
          · exact Or.inr (Or.inr ⟨hac, had, hbc, hbd⟩)
  · rintro (⟨hac, hbd⟩ | ⟨had, hbc⟩ | ⟨hac, had, hbc, hbd⟩)
    · subst c
      subst d
      exact monoRefl_commute_same a b δ ε
    · subst d
      subst c
      rw [← swapRefl_symm b a ε]
      exact monoRefl_commute_same a b δ ε
    · exact monoRefl_commute_disjoint hac had hbc hbd δ ε

private theorem monoRefl_col_coord (σ : Equiv.Perm (Fin k)) (s : Fin k → ZMod 3) (m i : Fin k) :
    ((spMat σ s *ᵥ Pi.single m 1) - Pi.single m 1 : Fin k → ZMod 3) i =
      s m * (if i = σ m then 1 else 0) - (if i = m then 1 else 0) := by
  rw [spMat_mulVec]
  beta_reduce
  by_cases hi : i = σ m
  · subst hi
    simp [Pi.single_apply]
  · have hsymm : σ.symm i ≠ m := fun h => hi (by rw [← h, Equiv.apply_symm_apply])
    simp [Pi.single_apply, hi, hsymm]

private theorem monoRefl_col (σ : Equiv.Perm (Fin k)) (s : Fin k → ZMod 3) (m : Fin k) :
    spMat σ s *ᵥ Pi.single m 1 - Pi.single m 1 =
      s m • Pi.single (σ m) 1 - Pi.single m 1 := by
  funext i
  rw [monoRefl_col_coord, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    Pi.single_apply]

private theorem monoRefl_neg_one_mul_sub_one : (-1 : ZMod 3) * 1 - 1 = 1 := by decide

theorem spMat_refl_cases {σ : Equiv.Perm (Fin k)} {s : Fin k → ZMod 3} (hs : IsSign s)
    (hne : spMat σ s ≠ 1) {w : Fin k → ZMod 3}
    (hw : ∀ m : Fin k, ∃ c : ZMod 3, spMat σ s *ᵥ Pi.single m 1 - Pi.single m 1 = c • w) :
    (∃ a, spMat σ s = coordRefl a ∧ ∃ c : ZMod 3, c ≠ 0 ∧ w = c • Pi.single a 1) ∨
      ∃ a b, a ≠ b ∧ ∃ δ : ZMod 3, δ ≠ 0 ∧ spMat σ s = swapRefl a b δ ∧
        ∃ c : ZMod 3, c ≠ 0 ∧ w = c • (Pi.single a 1 - δ • Pi.single b 1) := by
  by_cases hfix : ∀ m, σ m = m
  · have hσ : σ = 1 := Equiv.ext hfix
    subst σ
    have hex : ∃ a, s a = -1 := by
      by_contra h
      push Not at h
      have hs1 : ∀ m, s m = 1 := by
        intro m
        rcases hs m with h1 | h1
        · exact h1
        · exact absurd h1 (h m)
      apply hne
      ext i j
      rw [spMat_apply, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij
        simp [hs1]
      · simp [hij]
    obtain ⟨a, ha⟩ := hex
    have hva : spMat 1 s *ᵥ Pi.single a 1 - Pi.single a 1 = Pi.single a 1 := by
      rw [monoRefl_col]
      funext i
      by_cases hi : i = a
      · rw [hi]
        simp only [Equiv.Perm.one_apply]
        rw [ha]
        simpa using monoRefl_neg_one_mul_sub_one
      · simp [Pi.single_apply, hi, Ne.symm hi]
    obtain ⟨c_a, hca⟩ := hw a
    rw [hva] at hca
    have hca0 : c_a ≠ 0 := by
      intro h0
      have hzero : Pi.single a 1 = (0 : Fin k → ZMod 3) := by rw [hca, h0, zero_smul]
      have e := congrFun hzero a
      simp at e
    have hw_eq : w = c_a⁻¹ • Pi.single a 1 := by
      rw [hca, smul_smul, inv_mul_cancel₀ hca0, one_smul]
    have huniq : ∀ m, s m = -1 → m = a := by
      intro m hm
      have hvm : spMat 1 s *ᵥ Pi.single m 1 - Pi.single m 1 = Pi.single m 1 := by
        rw [monoRefl_col]
        funext i
        by_cases hi : i = m
        · rw [hi]
          simp only [Equiv.Perm.one_apply]
          rw [hm]
          simpa using monoRefl_neg_one_mul_sub_one
        · simp [Pi.single_apply, hi, Ne.symm hi]
      obtain ⟨c_m, hcm⟩ := hw m
      rw [hvm] at hcm
      have hprop : Pi.single m 1 = (c_m * c_a⁻¹) • Pi.single a 1 := by
        rw [hcm, hw_eq, smul_smul]
      have e := congrFun hprop m
      by_contra hma
      rw [Pi.single_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
        if_pos rfl, if_neg hma, mul_zero] at e
      revert e
      decide
    have hs1 : ∀ m, m ≠ a → s m = 1 := by
      intro m hm
      rcases hs m with h1 | h1
      · exact h1
      · exact absurd (huniq m h1) hm
    refine Or.inl ⟨a, ?_, c_a⁻¹, inv_ne_zero hca0, hw_eq⟩
    ext i j
    rw [spMat_apply, coordRefl, spMat_apply]
    by_cases hij : i = j
    · subst i
      by_cases hja : j = a
      · simpa [hja] using ha
      · simpa [hja] using hs1 j hja
    · simp [hij]
  · rw [not_forall] at hfix
    obtain ⟨a, ha⟩ := hfix
    set b : Fin k := σ a with hb
    have hba : b ≠ a := by rw [hb]; exact ha
    have hab : a ≠ b := fun h => hba h.symm
    have hbase : s a • Pi.single (σ a) 1 - Pi.single a 1 ≠ 0 := by
      intro h0
      have e := congrFun h0 a
      rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Pi.single_apply,
        if_neg (fun h => ha h.symm), if_pos rfl, mul_zero, zero_sub, Pi.zero_apply] at e
      revert e
      decide
    obtain ⟨c_a, hca⟩ := hw a
    rw [monoRefl_col] at hca
    have hca0 : c_a ≠ 0 := by
      intro h0
      exact hbase (by rw [hca, h0, zero_smul])
    have hw_eq : w = c_a⁻¹ • (s a • Pi.single (σ a) 1 - Pi.single a 1) := by
      rw [hca, smul_smul, inv_mul_cancel₀ hca0, one_smul]
    have hw_eq_b : w = c_a⁻¹ • (s a • Pi.single b 1 - Pi.single a 1) := by
      rw [hw_eq, ← hb]
    have hprop : ∀ (m : Fin k) (c_m : ZMod 3),
        s m • Pi.single (σ m) 1 - Pi.single m 1 = c_m • w →
        s m • Pi.single (σ m) 1 - Pi.single m 1 =
          (c_m * c_a⁻¹) • (s a • Pi.single b 1 - Pi.single a 1) := by
      intro m c_m hcm
      rw [hcm, hw_eq_b, smul_smul]
    have hout : ∀ m, m ≠ a → m ≠ b → σ m = m ∧ s m = 1 := by
      intro m hma hmb
      obtain ⟨c_m, hcm⟩ := hw m
      rw [monoRefl_col] at hcm
      have hp := hprop m c_m hcm
      have e := congrFun hp m
      rw [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, Pi.single_apply,
        Pi.smul_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_apply,
        Pi.single_apply] at e
      rw [if_neg hmb, if_neg hma, if_pos rfl] at e
      simp at e
      by_cases hm : σ m = m
      · refine ⟨hm, ?_⟩
        rw [if_pos hm.symm] at e
        rcases hs m with h1 | h1
        · exact h1
        · exfalso
          rw [h1] at e
          revert e
          decide
      · exfalso
        rw [if_neg (fun h : m = σ m => hm h.symm)] at e
        revert e
        decide
    have hbmap : σ b = a := by
      by_contra hne
      have hbfix : σ b ≠ b := by
        intro h
        exact hab (σ.injective (h.trans hb)).symm
      have houtb := hout (σ b) hne hbfix
      exact hbfix (σ.injective houtb.1)
    obtain ⟨c_b, hcb⟩ := hw b
    rw [monoRefl_col] at hcb
    have hpb := hprop b c_b hcb
    rw [hbmap] at hpb
    set lam : ZMod 3 := c_b * c_a⁻¹ with hlam
    have hpb' : s b • Pi.single a 1 - Pi.single b 1 =
        lam • (s a • Pi.single b 1 - Pi.single a 1) := hpb
    have ea := congrFun hpb' a
    have eb := congrFun hpb' b
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Pi.single_apply,
      Pi.smul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      Pi.single_apply] at ea eb
    rw [if_pos rfl, if_neg hab] at ea
    rw [if_neg (Ne.symm hab), if_pos rfl] at eb
    have ea' : s b = -lam := by
      simp at ea
      calc s b = s b - 0 := by abel
        _ = -lam := ea
    have eb' : -1 = lam * s a := by
      simp at eb
      calc -1 = lam * (s a - 0) := eb
        _ = lam * s a := by rw [show s a - 0 = s a from by abel]
    have hlam' : lam = -s b := by
      have h := congrArg Neg.neg ea'
      calc lam = - -lam := by abel
        _ = -s b := h.symm
    have hsba : s b = s a := by
      rcases hs a with hsa | hsa <;> rcases hs b with hsb | hsb
      · rw [hsa, hsb]
      · exfalso
        rw [hsa, hlam', hsb] at eb'
        revert eb'
        decide
      · exfalso
        rw [hsa, hlam', hsb] at eb'
        revert eb'
        decide
      · rw [hsa, hsb]
    have hσeq : σ = Equiv.swap a b := by
      ext m
      by_cases hma : m = a
      · rw [hma, Equiv.swap_apply_left]
      · by_cases hmb : m = b
        · rw [hmb, hbmap, Equiv.swap_apply_right]
        · rw [(hout m hma hmb).1, Equiv.swap_apply_of_ne_of_ne hma hmb]
    have hseq : s = fun l => if l = a ∨ l = b then s a else 1 := by
      funext l
      by_cases hla : l = a
      · subst l
        simp
      · by_cases hlb : l = b
        · subst l
          simp [hsba]
        · simp [hla, hlb, (hout l hla hlb).2]
    have hP : spMat σ s = swapRefl a b (s a) := by
      rw [hσeq, hseq, swapRefl]
      beta_reduce
      simp
    have hwform : w = (-c_a⁻¹) • (Pi.single a 1 - s a • Pi.single b 1) := by
      have hva' : s a • Pi.single b 1 - Pi.single a 1 =
          -(Pi.single a 1 - s a • Pi.single b 1) := by
        abel
      calc
        w = c_a⁻¹ • (s a • Pi.single b 1 - Pi.single a 1) := hw_eq_b
        _ = (-c_a⁻¹) • (Pi.single a 1 - s a • Pi.single b 1) := by
              rw [hva']
              funext i
              simp only [Pi.smul_apply, smul_eq_mul]
              exact (mul_neg _ _).trans (neg_mul _ _).symm
    refine Or.inr ⟨a, b, hab, s a, ?_, hP, -c_a⁻¹, ?_, hwform⟩
    · rcases hs a with h | h <;> rw [h] <;> decide
    · exact neg_ne_zero.mpr (inv_ne_zero hca0)

theorem coordRefl_mem_monoN0 {n : ℕ} (a : Fin (n + 1)) : coordRefl a ∈ monoN0 n := by
  refine ⟨1, fun i => if i = a then -1 else 1, ?_, rfl, rfl⟩
  intro i
  by_cases h : i = a <;> simp [h]

theorem swapRefl_mem_monoN0 {n : ℕ} {a b : Fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ 0) {δ : ZMod 3}
    (hδ : δ ≠ 0) : swapRefl a b δ ∈ monoN0 n := by
  refine ⟨Equiv.swap a b, fun l => if l = a ∨ l = b then δ else 1, ?_, ?_, rfl⟩
  · intro l
    change (if l = a ∨ l = b then δ else 1) = 1 ∨ (if l = a ∨ l = b then δ else 1) = -1
    by_cases hl : l = a ∨ l = b
    · rw [if_pos hl]
      exact eq_one_or_of_ne_zero hδ
    · rw [if_neg hl]
      exact Or.inl rfl
  · exact Equiv.swap_apply_of_ne_of_ne (fun h => ha h.symm) (fun h => hb h.symm)

theorem commute_coordRefl_zero_of_mem_monoN0 {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)} (hA : A ∈ monoN0 n) :
    Commute A (coordRefl 0) := by
  obtain ⟨σ, s, hs, hσ0, rfl⟩ := hA
  show spMat σ s * coordRefl 0 = coordRefl 0 * spMat σ s
  rw [coordRefl, spMat_mul, spMat_mul]
  simp only [one_mul, mul_one]
  congr 1
  funext j
  change s j * (if j = 0 then -1 else 1) =
    (if σ j = 0 then -1 else 1) * s j
  have hj : σ j = 0 ↔ j = 0 := by
    constructor
    · intro h
      exact σ.injective (h.trans hσ0.symm)
    · intro h
      rw [h, hσ0]
  by_cases h0 : j = 0
  · rw [if_pos h0, if_pos (hj.mpr h0)]
    ring
  · rw [if_neg h0, if_neg (fun h => h0 (hj.mp h))]
    ring

end CFSG.StandardType.FrameRoute.FS81
