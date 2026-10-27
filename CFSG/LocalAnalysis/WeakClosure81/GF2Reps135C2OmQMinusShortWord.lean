module

public import CFSG.LieType.Universal.Spin.Roots.TypeB
public import CFSG.LieType.RootSystem.Positivity
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFWeyl

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin CFSG.StandardType

@[expose] def omqMinusPalWord (l : ℕ) (hl : 0 < l) : ℕ → List (Fin l)
  | 0 => [⟨l - 1, by omega⟩]
  | d + 1 => ⟨l - 2 - d, by omega⟩ :: (omqMinusPalWord l hl d ++ [⟨l - 2 - d, by omega⟩])

@[expose] def omqMinusShortWord (l : ℕ) (hl : 0 < l) : List (Fin l) :=
  omqMinusPalWord l hl (l - 1)

section

variable {l : ℕ}

private theorem c2slomqi5_pal_reverse (hl : 0 < l) (d : ℕ) :
    (omqMinusPalWord l hl d).reverse = omqMinusPalWord l hl d := by
  induction d with
  | zero => simp [omqMinusPalWord]
  | succ d ih => simp [omqMinusPalWord, List.reverse_append, ih]

private theorem c2slomqi5_real_step {a : Fin l} (ha : a.val + 1 < l) {w : (coxeterMatrix
    (isFiniteType_cartanB l)).Group}
    (hw : omqnfRealizes l w 1 (spSgn (⟨a.val + 1, ha⟩ : Fin l))) :
    omqnfRealizes l ((coxeterMatrix (isFiniteType_cartanB l)).toCoxeterSystem.simple a *
      (w * (coxeterMatrix (isFiniteType_cartanB l)).toCoxeterSystem.simple a)) 1 (spSgn a) := by
  intro γ
  rw [weylAction_mul_apply, weylAction_mul_apply, weylAction_simple]
  rw [toStdB_reflection_of_lt l ha, Function.comp_def]
  funext b
  have h1 := congrFun (hw (reflection (cartanB l) a γ)) (Equiv.swap a ⟨a.val + 1, ha⟩ b)
  rw [h1, toStdB_reflection_of_lt l ha, Function.comp_apply]
  have e1 : ∀ x : Fin l, (Equiv.symm (1 : Equiv.Perm (Fin l))) x = x := fun x => rfl
  simp only [e1, Equiv.swap_apply_self]
  have e2 : (Equiv.swap a (⟨a.val + 1, ha⟩ : Fin l)) b = ⟨a.val + 1, ha⟩ ↔ b = a := by
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
  simp only [spSgn, e2]

private theorem c2slomqi5_coord {a : Fin l} (ha : a.val + 1 < l) {v : Fin l → ℤ}
    (hv : toStdB l v = Pi.single a 1 + Pi.single (⟨a.val + 1, ha⟩ : Fin l) 1) : v a = 1 := by
  have h1 : v = ofStdB l (Pi.single a 1 + Pi.single (⟨a.val + 1, ha⟩ : Fin l) 1) :=
    (toStdB_eq_iff l v _).mp hv
  have hne : a ≠ (⟨a.val + 1, ha⟩ : Fin l) := Fin.ne_of_val_ne (by simp)
  rw [h1, ofStdB, Finset.sum_eq_single a]
  · simp [Pi.single_apply, hne]
  · intro b _ hb
    by_cases hba : b.val ≤ a.val
    · have hb' : b ≠ (⟨a.val + 1, ha⟩ : Fin l) := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      simp [hba, Pi.single_apply, hb, hb']
    · simp [hba]
  · simp

private theorem c2slomqi5_toStd {a : Fin l} (ha : a.val + 1 < l) {w : (coxeterMatrix
    (isFiniteType_cartanB l)).Group}
    (hw : omqnfRealizes l w 1 (spSgn (⟨a.val + 1, ha⟩ : Fin l))) :
    toStdB l (weylAction (isFiniteType_cartanB l) w (Pi.single a 1)) =
      Pi.single a 1 + Pi.single (⟨a.val + 1, ha⟩ : Fin l) 1 := by
  rw [hw, toStdB_single_of_lt l ha]
  funext b
  have e1 : (Equiv.symm (1 : Equiv.Perm (Fin l))) b = b := rfl
  have hne : a ≠ (⟨a.val + 1, ha⟩ : Fin l) := Fin.ne_of_val_ne (by simp)
  by_cases hb : b = a
  · subst hb
    simp [e1, spSgn, hne]
  · by_cases hb' : b = (⟨a.val + 1, ha⟩ : Fin l)
    · subst hb'
      simp [e1, spSgn, hne.symm, Pi.single_apply]
    · simp [e1, spSgn, hb, hb', Pi.single_apply]

private theorem c2slomqi5_key (hl : 0 < l) :
    ∀ d : ℕ, d < l →
      (coxeterMatrix (isFiniteType_cartanB l)).toCoxeterSystem.IsReduced
          (omqMinusPalWord l hl d) ∧
        omqnfRealizes l ((coxeterMatrix (isFiniteType_cartanB l)).toCoxeterSystem.wordProd
          (omqMinusPalWord l hl d)) 1 (spSgn (⟨l - 1 - d, by omega⟩ : Fin l)) := by
  set cs := (coxeterMatrix (isFiniteType_cartanB l)).toCoxeterSystem with hcs
  intro d
  induction d with
  | zero =>
    intro hd
    refine ⟨?_, ?_⟩
    · rw [CoxeterSystem.IsReduced, omqMinusPalWord, cs.wordProd_singleton, cs.length_simple]
      rfl
    · rw [omqMinusPalWord, cs.wordProd_singleton]
      exact omqnfRealizes_simple_of_not_lt (k := ⟨l - 1, by omega⟩) (by
        show ¬ (l - 1 + 1 < l)
        omega)
  | succ d ih =>
    intro hd
    obtain ⟨hred, hreal⟩ := ih (by omega)
    have ha : (⟨l - 2 - d, by omega⟩ : Fin l).val + 1 < l := by
      show l - 2 - d + 1 < l
      omega
    have hidx : (⟨l - 1 - d, by omega⟩ : Fin l) =
        ⟨(⟨l - 2 - d, by omega⟩ : Fin l).val + 1, ha⟩ := by
      apply Fin.ext
      show l - 1 - d = l - 2 - d + 1
      omega
    rw [hidx] at hreal
    have hinv : (cs.wordProd (omqMinusPalWord l hl d))⁻¹ =
        cs.wordProd (omqMinusPalWord l hl d) := by
      rw [← cs.wordProd_reverse, c2slomqi5_pal_reverse]
    have hcoord1 := c2slomqi5_coord ha (c2slomqi5_toStd ha hreal)
    have hnotL : ¬ cs.IsLeftDescent (cs.wordProd (omqMinusPalWord l hl d))
        (⟨l - 2 - d, by omega⟩ : Fin l) := by
      rw [← cs.isRightDescent_inv_iff, hinv, isRightDescent_iff]
      intro hle
      have := hle (⟨l - 2 - d, by omega⟩ : Fin l)
      change (weylAction (isFiniteType_cartanB l) (cs.wordProd (omqMinusPalWord l hl d))
        (Pi.single (⟨l - 2 - d, by omega⟩ : Fin l) 1)) (⟨l - 2 - d, by omega⟩ : Fin l) ≤ 0 at this
      omega
    have hred1 : cs.IsReduced ((⟨l - 2 - d, by omega⟩ : Fin l) :: omqMinusPalWord l hl d) := by
      rw [CoxeterSystem.IsReduced, cs.wordProd_cons, cs.not_isLeftDescent_iff.mp hnotL, hred.eq,
        List.length_cons]
    have hnotR : ¬ cs.IsRightDescent (cs.wordProd ((⟨l - 2 - d, by omega⟩ : Fin l) ::
        omqMinusPalWord l hl d)) (⟨l - 2 - d, by omega⟩ : Fin l) := by
      rw [isRightDescent_iff]
      intro hle
      have := hle (⟨l - 2 - d, by omega⟩ : Fin l)
      change (weylAction (isFiniteType_cartanB l) (cs.wordProd ((⟨l - 2 - d, by omega⟩ : Fin l) ::
        omqMinusPalWord l hl d)) (Pi.single (⟨l - 2 - d, by omega⟩ : Fin l) 1))
        (⟨l - 2 - d, by omega⟩ : Fin l) ≤ 0 at this
      rw [cs.wordProd_cons, weylAction_mul_apply, weylAction_simple] at this
      have hst : toStdB l (reflection (cartanB l) (⟨l - 2 - d, by omega⟩ : Fin l)
          (weylAction (isFiniteType_cartanB l) (cs.wordProd (omqMinusPalWord l hl d))
            (Pi.single (⟨l - 2 - d, by omega⟩ : Fin l) 1))) =
          Pi.single (⟨l - 2 - d, by omega⟩ : Fin l) 1 +
            Pi.single (⟨(⟨l - 2 - d, by omega⟩ : Fin l).val + 1, ha⟩ : Fin l) 1 := by
        rw [toStdB_reflection_of_lt l ha, c2slomqi5_toStd ha hreal]
        funext b
        have e2 : (Equiv.swap (⟨l - 2 - d, by omega⟩ : Fin l)
            (⟨(⟨l - 2 - d, by omega⟩ : Fin l).val + 1, ha⟩ : Fin l)) b =
              (⟨(⟨l - 2 - d, by omega⟩ : Fin l).val + 1, ha⟩ : Fin l) ↔
            b = (⟨l - 2 - d, by omega⟩ : Fin l) := by
          rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
        have e3 : (Equiv.swap (⟨l - 2 - d, by omega⟩ : Fin l)
            (⟨(⟨l - 2 - d, by omega⟩ : Fin l).val + 1, ha⟩ : Fin l)) b =
              (⟨l - 2 - d, by omega⟩ : Fin l) ↔
            b = (⟨(⟨l - 2 - d, by omega⟩ : Fin l).val + 1, ha⟩ : Fin l) := by
          rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
        simp only [Function.comp_apply, Pi.add_apply, Pi.single_apply, e2, e3]
        by_cases h1 : b = (⟨l - 2 - d, by omega⟩ : Fin l)
        · simp [h1]
        · by_cases h2 : b = (⟨(⟨l - 2 - d, by omega⟩ : Fin l).val + 1, ha⟩ : Fin l)
          · simp [h2]
          · simp [h1, h2]
      have := c2slomqi5_coord ha hst
      omega
    refine ⟨?_, ?_⟩
    · have hred2 : cs.IsReduced (((⟨l - 2 - d, by omega⟩ : Fin l) :: omqMinusPalWord l hl d) ++
          [(⟨l - 2 - d, by omega⟩ : Fin l)]) := by
        rw [CoxeterSystem.IsReduced, cs.wordProd_append, cs.wordProd_singleton,
          cs.not_isRightDescent_iff.mp hnotR, hred1.eq, List.length_append, List.length_singleton]
      simpa [omqMinusPalWord] using hred2
    · have hr := c2slomqi5_real_step ha hreal
      rw [omqMinusPalWord, cs.wordProd_cons, cs.wordProd_append, cs.wordProd_singleton]
      have hidx2 : (⟨l - 1 - (d + 1), by omega⟩ : Fin l) = ⟨l - 2 - d, by omega⟩ := by
        apply Fin.ext
        show l - 1 - (d + 1) = l - 2 - d
        omega
      rw [hidx2]
      exact hr

end

theorem omq_omMinus_shortWord_mem (l : ℕ) (hl : 0 < l) (j : Fin l) :
    j ∈ omqMinusShortWord l hl := by
  have key : ∀ d : ℕ, ∀ j : Fin l, l - 1 - d ≤ j.val → j ∈ omqMinusPalWord l hl d := by
    intro d
    induction d with
    | zero =>
      intro j hj
      have : j = ⟨l - 1, by omega⟩ := Fin.ext (by have := j.isLt; show j.val = l - 1; omega)
      simp [omqMinusPalWord, this]
    | succ d ih =>
      intro j hj
      by_cases hjd : l - 1 - d ≤ j.val
      · simp only [omqMinusPalWord, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl (ih j hjd))
      · have : j = ⟨l - 2 - d, by omega⟩ := Fin.ext (by show j.val = l - 2 - d; omega)
        simp [omqMinusPalWord, this]
  exact key (l - 1) j (by omega)

theorem omq_omMinus_reduced_shortWord (l : ℕ) (hl : 3 ≤ l) :
    (coxeterMatrix (isFiniteType_cartanB l)).toCoxeterSystem.IsReduced
      (omqMinusShortWord l (by omega)) := by
  exact (c2slomqi5_key (by omega) (l - 1) (by omega)).1

end CFSG.LocalAnalysis.WeakClosure81
