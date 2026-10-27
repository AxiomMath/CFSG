module

public import CFSG.LocalAnalysis.StandardType.GGLangRatCentreStmts
public import CFSG.LieType.Chevalley.KernelComponentRoots
import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
import CFSG.HardMathSupport.Timmesfeld.RootAut.Count

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.RootAut

private def langRatNF_coordStep (n : ℕ) (i : Fin n) : Matrix (Fin n) (Fin n) ℤ :=
  1 - Matrix.of (fun a b => if a = i then CartanMatrix.D n i b else 0)

private theorem langRatNF_coordReflect_mulVec (n : ℕ) (i : Fin n) (x : Fin n → ℤ) :
    coordReflect (CartanMatrix.D n) i x = Matrix.mulVec (langRatNF_coordStep n i) x := by
  rw [coordReflect, langRatNF_coordStep, Matrix.sub_mulVec, Matrix.one_mulVec]
  funext a
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, Matrix.of_apply,
    dotProduct]
  by_cases h : a = i
  · subst h
    simp [Pi.single_eq_same]
  · simp [h]

private theorem langRatNF_coordReflect_add (n : ℕ) (i : Fin n) (x y : Fin n → ℤ) :
    coordReflect (CartanMatrix.D n) i (x + y) =
      coordReflect (CartanMatrix.D n) i x + coordReflect (CartanMatrix.D n) i y := by
  rw [langRatNF_coordReflect_mulVec, langRatNF_coordReflect_mulVec,
    langRatNF_coordReflect_mulVec, Matrix.mulVec_add]

private theorem langRatNF_coordReflect_smul (n : ℕ) (i : Fin n) (k : ℤ) (x : Fin n → ℤ) :
    coordReflect (CartanMatrix.D n) i (k • x) =
      k • coordReflect (CartanMatrix.D n) i x := by
  rw [langRatNF_coordReflect_mulVec, langRatNF_coordReflect_mulVec, Matrix.mulVec_smul]

private theorem langRatNF_fold_add {n : ℕ} (l : List (Fin n)) (x y : Fin n → ℤ) :
    l.foldr (coordReflect (CartanMatrix.D n)) (x + y) =
      l.foldr (coordReflect (CartanMatrix.D n)) x +
        l.foldr (coordReflect (CartanMatrix.D n)) y := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldr_cons]
    rw [ih, langRatNF_coordReflect_add]

private theorem langRatNF_fold_zsmul {n : ℕ} (l : List (Fin n)) (k : ℤ) (x : Fin n → ℤ) :
    l.foldr (coordReflect (CartanMatrix.D n)) (k • x) =
      k • l.foldr (coordReflect (CartanMatrix.D n)) x := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldr_cons]
    rw [ih, langRatNF_coordReflect_smul]

private theorem langRatNF_fold_zero {n : ℕ} (l : List (Fin n)) :
    l.foldr (coordReflect (CartanMatrix.D n)) 0 = 0 := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.foldr_cons, ih]
    simp [coordReflect]

private theorem langRatNF_fold_sum {n : ℕ} {ι : Type*} (l : List (Fin n)) (s : Finset ι)
    (f : ι → Fin n → ℤ) :
    l.foldr (coordReflect (CartanMatrix.D n)) (∑ i ∈ s, f i) =
      ∑ i ∈ s, l.foldr (coordReflect (CartanMatrix.D n)) (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [langRatNF_fold_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, langRatNF_fold_add, ih]

private theorem langRatNF_fold_eq_neg {n : ℕ} (l : List (Fin n))
    (hs : ∀ j : Fin n,
      l.foldr (coordReflect (CartanMatrix.D n)) (Pi.single j 1) = -Pi.single j 1)
    (c : Fin n → ℤ) :
    l.foldr (coordReflect (CartanMatrix.D n)) c = -c := by
  have hc : c = ∑ j, c j • (Pi.single j 1 : Fin n → ℤ) := by
    funext a
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single a]
    · simp
    · intro j _ hj
      rw [Pi.single_eq_of_ne (Ne.symm hj), mul_zero]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  rw [hc, langRatNF_fold_sum]
  simp only [langRatNF_fold_zsmul, hs, smul_neg, Finset.sum_neg_distrib]

private theorem langRatNF_rootLift_neg {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} {n : ℕ}
    (e : simpleRoots Ψ ≃ Fin n) (c : Fin n → ℤ) :
    rootLift e (-c) = -rootLift e c := by
  rw [rootLift, rootLift, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun β hβ => ?_
  simp [liftCoeff, hβ]

private theorem langRatNF_fold_smul {τ : Tag}
    {Ψ : Set (Fin τ.rank → ℤ)} {n : ℕ} (e : simpleRoots Ψ ≃ Fin n)
    (he : ∀ β γ : simpleRoots Ψ,
      corootPair (β : Fin τ.rank → ℤ) γ = CartanMatrix.D n (e β) (e γ))
    (l : List (Fin n)) (c : Fin n → ℤ) :
    (l.map fun i => rootReflection (e.symm i : Fin τ.rank → ℤ)).prod • rootLift e c =
      rootLift e (l.foldr (coordReflect (CartanMatrix.D n)) c) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, mul_smul, ih, List.foldr_cons]
    exact (rootLift_coordReflect e he i
      (l.foldr (coordReflect (CartanMatrix.D n)) c)).symm

private theorem langRatNF_twistInner_of_word {τ : Tag}
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) {n : ℕ}
    (e : simpleRoots Ψ ≃ Fin n)
    (he : ∀ β γ : simpleRoots Ψ,
      corootPair (β : Fin τ.rank → ℤ) γ = CartanMatrix.D n (e β) (e γ))
    (l : List (Fin n))
    (hs : ∀ j : Fin n,
      l.foldr (coordReflect (CartanMatrix.D n)) (Pi.single j 1) = -Pi.single j 1) :
    twistInner Ψ (fun γ => -γ) := by
  classical
  have hfold : ∀ c : Fin n → ℤ,
      l.foldr (coordReflect (CartanMatrix.D n)) c = -c :=
    langRatNF_fold_eq_neg l hs
  have hact : ∀ c : Fin n → ℤ,
      (l.map fun i => rootReflection (e.symm i : Fin τ.rank → ℤ)).prod • rootLift e c =
        -rootLift e c := by
    intro c
    rw [langRatNF_fold_smul e he l c, hfold c, langRatNF_rootLift_neg e c]
  refine ⟨(l.map fun i => rootReflection (e.symm i : Fin τ.rank → ℤ)).prod, ?_, ?_⟩
  · refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact componentWeylGroup_le Ψ (rootReflection_mem_componentWeylGroup (e.symm i).2)
  · intro γ hγ
    have hmem : γ ∈ rootLift e '' {x : Fin n → ℤ | IsOrbitRoot (CartanMatrix.D n) x} := by
      rw [image_rootLift_orbit hΨ e he]
      exact hγ
    obtain ⟨c, -, rfl⟩ := hmem
    exact (hact c).symm

private def langRatNF_word4 : List (Fin 4) :=
  [0, 1, 0, 2, 1, 0, 3, 1, 0, 2, 1, 3]

private def langRatNF_word6 : List (Fin 6) :=
  [0, 1, 0, 2, 1, 0, 3, 2, 1, 0, 4, 3, 2, 1, 0, 5, 3, 2, 1, 0, 4, 3, 2, 1, 5, 3, 2, 4, 3, 5]

private def langRatNF_word8 : List (Fin 8) :=
  [0, 1, 0, 2, 1, 0, 3, 2, 1, 0, 4, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 6, 5, 4, 3, 2, 1, 0, 7, 5, 4,
    3, 2, 1, 0, 6, 5, 4, 3, 2, 1, 7, 5, 4, 3, 2, 6, 5, 4, 3, 7, 5, 4, 6, 5, 7]

private def langRatNF_word8a : List (Fin 8) :=
  [0, 1, 0, 2, 1, 0, 3, 2, 1, 0, 4, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 6, 5, 4, 3, 2, 1, 0]

private def langRatNF_word8b : List (Fin 8) :=
  [7, 5, 4, 3, 2, 1, 0, 6, 5, 4, 3, 2, 1, 7, 5, 4, 3, 2, 6, 5, 4, 3, 7, 5, 4, 6, 5, 7]

private def langRatNF_v8 (j : Fin 8) : Fin 8 → ℤ :=
  match j.val with
  | 0 => ![0, 0, 0, 0, 0, 0, 1, 0]
  | 1 => ![0, 0, 0, 0, 0, 1, 0, 0]
  | 2 => ![0, 0, 0, 0, 1, 0, 0, 0]
  | 3 => ![0, 0, 0, 1, 0, 0, 0, 0]
  | 4 => ![0, 0, 1, 0, 0, 0, 0, 0]
  | 5 => ![0, 1, 0, 0, 0, 0, 0, 0]
  | 6 => ![1, 0, 0, 0, 0, 0, 0, 0]
  | _ => ![-1, -2, -2, -2, -2, -2, -1, -1]

private theorem langRatNF_word8b_unit (j : Fin 8) :
    langRatNF_word8b.foldr (coordReflect (CartanMatrix.D 8)) (Pi.single j 1) =
      langRatNF_v8 j := by
  fin_cases j <;> decide

private theorem langRatNF_word8a_unit (j : Fin 8) :
    langRatNF_word8a.foldr (coordReflect (CartanMatrix.D 8)) (langRatNF_v8 j) =
      -Pi.single j 1 := by
  fin_cases j <;> decide

private theorem langRatNF_word8_unit (j : Fin 8) :
    langRatNF_word8.foldr (coordReflect (CartanMatrix.D 8)) (Pi.single j 1) =
      -Pi.single j 1 := by
  have h : langRatNF_word8 = langRatNF_word8a ++ langRatNF_word8b := rfl
  rw [h, List.foldr_append, langRatNF_word8b_unit j, langRatNF_word8a_unit j]

theorem langRatNegOne_twistInner_of_cartanD {τ : Tag}
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) {n : ℕ} (hn : n = 4 ∨ n = 6 ∨ n = 8)
    (e : simpleRoots Ψ ≃ Fin n)
    (he : ∀ β γ : simpleRoots Ψ,
      corootPair (β : Fin τ.rank → ℤ) γ = CartanMatrix.D n (e β) (e γ)) :
    twistInner Ψ (fun γ => -γ) := by
  rcases hn with rfl | rfl | rfl
  · exact langRatNF_twistInner_of_word hΨ e he langRatNF_word4 (fun j => by
      fin_cases j <;> decide)
  · exact langRatNF_twistInner_of_word hΨ e he langRatNF_word6 (fun j => by
      fin_cases j <;> decide)
  · exact langRatNF_twistInner_of_word hΨ e he langRatNF_word8 langRatNF_word8_unit

end CFSG.StandardType.LangRat
