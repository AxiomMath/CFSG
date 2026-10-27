module

public import CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProofWeyl
public import CFSG.RankThree.PartOne.KF4.QPlusWeyl

public section

namespace CFSG.RankThree.PartTwo.Sec8.ReeF4Conj2Proof

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.Monster.B.Geometry
open CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProof

@[expose] def codeOfWord (ω : List (Fin Tag.F4.rank)) : ℕ := ω.foldr f4Act 794688

theorem f4Realizes_wordProd
    (ω : List (Fin Tag.F4.rank)) :
    F4Realizes ((coxeterSystem Tag.F4).wordProd ω) (codeOfWord ω) := by
  induction ω with
  | nil => exact f4Realizes_one
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons]
    exact ih.simple_mul i

theorem smul_single_eq_codeRoots
    {w : WeylGroup Tag.F4} {c : ℕ} (h : F4Realizes w c) (j : Fin Tag.F4.rank) :
    w • (Pi.single j 1 : Fin Tag.F4.rank → ℤ) = codeRoots c j :=
  (h j).2

theorem smul_single_eq_codeRoots'
    {w : WeylGroup ReeTag.F4.tag} {c : ℕ} (h : F4Realizes w c) (j : Fin ReeTag.F4.tag.rank) :
    w • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) = codeRoots c j :=
  (h j).2

@[expose] def hiConjWord : List (Fin Tag.F4.rank) := [0, 1, 2, 3, 1, 2, 0]

@[expose] def stdGen : Fin 4 → List (Fin Tag.F4.rank) :=
  ![[0], hiConjWord ++ [1] ++ hiConjWord.reverse, [2], [3]]

@[expose] def stdGenRoot : Fin 4 → Fin Tag.F4.rank → ℤ :=
  ![Pi.single 0 1, ![2, 3, 4, 2], Pi.single 2 1, Pi.single 3 1]

@[expose] def stdWords : List (List (Fin 4)) :=
  ([[], [0], [1], [0, 1], [1, 0], [0, 1, 0]] : List (List (Fin 4))).flatMap fun a =>
    ([[], [2], [3], [2, 3], [3, 2], [2, 3, 2]] : List (List (Fin 4))).map fun b => a ++ b

@[expose] def stdExpand (ω : List (Fin 4)) : List (Fin Tag.F4.rank) := ω.flatMap stdGen

@[expose] def condStd (c : ℕ) : Bool :=
  (List.finRange 4).all fun j => (codeRoots c j 1 - if j = 1 then 1 else 0) % 3 == 0

@[expose] def stdStabCheck : Bool :=
  (List.range 1152).all fun k =>
    !condStd (f4Code k) || (stdWords.map fun ω => codeOfWord (stdExpand ω)).contains (f4Code k)

set_option maxRecDepth 100000 in
theorem stdStabCheck_eq : stdStabCheck = true := by decide +kernel

set_option maxRecDepth 10000 in
theorem hiConjWord_smul :
    (coxeterSystem Tag.F4).wordProd hiConjWord •
        (Pi.single (1 : Fin Tag.F4.rank) 1 : Fin Tag.F4.rank → ℤ) =
      stdGenRoot 1 := by
  rw [smul_single_eq_codeRoots (f4Realizes_wordProd hiConjWord) 1]
  funext l
  fin_cases l <;> decide +kernel

theorem rootReflection_single
    (j : Fin Tag.F4.rank) :
    rootReflection (Pi.single j 1 : Fin Tag.F4.rank → ℤ) = (coxeterSystem Tag.F4).simple j := by
  rw [rootReflection_eq_conj (w := 1) (j := j) (by rw [one_smul]), one_mul, inv_one, mul_one]

theorem wordProd_stdGen
    (g : Fin 4) :
    (coxeterSystem Tag.F4).wordProd (stdGen g) = rootReflection (stdGenRoot g) := by
  fin_cases g
  · show (coxeterSystem Tag.F4).wordProd [0] = rootReflection (Pi.single 0 1)
    rw [CoxeterSystem.wordProd_singleton, rootReflection_single]
  · show (coxeterSystem Tag.F4).wordProd (hiConjWord ++ [1] ++ hiConjWord.reverse) =
      rootReflection (stdGenRoot 1)
    rw [rootReflection_eq_conj hiConjWord_smul, CoxeterSystem.wordProd_append,
      CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_reverse,
      CoxeterSystem.wordProd_singleton]
  · show (coxeterSystem Tag.F4).wordProd [2] = rootReflection (Pi.single 2 1)
    rw [CoxeterSystem.wordProd_singleton, rootReflection_single]
  · show (coxeterSystem Tag.F4).wordProd [3] = rootReflection (Pi.single 3 1)
    rw [CoxeterSystem.wordProd_singleton, rootReflection_single]

theorem wordProd_stdExpand
    (ω : List (Fin 4)) :
    (coxeterSystem Tag.F4).wordProd (stdExpand ω) =
      (ω.map fun g => rootReflection (stdGenRoot g)).prod := by
  induction ω with
  | nil => rfl
  | cons g ω ih =>
    rw [stdExpand, List.flatMap_cons, CoxeterSystem.wordProd_append, List.map_cons,
      List.prod_cons, wordProd_stdGen]
    exact congrArg _ ih

theorem mem_closure_of_stdStab
    {S : Set (Fin Tag.F4.rank → ℤ)} (hS : ∀ g, stdGenRoot g ∈ S) {w : WeylGroup Tag.F4}
    (hw : ∀ j : Fin Tag.F4.rank,
      (3 : ℤ) ∣ (w • (Pi.single j 1 : Fin Tag.F4.rank → ℤ)) 1 - if j = 1 then 1 else 0) :
    w ∈ Subgroup.closure {s | ∃ α ∈ S, s = rootReflection α} := by
  obtain ⟨k, hk, hr, -⟩ := exists_entry w
  have hcond : condStd (f4Code k) = true := by
    simp only [condStd, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq]
    intro j
    have h := hw j
    rw [smul_single_eq_codeRoots hr j] at h
    exact Int.emod_eq_zero_of_dvd h
  have hcheck := stdStabCheck_eq
  simp only [stdStabCheck, List.all_eq_true, List.mem_range] at hcheck
  have h1 := hcheck k hk
  rw [hcond, Bool.not_true, Bool.false_or, List.contains_iff_mem, List.mem_map] at h1
  obtain ⟨ω, -, hω⟩ := h1
  have hw' : w = (coxeterSystem Tag.F4).wordProd (stdExpand ω) :=
    hr.eq (hω ▸ f4Realizes_wordProd (stdExpand ω))
  rw [hw', wordProd_stdExpand]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨g, -, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨stdGenRoot g, hS g, rfl⟩

@[expose] def conjK (s : ℤ) (i j : ℕ) : ℕ :=
  if s = 1 then
    ([[0, 113, 40], [123, 112, 114], [0, 234, 115]].getD i []).getD j 0
  else
    ([[0, 45, 9], [166, 167, 121], [170, 8, 169]].getD i []).getD j 0

@[expose] def condConj (s : ℤ) (i j : ℕ) (c : ℕ) : Bool :=
  (List.finRange 4).all fun k =>
    ((i : ℤ) * dot4 (uBar s 0) (codeRoots c k) + (j : ℤ) * dot4 (uBar s 1) (codeRoots c k) -
      if k = 1 then 1 else 0) % 3 == 0

@[expose] def conjCheck : Bool :=
  ([1, 2] : List ℤ).all fun s => (List.range 3).all fun i => (List.range 3).all fun j =>
    (i == 0 && j == 0) || (decide (conjK s i j < 1152) && condConj s i j (f4Code (conjK s i j)))

set_option maxRecDepth 100000 in
theorem conjCheck_eq : conjCheck = true := by decide +kernel

theorem exists_transport {s : ℤ}
    (hs : s = 1 ∨ s = 2) {i j : ℕ} (hi : i < 3) (hj : j < 3) (hij : ¬ (i = 0 ∧ j = 0)) :
    ∃ v : WeylGroup ReeTag.F4.tag, ∀ k : Fin ReeTag.F4.tag.rank,
      (3 : ℤ) ∣ (i : ℤ) * dot4 (uBar s 0) (v • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) +
        (j : ℤ) * dot4 (uBar s 1) (v • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) -
          if k = 1 then 1 else 0 := by
  have hcheck := conjCheck_eq
  simp only [conjCheck, List.all_eq_true, List.mem_range] at hcheck
  have h1 := hcheck s (by rcases hs with rfl | rfl <;> simp) i hi j hj
  have hij' : (i == 0 && j == 0) = false := by
    simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    tauto
  rw [hij', Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨hlt, hc⟩ := h1
  refine ⟨f4Elem (conjK s i j), fun k => ?_⟩
  have hr := f4Realizes_elem hlt
  simp only [condConj, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  rw [smul_single_eq_codeRoots' hr k]
  exact Int.dvd_of_emod_eq_zero (hc k)

@[expose] def trCode : ℕ := 340

@[expose] noncomputable def trElem : WeylGroup ReeTag.F4.tag := f4Elem trCode

theorem f4Realizes_trElem :
    F4Realizes trElem (f4Code trCode) :=
  f4Realizes_elem (k := trCode) (by decide)

section Neg

theorem lin4_dualRoot_w0Col (j : Fin ReeTag.F4.tag.rank) :
    lin4 (ReeTag.F4.dualRoot (w0Col (ReeTag.F4.perm j))) w0Col =
      -(Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) := by
  funext l
  fin_cases j <;> fin_cases l <;> decide +kernel

theorem wPhi2_mul_weylPerm_smul (j : Fin ReeTag.F4.tag.rank) :
    (wPhi2 * ReeTag.F4.weylPerm wPhi2) • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) =
      -(Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) := by
  have hj : (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) =
      ReeTag.F4.dualRoot (Pi.single (ReeTag.F4.perm j) 1) := by
    rw [ReeTag.dualRoot_single, ReeTag.perm_perm]
  rw [mul_smul]
  conv_lhs => rw [hj]
  rw [← ReeTag.dualRoot_smul wPhi2 (isRoot_single _ _), wPhi2_smul_single, wPhi2_smul]
  exact lin4_dualRoot_w0Col j

theorem wPhi2_mul_weylPerm :
    wPhi2 * ReeTag.F4.weylPerm wPhi2 = CFSG.RankThree.PartOne.KF4.qpNeg := by
  refine ext_single fun j => ?_
  rw [wPhi2_mul_weylPerm_smul]
  exact (CFSG.RankThree.PartOne.KF4.qpNeg_smul _).symm

end Neg

end CFSG.RankThree.PartTwo.Sec8.ReeF4Conj2Proof
