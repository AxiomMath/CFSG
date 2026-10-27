module

public import CFSG.Mathlib.Decide.Bounded
public import CFSG.Mathlib.Decide.Nodup
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd
import CFSG.LocalAnalysis.StandardType.GGTableBE6ThreeWeylModule

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.StandardType.TableBExc.E6Three
open CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley

open scoped CFSG.Decide.Bounded

local instance : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def ovgE2 : Fin Tag.E6.rank → ZMod 3 := ![0, 1, 0, 0, 0, 0]

@[expose] def ovgBase30 : Fin Tag.E6.rank → ZMod 3 := ![0, 0, 0, 0, 1, 1]

@[expose] def ovgBase20a : Fin Tag.E6.rank → ZMod 3 := ![0, 0, 1, 0, 0, 2]

@[expose] def ovgBase20b : Fin Tag.E6.rank → ZMod 3 := ![0, 0, 2, 0, 0, 1]

@[expose] def ovgClass30 :
    List ((Fin Tag.E6.rank → ZMod 3) × List (Fin Tag.E6.rank)) :=
  ([
     (![0, 0, 0, 0, 1, 1], []),
     (![0, 0, 0, 0, 2, 2], [5]),
     (![0, 0, 0, 1, 1, 1], [4, 5]),
     (![0, 0, 0, 1, 2, 2], [4]),
     (![0, 0, 0, 2, 1, 1], [5, 4]),
     (![0, 0, 0, 2, 2, 2], [4, 5, 4]),
     (![0, 1, 1, 1, 1, 0], [4, 3, 5, 4]),
     (![0, 1, 1, 2, 0, 2], [4, 3]),
     (![0, 1, 1, 2, 2, 1], [4, 3, 5]),
     (![0, 2, 2, 1, 0, 1], [5, 4, 3]),
     (![0, 2, 2, 1, 1, 2], [4, 5, 4, 3]),
     (![0, 2, 2, 2, 2, 0], [4, 3, 5, 4, 3]),
     (![1, 0, 1, 0, 0, 0], [4, 3, 2, 0, 5, 4, 3, 2]),
     (![1, 0, 1, 1, 0, 0], [4, 3, 2, 5, 4, 3]),
     (![1, 0, 1, 2, 0, 0], [4, 3, 2, 5, 4, 3, 2, 0]),
     (![1, 1, 2, 0, 0, 2], [4, 3, 2]),
     (![1, 1, 2, 0, 2, 1], [4, 3, 2, 5]),
     (![1, 1, 2, 2, 1, 0], [4, 3, 2, 5, 4]),
     (![1, 2, 0, 0, 0, 1], [5, 4, 3, 2, 0]),
     (![1, 2, 0, 0, 1, 2], [4, 5, 4, 3, 2, 0]),
     (![1, 2, 0, 1, 2, 0], [4, 3, 5, 4, 3, 2, 0]),
     (![2, 0, 2, 0, 0, 0], [4, 3, 2, 0, 5, 4, 3, 2, 0]),
     (![2, 0, 2, 1, 0, 0], [4, 3, 2, 0, 5, 4, 3]),
     (![2, 0, 2, 2, 0, 0], [4, 3, 2, 5, 4, 3, 2]),
     (![2, 1, 0, 0, 0, 2], [4, 3, 2, 0]),
     (![2, 1, 0, 0, 2, 1], [4, 3, 2, 0, 5]),
     (![2, 1, 0, 2, 1, 0], [4, 3, 2, 0, 5, 4]),
     (![2, 2, 1, 0, 0, 1], [5, 4, 3, 2]),
     (![2, 2, 1, 0, 1, 2], [4, 5, 4, 3, 2]),
     (![2, 2, 1, 1, 2, 0], [4, 3, 5, 4, 3, 2]),
    ] : List ((Fin Tag.E6.rank → ZMod 3) × List (Fin Tag.E6.rank)))

@[expose] def ovgClass20a :
    List ((Fin Tag.E6.rank → ZMod 3) × List (Fin Tag.E6.rank)) :=
  ([
     (![0, 0, 1, 0, 0, 2], []),
     (![0, 0, 1, 0, 2, 1], [5]),
     (![0, 0, 1, 2, 1, 0], [5, 4]),
     (![0, 1, 2, 0, 0, 1], [2, 0, 3, 2, 5]),
     (![0, 1, 2, 0, 1, 2], [2, 0, 3, 2]),
     (![0, 1, 2, 1, 2, 0], [2, 0, 3, 2, 4]),
     (![0, 2, 0, 1, 0, 0], [5, 4, 3]),
     (![0, 2, 0, 2, 0, 0], [2, 0, 3, 2, 4, 3]),
     (![1, 0, 2, 0, 1, 0], [2, 5, 4]),
     (![1, 0, 2, 1, 0, 2], [2]),
     (![1, 0, 2, 1, 2, 1], [2, 5]),
     (![1, 1, 0, 0, 2, 0], [2, 3, 4]),
     (![1, 1, 0, 2, 0, 1], [2, 3, 5]),
     (![1, 1, 0, 2, 1, 2], [2, 3]),
     (![2, 0, 0, 0, 1, 0], [2, 0, 5, 4]),
     (![2, 0, 0, 1, 0, 2], [2, 0]),
     (![2, 0, 0, 1, 2, 1], [2, 0, 5]),
     (![2, 1, 1, 0, 2, 0], [2, 0, 3, 4]),
     (![2, 1, 1, 2, 0, 1], [2, 0, 3, 5]),
     (![2, 1, 1, 2, 1, 2], [2, 0, 3]),
    ] : List ((Fin Tag.E6.rank → ZMod 3) × List (Fin Tag.E6.rank)))

@[expose] def ovgClass20b :
    List ((Fin Tag.E6.rank → ZMod 3) × List (Fin Tag.E6.rank)) :=
  ([
     (![0, 0, 2, 0, 0, 1], []),
     (![0, 0, 2, 0, 1, 2], [5]),
     (![0, 0, 2, 1, 2, 0], [5, 4]),
     (![0, 1, 0, 1, 0, 0], [2, 0, 3, 2, 4, 3]),
     (![0, 1, 0, 2, 0, 0], [5, 4, 3]),
     (![0, 2, 1, 0, 0, 2], [2, 0, 3, 2, 5]),
     (![0, 2, 1, 0, 2, 1], [2, 0, 3, 2]),
     (![0, 2, 1, 2, 1, 0], [2, 0, 3, 2, 4]),
     (![1, 0, 0, 0, 2, 0], [2, 0, 5, 4]),
     (![1, 0, 0, 2, 0, 1], [2, 0]),
     (![1, 0, 0, 2, 1, 2], [2, 0, 5]),
     (![1, 2, 2, 0, 1, 0], [2, 0, 3, 4]),
     (![1, 2, 2, 1, 0, 2], [2, 0, 3, 5]),
     (![1, 2, 2, 1, 2, 1], [2, 0, 3]),
     (![2, 0, 1, 0, 2, 0], [2, 5, 4]),
     (![2, 0, 1, 2, 0, 1], [2]),
     (![2, 0, 1, 2, 1, 2], [2, 5]),
     (![2, 2, 0, 0, 1, 0], [2, 3, 4]),
     (![2, 2, 0, 1, 0, 2], [2, 3, 5]),
     (![2, 2, 0, 1, 2, 1], [2, 3]),
    ] : List ((Fin Tag.E6.rank → ZMod 3) × List (Fin Tag.E6.rank)))

@[expose] def ovgPoints : List (Fin Tag.E6.rank → ZMod 3) :=
  ovgE2 :: (-ovgE2) ::
    (ovgClass30.map Prod.fst ++ ovgClass20a.map Prod.fst ++ ovgClass20b.map Prod.fst)

private def ovgKey (y : Fin Tag.E6.rank → ZMod 3) : ℕ :=
  ∑ i : Fin Tag.E6.rank, (y i).val * 3 ^ (i : ℕ)

theorem ovgPoints_nodup : ovgPoints.Nodup := by
  refine CFSG.Decide.nodup_of_bitsetNodup ovgKey ?_
  decide +kernel

theorem ovgPoints_length : ovgPoints.length = 72 := by
  decide +kernel

theorem ovgE2_mem : ovgE2 ∈ ovgPoints := List.mem_cons_self ..

theorem ovgPoints_adRefl : ∀ y ∈ ovgPoints, ∀ i : Fin Tag.E6.rank,
    adRefl .E6 3 i y ∈ ovgPoints := by
  decide +kernel

theorem ovgClass30_acts : ∀ p ∈ ovgClass30, adWord .E6 3 p.2 p.1 = ovgBase30 := by
  decide +kernel

theorem ovgClass30_letters : ∀ p ∈ ovgClass30, ∀ i ∈ p.2, i.val ≠ 1 := by
  decide +kernel

theorem ovgClass20a_acts : ∀ p ∈ ovgClass20a, adWord .E6 3 p.2 p.1 = ovgBase20a := by
  decide +kernel

theorem ovgClass20a_letters : ∀ p ∈ ovgClass20a, ∀ i ∈ p.2, i.val ≠ 1 := by
  decide +kernel

theorem ovgClass20b_acts : ∀ p ∈ ovgClass20b, adWord .E6 3 p.2 p.1 = ovgBase20b := by
  decide +kernel

theorem ovgClass20b_letters : ∀ p ∈ ovgClass20b, ∀ i ∈ p.2, i.val ≠ 1 := by
  decide +kernel

private theorem adWord_append (l₁ l₂ : List (Fin Tag.E6.rank))
    (x : Fin Tag.E6.rank → ZMod 3) :
    adWord .E6 3 (l₁ ++ l₂) x = adWord .E6 3 l₁ (adWord .E6 3 l₂ x) :=
  List.foldr_append ..

private theorem adWord_reverse (ω : List (Fin Tag.E6.rank)) (x : Fin Tag.E6.rank → ZMod 3) :
    adWord .E6 3 ω.reverse (adWord .E6 3 ω x) = x := by
  induction ω generalizing x with
  | nil => rfl
  | cons i ω ih =>
    rw [List.reverse_cons, adWord_append]
    change adWord .E6 3 (List.reverse ω) (adRefl .E6 3 i (adRefl .E6 3 i
      (adWord .E6 3 ω x))) = x
    rw [adRefl_adRefl, ih]

private theorem adWord_mem {A : Finset (Fin Tag.E6.rank → ZMod 3)}
    (hcl : ∀ y ∈ A, ∀ i : Fin Tag.E6.rank, i.val ≠ 1 → adRefl .E6 3 i y ∈ A)
    {ω : List (Fin Tag.E6.rank)} (hω : ∀ i ∈ ω, i.val ≠ 1)
    {y : Fin Tag.E6.rank → ZMod 3} (hy : y ∈ A) : adWord .E6 3 ω y ∈ A := by
  induction ω generalizing y with
  | nil => simpa [adWord] using hy
  | cons i ω ih =>
    have hi : i.val ≠ 1 := hω i (List.mem_cons_self ..)
    have hω' : ∀ j ∈ ω, j.val ≠ 1 := fun j hj => hω j (List.mem_cons_of_mem i hj)
    exact hcl _ (ih hω' hy) i hi

private theorem adWord_mem_all {A : Finset (Fin Tag.E6.rank → ZMod 3)}
    (hcl : ∀ y ∈ A, ∀ i : Fin Tag.E6.rank, adRefl .E6 3 i y ∈ A)
    {ω : List (Fin Tag.E6.rank)} {y : Fin Tag.E6.rank → ZMod 3} (hy : y ∈ A) :
    adWord .E6 3 ω y ∈ A := by
  induction ω generalizing y with
  | nil => simpa [adWord] using hy
  | cons i ω ih => exact hcl _ (ih hy) i

theorem ovgPoints_adAct_mem (w : WeylGroup .E6) :
    adAct .E6 3 w ovgE2 ∈ ovgPoints.toFinset := by
  obtain ⟨ω, rfl⟩ := (coxeterSystem .E6).wordProd_surjective w
  rw [← adWord_eq_adAct]
  have hcl : ∀ y ∈ ovgPoints.toFinset, ∀ i : Fin Tag.E6.rank,
      adRefl .E6 3 i y ∈ ovgPoints.toFinset := by
    intro y hy i
    exact List.mem_toFinset.mpr (ovgPoints_adRefl y (List.mem_toFinset.mp hy) i)
  exact adWord_mem_all hcl (List.mem_toFinset.mpr ovgE2_mem)

private theorem ovgClass_exists_word
    {l : List ((Fin Tag.E6.rank → ZMod 3) × List (Fin Tag.E6.rank))}
    {b : Fin Tag.E6.rank → ZMod 3}
    (hacts : ∀ p ∈ l, adWord .E6 3 p.2 p.1 = b)
    (hletters : ∀ p ∈ l, ∀ i ∈ p.2, i.val ≠ 1)
    {y : Fin Tag.E6.rank → ZMod 3} (hy : y ∈ l.map Prod.fst) :
    ∃ w : List (Fin Tag.E6.rank), (∀ i ∈ w, i.val ≠ 1) ∧ adWord .E6 3 w y = b := by
  obtain ⟨p, hp, hpy⟩ := List.mem_map.1 hy
  refine ⟨p.2, hletters p hp, ?_⟩
  rw [← hpy]
  exact hacts p hp

private theorem ovgClassPts_subset_of_inter
    {l : List ((Fin Tag.E6.rank → ZMod 3) × List (Fin Tag.E6.rank))}
    {b : Fin Tag.E6.rank → ZMod 3}
    (hacts : ∀ p ∈ l, adWord .E6 3 p.2 p.1 = b)
    (hletters : ∀ p ∈ l, ∀ i ∈ p.2, i.val ≠ 1)
    {A : Finset (Fin Tag.E6.rank → ZMod 3)}
    (hcl : ∀ y ∈ A, ∀ i : Fin Tag.E6.rank, i.val ≠ 1 → adRefl .E6 3 i y ∈ A)
    (hmeet : ∃ y ∈ A, y ∈ (l.map Prod.fst).toFinset) :
    (l.map Prod.fst).toFinset ⊆ A := by
  obtain ⟨y, hyA, hyC⟩ := hmeet
  obtain ⟨w, hw, hwb⟩ := ovgClass_exists_word hacts hletters (List.mem_toFinset.mp hyC)
  have hbase : b ∈ A := by
    rw [← hwb]
    exact adWord_mem hcl hw hyA
  intro z hzC
  obtain ⟨wz, hwz, hwzb⟩ := ovgClass_exists_word hacts hletters (List.mem_toFinset.mp hzC)
  have hz : z = adWord .E6 3 (List.reverse wz) b := by
    rw [← hwzb, adWord_reverse]
  rw [hz]
  exact adWord_mem hcl (fun i hi => hwz i (List.mem_reverse.mp hi)) hbase

private def ovgE2Pts : Finset (Fin Tag.E6.rank → ZMod 3) := {ovgE2}

private def ovgNegE2Pts : Finset (Fin Tag.E6.rank → ZMod 3) := {-ovgE2}

private def ovgClass30Pts : Finset (Fin Tag.E6.rank → ZMod 3) :=
  (ovgClass30.map Prod.fst).toFinset

private def ovgClass20aPts : Finset (Fin Tag.E6.rank → ZMod 3) :=
  (ovgClass20a.map Prod.fst).toFinset

private def ovgClass20bPts : Finset (Fin Tag.E6.rank → ZMod 3) :=
  (ovgClass20b.map Prod.fst).toFinset

private theorem ovgPoints_toFinset_eq :
    ovgPoints.toFinset = ovgE2Pts ∪ ovgNegE2Pts ∪ ovgClass30Pts ∪ ovgClass20aPts ∪
      ovgClass20bPts := by
  ext y
  simp [ovgPoints, ovgE2Pts, ovgNegE2Pts, ovgClass30Pts, ovgClass20aPts,
    ovgClass20bPts, List.mem_append]

private theorem ovgE2Pts_subset {A : Finset (Fin Tag.E6.rank → ZMod 3)} (h : ovgE2 ∈ A) :
    ovgE2Pts ⊆ A := by
  intro y hy
  have hy' : y = ovgE2 := by simpa [ovgE2Pts] using hy
  rwa [hy']

theorem ovg_eq_allPoints_or_subset {A : Finset (Fin Tag.E6.rank → ZMod 3)}
    (hA : A ⊆ ovgPoints.toFinset) (he2 : ovgE2 ∈ A)
    (hcl : ∀ y ∈ A, ∀ i : Fin Tag.E6.rank, i.val ≠ 1 → adRefl .E6 3 i y ∈ A)
    (hdvd : A.card ∣ 72) :
    A = ovgPoints.toFinset ∨ A ⊆ {ovgE2, -ovgE2} := by
  have hAeq : A = ovgE2Pts ∪ (A ∩ ovgNegE2Pts) ∪ (A ∩ ovgClass30Pts) ∪
      (A ∩ ovgClass20aPts) ∪ (A ∩ ovgClass20bPts) := by
    have h := congrArg (fun s => A ∩ s) ovgPoints_toFinset_eq
    rw [Finset.inter_eq_left.mpr hA] at h
    conv_lhs => rw [h]
    simp only [Finset.inter_union_distrib_left,
      Finset.inter_eq_right.mpr (ovgE2Pts_subset he2)]
  have hK1 : A ∩ ovgNegE2Pts = if -ovgE2 ∈ A then ovgNegE2Pts else ∅ := by
    by_cases h : -ovgE2 ∈ A
    · rw [if_pos h]
      apply Finset.inter_eq_right.mpr
      intro y hy
      have hy' : y = -ovgE2 := by simpa [ovgNegE2Pts] using hy
      rwa [hy']
    · rw [if_neg h]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      rw [Finset.mem_inter] at hy
      have hy' : y = -ovgE2 := by simpa [ovgNegE2Pts] using hy.2
      rw [hy'] at hy
      exact h hy.1
  have hK2 : A ∩ ovgClass30Pts = if (A ∩ ovgClass30Pts).Nonempty then ovgClass30Pts else ∅ := by
    by_cases h : (A ∩ ovgClass30Pts).Nonempty
    · rw [if_pos h]
      apply Finset.inter_eq_right.mpr
      obtain ⟨y, hy⟩ := h
      exact ovgClassPts_subset_of_inter ovgClass30_acts ovgClass30_letters hcl
        ⟨y, Finset.mem_inter.mp hy⟩
    · rw [if_neg h]
      exact Finset.not_nonempty_iff_eq_empty.mp h
  have hK3 : A ∩ ovgClass20aPts =
      if (A ∩ ovgClass20aPts).Nonempty then ovgClass20aPts else ∅ := by
    by_cases h : (A ∩ ovgClass20aPts).Nonempty
    · rw [if_pos h]
      apply Finset.inter_eq_right.mpr
      obtain ⟨y, hy⟩ := h
      exact ovgClassPts_subset_of_inter ovgClass20a_acts ovgClass20a_letters hcl
        ⟨y, Finset.mem_inter.mp hy⟩
    · rw [if_neg h]
      exact Finset.not_nonempty_iff_eq_empty.mp h
  have hK4 : A ∩ ovgClass20bPts =
      if (A ∩ ovgClass20bPts).Nonempty then ovgClass20bPts else ∅ := by
    by_cases h : (A ∩ ovgClass20bPts).Nonempty
    · rw [if_pos h]
      apply Finset.inter_eq_right.mpr
      obtain ⟨y, hy⟩ := h
      exact ovgClassPts_subset_of_inter ovgClass20b_acts ovgClass20b_letters hcl
        ⟨y, Finset.mem_inter.mp hy⟩
    · rw [if_neg h]
      exact Finset.not_nonempty_iff_eq_empty.mp h
  rw [hK1, hK2, hK3, hK4] at hAeq
  have hcard : A.card = 1 + (if -ovgE2 ∈ A then 1 else 0) +
      (if (A ∩ ovgClass30Pts).Nonempty then 30 else 0) +
      (if (A ∩ ovgClass20aPts).Nonempty then 20 else 0) +
      (if (A ∩ ovgClass20bPts).Nonempty then 20 else 0) := by
    rw [hAeq]
    by_cases h1 : -ovgE2 ∈ A <;>
    by_cases h2 : (A ∩ ovgClass30Pts).Nonempty <;>
    by_cases h3 : (A ∩ ovgClass20aPts).Nonempty <;>
    by_cases h4 : (A ∩ ovgClass20bPts).Nonempty <;>
    simp only [h1, h2, h3, h4] <;>
    decide +kernel
  have hall : -ovgE2 ∈ A → (A ∩ ovgClass30Pts).Nonempty →
      (A ∩ ovgClass20aPts).Nonempty → (A ∩ ovgClass20bPts).Nonempty →
      A = ovgPoints.toFinset := by
    intro h1 h2 h3 h4
    rw [hAeq, if_pos h1, if_pos h2, if_pos h3, if_pos h4]
    exact ovgPoints_toFinset_eq.symm
  have hsmall : ¬ (A ∩ ovgClass30Pts).Nonempty → ¬ (A ∩ ovgClass20aPts).Nonempty →
      ¬ (A ∩ ovgClass20bPts).Nonempty → A ⊆ {ovgE2, -ovgE2} := by
    intro h2 h3 h4 y hy
    have hy' : y ∈ ovgE2Pts ∪ ovgNegE2Pts ∪ ovgClass30Pts ∪ ovgClass20aPts ∪
        ovgClass20bPts := by
      rw [← ovgPoints_toFinset_eq]
      exact hA hy
    simp only [Finset.mem_union, ovgE2Pts, ovgNegE2Pts, Finset.mem_insert,
      Finset.mem_singleton] at hy' ⊢
    rcases hy' with ((((hy0 | hy1) | hy2) | hy3) | hy4)
    · exact Or.inl hy0
    · exact Or.inr hy1
    · exact absurd ⟨y, Finset.mem_inter.mpr ⟨hy, hy2⟩⟩ h2
    · exact absurd ⟨y, Finset.mem_inter.mpr ⟨hy, hy3⟩⟩ h3
    · exact absurd ⟨y, Finset.mem_inter.mpr ⟨hy, hy4⟩⟩ h4
  rw [hcard] at hdvd
  by_cases h1 : -ovgE2 ∈ A <;>
  by_cases h2 : (A ∩ ovgClass30Pts).Nonempty <;>
  by_cases h3 : (A ∩ ovgClass20aPts).Nonempty <;>
  by_cases h4 : (A ∩ ovgClass20bPts).Nonempty
  all_goals
    first
    | (left; exact hall h1 h2 h3 h4)
    | (right; exact hsmall h2 h3 h4)
    | (simp only [h1, h2, h3, h4] at hdvd; norm_num at hdvd)

end CFSG.StandardType.E6QTwo

end
