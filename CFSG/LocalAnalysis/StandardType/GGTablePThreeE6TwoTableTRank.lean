module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoTableTBridge

import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTRank

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open Certificates.Data.E6TableT

private def e6tRank_qv (v : Vec) : Fin Tag.E6.rank → ℚ := fun i => ((v.getD i 0 : ℤ) : ℚ)

private def e6tRank_co (γ : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℚ := fun i => (γ i : ℚ)

private def e6tRank_zro (v : Vec) : Fin Tag.E6.rank → ℤ := fun i => v.getD i 0

private theorem e6tRank_co_eq_qv_ofFn (γ : Fin Tag.E6.rank → ℤ) :
    e6tRank_co γ = e6tRank_qv (List.ofFn γ) := by
  funext i
  simp only [e6tRank_co, e6tRank_qv]
  have hi : (i : ℕ) < (List.ofFn γ).length := by
    rw [List.length_ofFn]; exact i.isLt
  rw [List.getD_eq_getElem _ _ hi, List.getElem_ofFn]

private theorem e6tRank_ofFn_zro (v : Vec) (hv : v.length = 6) :
    List.ofFn (e6tRank_zro v) = v := by
  apply List.ext_getElem
  · rw [List.length_ofFn, hv]; rfl
  · intro n h1 h2
    rw [List.getElem_ofFn]
    change v.getD n 0 = v[n]
    rw [List.getD_eq_getElem v 0 h2]

private theorem e6tRank_mem_co_classSet {l : List Vec} {v : Vec} (hv : v ∈ l)
    (hlen : v.length = 6) : e6tRank_qv v ∈ e6tRank_co '' classSet l := by
  refine ⟨e6tRank_zro v, ?_, ?_⟩
  · show List.ofFn (e6tRank_zro v) ∈ l
    rw [e6tRank_ofFn_zro v hlen]; exact hv
  · rw [e6tRank_co_eq_qv_ofFn, e6tRank_ofFn_zro v hlen]

private theorem e6tRank_mem_span_range_of_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {b : ι → (Fin Tag.E6.rank → ℚ)} {x : Fin Tag.E6.rank → ℚ} {c : ι → ℚ}
    (h : x = ∑ j, c j • b j) : x ∈ Submodule.span ℚ (Set.range b) := by
  rw [h]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

private theorem e6tRank_forall_mem_of_all_decide {l : List Vec} {P : Vec → Prop} [DecidablePred P]
    (h : (l.all fun v => decide (P v)) = true) : ∀ v ∈ l, P v :=
  fun v hv => of_decide_eq_true ((List.all_eq_true.1 h) v hv)

private def e6tRank_coordProj {ι : Type*} (σ : ι → Fin Tag.E6.rank) :
    (Fin Tag.E6.rank → ℚ) →ₗ[ℚ] (ι → ℚ) where
  toFun x := fun i => x (σ i)
  map_add' x y := by funext i; rfl
  map_smul' a x := by funext i; rfl

private theorem e6tRank_linearIndependent_of_submatrix {n : ℕ}
    (b : Fin n → (Fin Tag.E6.rank → ℚ)) (σ : Fin n → Fin Tag.E6.rank)
    (hdet : Matrix.det (fun i j => b i (σ j) : Matrix (Fin n) (Fin n) ℚ) ≠ 0) :
    LinearIndependent ℚ b :=
  LinearIndependent.of_comp (e6tRank_coordProj σ)
    (Matrix.linearIndependent_rows_of_det_ne_zero hdet)

private theorem e6tRank_co_sum_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℤ) (z : ι → (Fin Tag.E6.rank → ℤ)) :
    e6tRank_co (∑ j, c j • z j) = ∑ j, ((c j : ℤ) : ℚ) • e6tRank_co (z j) := by
  funext i
  simp only [e6tRank_co, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  rfl

private theorem e6tRank_compRank_classSet_eq {n : ℕ} (l : List Vec)
    (b : Fin n → (Fin Tag.E6.rank → ℚ)) (hb : LinearIndependent ℚ b)
    (hbS : ∀ i, b i ∈ e6tRank_co '' classSet l)
    (hgen : ∀ v ∈ l, e6tRank_qv v ∈ Submodule.span ℚ (Set.range b)) :
    compRank (classSet l) = n := by
  have hspan_eq : Submodule.span ℚ (e6tRank_co '' classSet l) =
      Submodule.span ℚ (Set.range b) := by
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro x ⟨γ, hγ, rfl⟩
      rw [e6tRank_co_eq_qv_ofFn]
      exact hgen (List.ofFn γ) hγ
    · rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      exact Submodule.subset_span (hbS i)
  rw [compRank]
  change Module.finrank ℚ (Submodule.span ℚ (e6tRank_co '' classSet l)) = n
  rw [hspan_eq, finrank_span_eq_card hb, Fintype.card_fin]

private def e6tRank_lA4_20 : List Vec :=
  [[1,0,0,0,0,0],[0,0,1,0,0,0],[-1,0,0,0,0,0],[1,0,1,0,0,0],[0,0,-1,0,0,0],
   [0,0,1,1,0,0],[-1,0,-1,0,0,0],[1,0,1,1,0,0],[0,1,1,1,0,0],[0,0,-1,-1,0,0],
   [-1,0,-1,-1,0,0],[1,1,1,1,0,0],[0,-1,-1,-1,0,0],[-1,-1,-1,-1,0,0],[0,0,0,1,0,0],
   [0,1,0,1,0,0],[0,0,0,-1,0,0],[0,-1,0,-1,0,0],[0,1,0,0,0,0],[0,-1,0,0,0,0]]

private def e6tRank_bvecA4 : Fin 4 → Vec :=
  ![[1,0,0,0,0,0], [0,0,1,0,0,0], [0,0,0,1,0,0], [0,1,0,0,0,0]]
private def e6tRank_bA4 : Fin 4 → (Fin Tag.E6.rank → ℚ) :=
  fun j => e6tRank_qv (e6tRank_bvecA4 j)
private def e6tRank_coeffZA4 (v : Vec) : Fin 4 → ℤ :=
  ![v.getD 0 0, v.getD 2 0, v.getD 3 0, v.getD 1 0]

private theorem e6tRank_hZA4 : ∀ v ∈ e6tRank_lA4_20,
    e6tRank_zro v = ∑ j, (e6tRank_coeffZA4 v j) • e6tRank_zro (e6tRank_bvecA4 j) :=
  e6tRank_forall_mem_of_all_decide (by decide +kernel)

private theorem e6tRank_hgenA4 : ∀ v ∈ e6tRank_lA4_20,
    e6tRank_qv v = ∑ j, ((e6tRank_coeffZA4 v j : ℤ) : ℚ) • e6tRank_bA4 j := by
  intro v hv
  have h := congrArg e6tRank_co (e6tRank_hZA4 v hv)
  rwa [e6tRank_co_sum_smul, show e6tRank_co (e6tRank_zro v) = e6tRank_qv v from rfl] at h

private theorem e6tRank_hbSA4 : ∀ i, e6tRank_bA4 i ∈ e6tRank_co '' classSet e6tRank_lA4_20 := by
  intro i
  fin_cases i
  · show e6tRank_qv [1,0,0,0,0,0] ∈ e6tRank_co '' classSet e6tRank_lA4_20
    exact e6tRank_mem_co_classSet (by decide) (by decide)
  · show e6tRank_qv [0,0,1,0,0,0] ∈ e6tRank_co '' classSet e6tRank_lA4_20
    exact e6tRank_mem_co_classSet (by decide) (by decide)
  · show e6tRank_qv [0,0,0,1,0,0] ∈ e6tRank_co '' classSet e6tRank_lA4_20
    exact e6tRank_mem_co_classSet (by decide) (by decide)
  · show e6tRank_qv [0,1,0,0,0,0] ∈ e6tRank_co '' classSet e6tRank_lA4_20
    exact e6tRank_mem_co_classSet (by decide) (by decide)

private theorem e6tRank_hbA4 : LinearIndependent ℚ e6tRank_bA4 := by
  refine e6tRank_linearIndependent_of_submatrix e6tRank_bA4 (![0,2,3,1] : Fin 4 → Fin Tag.E6.rank) ?_
  decide +kernel

private theorem e6tRank_compRank_A4 : compRank (classSet e6tRank_lA4_20) = 4 :=
  e6tRank_compRank_classSet_eq e6tRank_lA4_20 e6tRank_bA4 e6tRank_hbA4 e6tRank_hbSA4
    (fun v hv => e6tRank_mem_span_range_of_sum (e6tRank_hgenA4 v hv))

private def e6tRank_lA1_2 : List Vec := [[0,0,0,0,0,1],[0,0,0,0,0,-1]]

private def e6tRank_bvecA1 : Fin 1 → Vec := ![[0,0,0,0,0,1]]
private def e6tRank_bA1 : Fin 1 → (Fin Tag.E6.rank → ℚ) :=
  fun j => e6tRank_qv (e6tRank_bvecA1 j)
private def e6tRank_coeffZA1 (v : Vec) : Fin 1 → ℤ := ![v.getD 5 0]

private theorem e6tRank_hZA1 : ∀ v ∈ e6tRank_lA1_2,
    e6tRank_zro v = ∑ j, (e6tRank_coeffZA1 v j) • e6tRank_zro (e6tRank_bvecA1 j) :=
  e6tRank_forall_mem_of_all_decide (by decide +kernel)

private theorem e6tRank_hgenA1 : ∀ v ∈ e6tRank_lA1_2,
    e6tRank_qv v = ∑ j, ((e6tRank_coeffZA1 v j : ℤ) : ℚ) • e6tRank_bA1 j := by
  intro v hv
  have h := congrArg e6tRank_co (e6tRank_hZA1 v hv)
  rwa [e6tRank_co_sum_smul, show e6tRank_co (e6tRank_zro v) = e6tRank_qv v from rfl] at h

private theorem e6tRank_hbSA1 : ∀ i, e6tRank_bA1 i ∈ e6tRank_co '' classSet e6tRank_lA1_2 := by
  intro i
  fin_cases i
  · show e6tRank_qv [0,0,0,0,0,1] ∈ e6tRank_co '' classSet e6tRank_lA1_2
    exact e6tRank_mem_co_classSet (by decide) (by decide)

private theorem e6tRank_hbA1 : LinearIndependent ℚ e6tRank_bA1 := by
  refine e6tRank_linearIndependent_of_submatrix e6tRank_bA1 (![5] : Fin 1 → Fin Tag.E6.rank) ?_
  decide +kernel

private theorem e6tRank_compRank_A1 : compRank (classSet e6tRank_lA1_2) = 1 :=
  e6tRank_compRank_classSet_eq e6tRank_lA1_2 e6tRank_bA1 e6tRank_hbA1 e6tRank_hbSA1
    (fun v hv => e6tRank_mem_span_range_of_sum (e6tRank_hgenA1 v hv))

private theorem e6tRank_classes_A4A1 :
    classes (reps.getD 1 []) = [e6tRank_lA4_20, e6tRank_lA1_2] := by
  decide +kernel

theorem classes_compRank_eq_rankOf (k : Fin 5) (l : List Vec) (hl : l ∈ classes (reps.getD k [])) :
    compRank (classSet l) = Certificates.Data.E6TableTTwo.rankOf l.length := by
  fin_cases k
  ·
    have hmap : (classes (reps.getD 0 [])).map List.length = [6, 6, 6] := by
      have h := congrArg (fun (L : List (List ℕ)) => L.getD 0 []) classes_lengths
      rw [show (List.range 5 : List ℕ) = [0, 1, 2, 3, 4] from rfl] at h
      simp only [List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ] at h
      exact h
    have hlen : l.length = 6 := by
      have hmem : l.length ∈ (classes (reps.getD 0 [])).map List.length :=
        List.mem_map.2 ⟨l, hl, rfl⟩
      rw [hmap] at hmem
      simpa using hmem
    have hc : compRank (classSet l) = 2 := (classes_compRank 0 l hl).1 rfl
    rw [hlen, hc]
    decide
  ·
    rw [e6tRank_classes_A4A1] at hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · rw [e6tRank_compRank_A4]
      decide
    · rw [e6tRank_compRank_A1]
      decide
  ·
    have hmap : (classes (reps.getD 2 [])).map List.length = [24] := by
      have h := congrArg (fun (L : List (List ℕ)) => L.getD 2 []) classes_lengths
      rw [show (List.range 5 : List ℕ) = [0, 1, 2, 3, 4] from rfl] at h
      simp only [List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ] at h
      exact h
    have hlen : l.length = 24 := by
      have hmem : l.length ∈ (classes (reps.getD 2 [])).map List.length :=
        List.mem_map.2 ⟨l, hl, rfl⟩
      rw [hmap] at hmem
      simpa using hmem
    have hc : compRank (classSet l) = 4 := (classes_compRank 2 l hl).2.1 rfl
    rw [hlen, hc]
    decide
  ·
    have hmap : (classes (reps.getD 3 [])).map List.length = [30] := by
      have h := congrArg (fun (L : List (List ℕ)) => L.getD 3 []) classes_lengths
      rw [show (List.range 5 : List ℕ) = [0, 1, 2, 3, 4] from rfl] at h
      simp only [List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ] at h
      exact h
    have hlen : l.length = 30 := by
      have hmem : l.length ∈ (classes (reps.getD 3 [])).map List.length :=
        List.mem_map.2 ⟨l, hl, rfl⟩
      rw [hmap] at hmem
      simpa using hmem
    have hc : compRank (classSet l) = 5 := (classes_compRank 3 l hl).2.2.1 rfl
    rw [hlen, hc]
    decide
  ·
    have hmap : (classes (reps.getD 4 [])).map List.length = [40] := by
      have h := congrArg (fun (L : List (List ℕ)) => L.getD 4 []) classes_lengths
      rw [show (List.range 5 : List ℕ) = [0, 1, 2, 3, 4] from rfl] at h
      simp only [List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ] at h
      exact h
    have hlen : l.length = 40 := by
      have hmem : l.length ∈ (classes (reps.getD 4 [])).map List.length :=
        List.mem_map.2 ⟨l, hl, rfl⟩
      rw [hmap] at hmem
      simpa using hmem
    have hc : compRank (classSet l) = 5 := (classes_compRank 4 l hl).2.2.2 rfl
    rw [hlen, hc]
    decide

end CFSG.StandardType.TablePThreeKG

end
