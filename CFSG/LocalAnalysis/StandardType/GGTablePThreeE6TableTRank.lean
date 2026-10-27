module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTBridge
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTClasses

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open Certificates.Data.E6TableT

private def qv (v : Vec) : Fin Tag.E6.rank → ℚ := fun i => ((v.getD i 0 : ℤ) : ℚ)

private def co (γ : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℚ := fun i => (γ i : ℚ)

private def zro (v : Vec) : Fin Tag.E6.rank → ℤ := fun i => v.getD i 0

private theorem co_eq_qv_ofFn (γ : Fin Tag.E6.rank → ℤ) : co γ = qv (List.ofFn γ) := by
  funext i
  simp only [co, qv]
  have hi : (i : ℕ) < (List.ofFn γ).length := by
    rw [List.length_ofFn]; exact i.isLt
  rw [List.getD_eq_getElem _ _ hi, List.getElem_ofFn]

private theorem ofFn_zro (v : Vec) (hv : v.length = 6) : List.ofFn (zro v) = v := by
  apply List.ext_getElem
  · rw [List.length_ofFn, hv]; rfl
  · intro n h1 h2
    rw [List.getElem_ofFn]
    change v.getD n 0 = v[n]
    rw [List.getD_eq_getElem v 0 h2]

private theorem mem_co_classSet {l : List Vec} {v : Vec} (hv : v ∈ l) (hlen : v.length = 6) :
    qv v ∈ co '' classSet l := by
  refine ⟨zro v, ?_, ?_⟩
  · show List.ofFn (zro v) ∈ l
    rw [ofFn_zro v hlen]; exact hv
  · rw [co_eq_qv_ofFn, ofFn_zro v hlen]

private theorem mem_span_range_of_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {b : ι → (Fin Tag.E6.rank → ℚ)} {x : Fin Tag.E6.rank → ℚ} {c : ι → ℚ}
    (h : x = ∑ j, c j • b j) : x ∈ Submodule.span ℚ (Set.range b) := by
  rw [h]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

private theorem forall_mem_of_all_decide {l : List Vec} {P : Vec → Prop} [DecidablePred P]
    (h : (l.all fun v => decide (P v)) = true) : ∀ v ∈ l, P v :=
  fun v hv => of_decide_eq_true ((List.all_eq_true.1 h) v hv)

private def coordProj {ι : Type*} (σ : ι → Fin Tag.E6.rank) :
    (Fin Tag.E6.rank → ℚ) →ₗ[ℚ] (ι → ℚ) where
  toFun x := fun i => x (σ i)
  map_add' x y := by funext i; rfl
  map_smul' a x := by funext i; rfl

private theorem linearIndependent_of_submatrix {n : ℕ} (b : Fin n → (Fin Tag.E6.rank → ℚ))
    (σ : Fin n → Fin Tag.E6.rank)
    (hdet : Matrix.det (fun i j => b i (σ j) : Matrix (Fin n) (Fin n) ℚ) ≠ 0) :
    LinearIndependent ℚ b :=
  LinearIndependent.of_comp (coordProj σ) (Matrix.linearIndependent_rows_of_det_ne_zero hdet)

private theorem co_sum_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℤ) (z : ι → (Fin Tag.E6.rank → ℤ)) :
    co (∑ j, c j • z j) = ∑ j, ((c j : ℤ) : ℚ) • co (z j) := by
  funext i
  simp only [co, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  rfl

private theorem compRank_classSet_eq {n : ℕ} (l : List Vec) (b : Fin n → (Fin Tag.E6.rank → ℚ))
    (hb : LinearIndependent ℚ b)
    (hbS : ∀ i, b i ∈ co '' classSet l)
    (hgen : ∀ v ∈ l, qv v ∈ Submodule.span ℚ (Set.range b)) :
    compRank (classSet l) = n := by
  have hspan_eq : Submodule.span ℚ (co '' classSet l) = Submodule.span ℚ (Set.range b) := by
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro x ⟨γ, hγ, rfl⟩
      rw [co_eq_qv_ofFn]
      exact hgen (List.ofFn γ) hγ
    · rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      exact Submodule.subset_span (hbS i)
  rw [compRank]
  change Module.finrank ℚ (Submodule.span ℚ (co '' classSet l)) = n
  rw [hspan_eq, finrank_span_eq_card hb, Fintype.card_fin]

private def classStepInner (a : Vec) (q : List Vec × List Vec) (b : Vec) : List Vec × List Vec :=
  if q.1.contains b || q.2.contains b then q
  else if iform a b != 0 then (q.1, q.2 ++ [b]) else q

private theorem classStep_eq (ker acc frontier : List Vec) :
    classStep ker acc frontier =
      (frontier.foldl (fun q a => ker.foldl (classStepInner a) q) (acc, [])).2 := rfl

private theorem classStep_inner_subset (ker : List Vec) (a : Vec) (p : List Vec × List Vec) :
    ∀ b ∈ (ker.foldl (classStepInner a) p).2, b ∈ p.2 ++ ker := by
  induction ker generalizing p with
  | nil => intro b hb; exact List.mem_append.2 (Or.inl hb)
  | cons c cs ih =>
    intro b hb
    rw [List.foldl_cons] at hb
    have h1 : b ∈ (classStepInner a p c).2 ++ cs := ih (classStepInner a p c) b hb
    have h2 : (classStepInner a p c).2 ++ cs ⊆ p.2 ++ (c :: cs) := by
      unfold classStepInner
      by_cases hc : p.1.contains c || p.2.contains c
      · rw [if_pos hc]
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact List.mem_append.2 (Or.inl hx)
        · exact List.mem_append.2 (Or.inr (List.mem_cons_of_mem c hx))
      · rw [if_neg hc]
        by_cases hif : iform a c != 0
        · rw [if_pos hif]
          rw [List.append_assoc, List.singleton_append]
        · rw [if_neg hif]
          intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact List.mem_append.2 (Or.inl hx)
          · exact List.mem_append.2 (Or.inr (List.mem_cons_of_mem c hx))
    exact h2 h1

private theorem foldl_classStep_subset (ker : List Vec) (frontier : List Vec)
    (p : List Vec × List Vec) :
    ∀ b ∈ (frontier.foldl (fun q a => ker.foldl (classStepInner a) q) p).2,
      b ∈ p.2 ++ ker := by
  induction frontier generalizing p with
  | nil => intro b hb; exact List.mem_append.2 (Or.inl hb)
  | cons a as ih =>
    intro b hb
    rw [List.foldl_cons] at hb
    have h1 : b ∈ (ker.foldl (classStepInner a) p).2 ++ ker :=
      ih (ker.foldl (classStepInner a) p) b hb
    have h2 : (ker.foldl (classStepInner a) p).2 ++ ker ⊆ p.2 ++ ker := by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact classStep_inner_subset ker a p x hx
      · exact List.mem_append.2 (Or.inr hx)
    exact h2 h1

private theorem classStep_subset (ker acc frontier : List Vec) :
    ∀ b ∈ classStep ker acc frontier, b ∈ ker := by
  intro b hb
  rw [classStep_eq] at hb
  have h := foldl_classStep_subset ker frontier (acc, []) b hb
  simpa using h

private theorem classAux_subset_ker (fuel : ℕ) {ker acc frontier : List Vec}
    (hacc : ∀ b ∈ acc, b ∈ ker) (hfr : ∀ b ∈ frontier, b ∈ ker) :
    ∀ b ∈ classAux fuel ker acc frontier, b ∈ ker := by
  induction fuel generalizing acc frontier with
  | zero => intro b hb; exact hacc b hb
  | succ fuel ih =>
    intro b hb
    have hdef : classAux (fuel + 1) ker acc frontier =
        (if (classStep ker acc frontier).isEmpty then acc
         else classAux fuel ker (acc ++ classStep ker acc frontier)
           (classStep ker acc frontier)) := rfl
    rw [hdef] at hb
    by_cases hempty : (classStep ker acc frontier).isEmpty
    · rw [if_pos hempty] at hb; exact hacc b hb
    · rw [if_neg hempty] at hb
      exact ih (fun x hx => by
          rcases List.mem_append.1 hx with hx | hx
          · exact hacc x hx
          · exact classStep_subset ker acc frontier x hx)
        (fun x hx => classStep_subset ker acc frontier x hx) b hb

private theorem foldl_classesOf_subset (K : List Vec) :
    ∀ ker : List Vec, (∀ x ∈ ker, x ∈ K) →
    ∀ p : List (List Vec) × List Vec,
      (∀ l ∈ p.1, ∀ b ∈ l, b ∈ K) → (∀ b ∈ p.2, b ∈ K) →
      ∀ l ∈ (ker.foldl (fun (p : List (List Vec) × List Vec) x =>
        if p.2.contains x then p
        else (p.1 ++ [classAux K.length K [x] [x]],
              p.2 ++ classAux K.length K [x] [x])) p).1, ∀ b ∈ l, b ∈ K := by
  intro ker
  induction ker with
  | nil => intro _ p h1 h2 l hl; exact h1 l hl
  | cons x xs ih =>
    intro hker p h1 h2 l hl
    rw [List.foldl_cons] at hl
    have hxK : x ∈ K := hker x List.mem_cons_self
    have hsingle : ∀ b ∈ [x], b ∈ K := by
      intro b hb; rw [List.mem_singleton] at hb; subst hb; exact hxK
    by_cases hc : p.2.contains x
    · simp only [if_pos hc] at hl
      exact ih (fun y hy => hker y (List.mem_cons_of_mem x hy)) p h1 h2 l hl
    · simp only [if_neg hc] at hl
      refine ih (fun y hy => hker y (List.mem_cons_of_mem x hy)) _ ?_ ?_ l hl
      · intro l' hl'
        rcases List.mem_append.1 hl' with hl' | hl'
        · exact h1 l' hl'
        · rw [List.mem_singleton] at hl'; subst hl'
          exact classAux_subset_ker _ hsingle hsingle
      · intro b hb
        rcases List.mem_append.1 hb with hb | hb
        · exact h2 b hb
        · exact classAux_subset_ker _ hsingle hsingle b hb

private theorem classesOf_subset (ker : List Vec) :
    ∀ l ∈ classesOf ker, ∀ b ∈ l, b ∈ ker := by
  have h := foldl_classesOf_subset ker ker (fun x hx => hx) ([], []) (by simp) (by simp)
  simpa [classesOf] using h

private theorem ncard_classSet_le (l : List Vec) : (classSet l).ncard ≤ l.length := by
  have hinj : Function.Injective (fun γ : Fin Tag.E6.rank → ℤ => List.ofFn γ) :=
    List.ofFn_injective
  have himg : (List.ofFn '' classSet l : Set Vec) ⊆ ((l.toFinset : Finset Vec) : Set Vec) := by
    rintro v ⟨γ, hγ, rfl⟩
    simpa [classSet, List.mem_toFinset] using hγ
  calc (classSet l).ncard
      = (List.ofFn '' classSet l).ncard := (Set.ncard_image_of_injective _ hinj).symm
    _ ≤ ((l.toFinset : Finset Vec) : Set Vec).ncard :=
          Set.ncard_le_ncard himg (Finset.finite_toSet _)
    _ = l.toFinset.card := Set.ncard_coe_finset l.toFinset
    _ ≤ l.length := List.toFinset_card_le l

private theorem finite_classSet (l : List Vec) : (classSet l).Finite := by
  have hrange : {v : Vec | v ∈ l} = Set.range (fun i : Fin l.length => l.get i) := by
    ext v
    constructor
    · intro hv; obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hv; exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩; exact List.get_mem ..
  have hfin : ({v : Vec | v ∈ l}).Finite := by rw [hrange]; exact Set.finite_range _
  exact Set.Finite.preimage List.ofFn_injective.injOn hfin

private def lC0 : List Vec :=
  [[1,0,0,0,0,0],[0,0,1,0,0,0],[-1,0,0,0,0,0],[1,0,1,0,0,0],[0,0,-1,0,0,0],[-1,0,-1,0,0,0]]

private def bvecC0 : Fin 2 → Vec := ![[1,0,0,0,0,0], [0,0,1,0,0,0]]
private def bC0 : Fin 2 → (Fin Tag.E6.rank → ℚ) := fun j => qv (bvecC0 j)
private def coeffZC0 (v : Vec) : Fin 2 → ℤ := ![v.getD 0 0, v.getD 2 0]

private theorem hZC0 : ∀ v ∈ lC0, zro v = ∑ j, (coeffZC0 v j) • zro (bvecC0 j) :=
  forall_mem_of_all_decide (by decide +kernel)

private theorem hgenC0 : ∀ v ∈ lC0, qv v = ∑ j, ((coeffZC0 v j : ℤ) : ℚ) • bC0 j := by
  intro v hv
  have h := congrArg co (hZC0 v hv)
  rwa [co_sum_smul, show co (zro v) = qv v from rfl] at h

private theorem hbSC0 : ∀ i, bC0 i ∈ co '' classSet lC0 := by
  intro i
  fin_cases i
  · show qv [1,0,0,0,0,0] ∈ co '' classSet lC0
    exact mem_co_classSet (by decide) (by decide)
  · show qv [0,0,1,0,0,0] ∈ co '' classSet lC0
    exact mem_co_classSet (by decide) (by decide)

private theorem hbC0 : LinearIndependent ℚ bC0 := by
  refine linearIndependent_of_submatrix bC0 (![0,2] : Fin 2 → Fin Tag.E6.rank) ?_
  decide +kernel

private theorem compRank_C0 : compRank (classSet lC0) = 2 :=
  compRank_classSet_eq lC0 bC0 hbC0 hbSC0
    (fun v hv => mem_span_range_of_sum (hgenC0 v hv))

private def lC1 : List Vec :=
  [[0,1,0,0,0,0],[0,-1,0,0,0,0],[1,1,2,3,2,1],[-1,-1,-2,-3,-2,-1],[1,2,2,3,2,1],[-1,-2,-2,-3,-2,-1]]

private def bvecC1 : Fin 2 → Vec := ![[0,1,0,0,0,0], [1,1,2,3,2,1]]
private def bC1 : Fin 2 → (Fin Tag.E6.rank → ℚ) := fun j => qv (bvecC1 j)
private def coeffZC1 (v : Vec) : Fin 2 → ℤ := ![v.getD 1 0 - v.getD 0 0, v.getD 0 0]

private theorem hZC1 : ∀ v ∈ lC1, zro v = ∑ j, (coeffZC1 v j) • zro (bvecC1 j) :=
  forall_mem_of_all_decide (by decide +kernel)

private theorem hgenC1 : ∀ v ∈ lC1, qv v = ∑ j, ((coeffZC1 v j : ℤ) : ℚ) • bC1 j := by
  intro v hv
  have h := congrArg co (hZC1 v hv)
  rwa [co_sum_smul, show co (zro v) = qv v from rfl] at h

private theorem hbSC1 : ∀ i, bC1 i ∈ co '' classSet lC1 := by
  intro i
  fin_cases i
  · show qv [0,1,0,0,0,0] ∈ co '' classSet lC1
    exact mem_co_classSet (by decide) (by decide)
  · show qv [1,1,2,3,2,1] ∈ co '' classSet lC1
    exact mem_co_classSet (by decide) (by decide)

private theorem hbC1 : LinearIndependent ℚ bC1 := by
  refine linearIndependent_of_submatrix bC1 (![0,1] : Fin 2 → Fin Tag.E6.rank) ?_
  decide +kernel

private theorem compRank_C1 : compRank (classSet lC1) = 2 :=
  compRank_classSet_eq lC1 bC1 hbC1 hbSC1
    (fun v hv => mem_span_range_of_sum (hgenC1 v hv))

private def lC2 : List Vec :=
  [[0,0,0,0,1,0],[0,0,0,0,0,1],[0,0,0,0,-1,0],[0,0,0,0,1,1],[0,0,0,0,0,-1],[0,0,0,0,-1,-1]]

private def bvecC2 : Fin 2 → Vec := ![[0,0,0,0,1,0], [0,0,0,0,0,1]]
private def bC2 : Fin 2 → (Fin Tag.E6.rank → ℚ) := fun j => qv (bvecC2 j)
private def coeffZC2 (v : Vec) : Fin 2 → ℤ := ![v.getD 4 0, v.getD 5 0]

private theorem hZC2 : ∀ v ∈ lC2, zro v = ∑ j, (coeffZC2 v j) • zro (bvecC2 j) :=
  forall_mem_of_all_decide (by decide +kernel)

private theorem hgenC2 : ∀ v ∈ lC2, qv v = ∑ j, ((coeffZC2 v j : ℤ) : ℚ) • bC2 j := by
  intro v hv
  have h := congrArg co (hZC2 v hv)
  rwa [co_sum_smul, show co (zro v) = qv v from rfl] at h

private theorem hbSC2 : ∀ i, bC2 i ∈ co '' classSet lC2 := by
  intro i
  fin_cases i
  · show qv [0,0,0,0,1,0] ∈ co '' classSet lC2
    exact mem_co_classSet (by decide) (by decide)
  · show qv [0,0,0,0,0,1] ∈ co '' classSet lC2
    exact mem_co_classSet (by decide) (by decide)

private theorem hbC2 : LinearIndependent ℚ bC2 := by
  refine linearIndependent_of_submatrix bC2 (![4,5] : Fin 2 → Fin Tag.E6.rank) ?_
  decide +kernel

private theorem compRank_C2 : compRank (classSet lC2) = 2 :=
  compRank_classSet_eq lC2 bC2 hbC2 hbSC2
    (fun v hv => mem_span_range_of_sum (hgenC2 v hv))

private def lD4 : List Vec :=
  [[1,0,0,0,0,0],[-1,0,0,0,0,0],[0,0,1,1,1,0],[1,0,1,1,1,0],[0,1,1,1,1,0],[0,0,-1,-1,-1,0],
   [0,0,1,1,1,1],[-1,0,-1,-1,-1,0],[1,1,1,1,1,0],[1,0,1,1,1,1],[0,-1,-1,-1,-1,0],[0,1,1,1,1,1],
   [0,0,-1,-1,-1,-1],[-1,-1,-1,-1,-1,0],[-1,0,-1,-1,-1,-1],[1,1,1,1,1,1],[0,-1,-1,-1,-1,-1],
   [-1,-1,-1,-1,-1,-1],[0,1,0,0,0,0],[0,0,0,0,0,1],[0,-1,0,0,0,0],[0,0,0,0,0,-1],[1,1,2,2,2,1],
   [-1,-1,-2,-2,-2,-1]]

private def bvecD4 : Fin 4 → Vec :=
  ![[1,0,0,0,0,0], [0,1,0,0,0,0], [0,0,1,1,1,0], [0,0,0,0,0,1]]
private def bD4 : Fin 4 → (Fin Tag.E6.rank → ℚ) := fun j => qv (bvecD4 j)
private def coeffZD4 (v : Vec) : Fin 4 → ℤ :=
  ![v.getD 0 0, v.getD 1 0, v.getD 2 0, v.getD 5 0]

private theorem hZD4 : ∀ v ∈ lD4, zro v = ∑ j, (coeffZD4 v j) • zro (bvecD4 j) :=
  forall_mem_of_all_decide (by decide +kernel)

private theorem hgenD4 : ∀ v ∈ lD4, qv v = ∑ j, ((coeffZD4 v j : ℤ) : ℚ) • bD4 j := by
  intro v hv
  have h := congrArg co (hZD4 v hv)
  rwa [co_sum_smul, show co (zro v) = qv v from rfl] at h

private theorem hbSD4 : ∀ i, bD4 i ∈ co '' classSet lD4 := by
  intro i
  fin_cases i
  · show qv [1,0,0,0,0,0] ∈ co '' classSet lD4
    exact mem_co_classSet (by decide) (by decide)
  · show qv [0,1,0,0,0,0] ∈ co '' classSet lD4
    exact mem_co_classSet (by decide) (by decide)
  · show qv [0,0,1,1,1,0] ∈ co '' classSet lD4
    exact mem_co_classSet (by decide) (by decide)
  · show qv [0,0,0,0,0,1] ∈ co '' classSet lD4
    exact mem_co_classSet (by decide) (by decide)

private theorem hbD4 : LinearIndependent ℚ bD4 := by
  refine linearIndependent_of_submatrix bD4 (![0,1,2,5] : Fin 4 → Fin Tag.E6.rank) ?_
  decide +kernel

private theorem compRank_D4 : compRank (classSet lD4) = 4 :=
  compRank_classSet_eq lD4 bD4 hbD4 hbSD4
    (fun v hv => mem_span_range_of_sum (hgenD4 v hv))

private def lA5 : List Vec :=
  [[1,0,0,0,0,0],[0,0,1,0,0,0],[-1,0,0,0,0,0],[1,0,1,0,0,0],[0,0,-1,0,0,0],[0,0,1,1,0,0],
   [-1,0,-1,0,0,0],[1,0,1,1,0,0],[0,1,1,1,0,0],[0,0,-1,-1,0,0],[-1,0,-1,-1,0,0],[1,1,1,1,0,0],
   [0,-1,-1,-1,0,0],[-1,-1,-1,-1,0,0],[0,1,1,2,2,1],[1,1,1,2,2,1],[0,-1,-1,-2,-2,-1],
   [-1,-1,-1,-2,-2,-1],[0,0,0,1,0,0],[0,1,0,1,0,0],[0,0,0,-1,0,0],[0,-1,0,-1,0,0],
   [1,1,2,2,2,1],[-1,-1,-2,-2,-2,-1],[0,1,0,0,0,0],[0,-1,0,0,0,0],[1,1,2,3,2,1],
   [-1,-1,-2,-3,-2,-1],[1,2,2,3,2,1],[-1,-2,-2,-3,-2,-1]]

private def bvecA5 : Fin 5 → Vec :=
  ![[1,0,0,0,0,0], [0,1,0,0,0,0], [0,0,1,0,0,0], [0,0,0,1,0,0], [1,1,1,2,2,1]]
private def bA5 : Fin 5 → (Fin Tag.E6.rank → ℚ) := fun j => qv (bvecA5 j)
private def coeffZA5 (v : Vec) : Fin 5 → ℤ :=
  ![v.getD 0 0 - v.getD 5 0, v.getD 1 0 - v.getD 5 0, v.getD 2 0 - v.getD 5 0,
    v.getD 3 0 - 2 * v.getD 5 0, v.getD 5 0]

private theorem hZA5 : ∀ v ∈ lA5, zro v = ∑ j, (coeffZA5 v j) • zro (bvecA5 j) :=
  forall_mem_of_all_decide (by decide +kernel)

private theorem hgenA5 : ∀ v ∈ lA5, qv v = ∑ j, ((coeffZA5 v j : ℤ) : ℚ) • bA5 j := by
  intro v hv
  have h := congrArg co (hZA5 v hv)
  rwa [co_sum_smul, show co (zro v) = qv v from rfl] at h

private theorem hbSA5 : ∀ i, bA5 i ∈ co '' classSet lA5 := by
  intro i
  fin_cases i
  · show qv [1,0,0,0,0,0] ∈ co '' classSet lA5
    exact mem_co_classSet (by decide) (by decide)
  · show qv [0,1,0,0,0,0] ∈ co '' classSet lA5
    exact mem_co_classSet (by decide) (by decide)
  · show qv [0,0,1,0,0,0] ∈ co '' classSet lA5
    exact mem_co_classSet (by decide) (by decide)
  · show qv [0,0,0,1,0,0] ∈ co '' classSet lA5
    exact mem_co_classSet (by decide) (by decide)
  · show qv [1,1,1,2,2,1] ∈ co '' classSet lA5
    exact mem_co_classSet (by decide) (by decide)

private theorem hbA5 : LinearIndependent ℚ bA5 := by
  refine linearIndependent_of_submatrix bA5 (![0,1,2,3,4] : Fin 5 → Fin Tag.E6.rank) ?_
  decide +kernel

private theorem compRank_A5 : compRank (classSet lA5) = 5 :=
  compRank_classSet_eq lA5 bA5 hbA5 hbSA5
    (fun v hv => mem_span_range_of_sum (hgenA5 v hv))

private def lD5 : List Vec := kerRoots (reps.getD 4 [])

private def bvecD5 : Fin 5 → Vec :=
  ![[1,0,0,0,0,0], [0,1,0,0,0,0], [0,0,1,0,0,0], [0,0,0,1,0,0], [0,0,0,0,1,0]]
private def bD5 : Fin 5 → (Fin Tag.E6.rank → ℚ) := fun j => qv (bvecD5 j)
private def coeffZD5 (v : Vec) : Fin 5 → ℤ :=
  ![v.getD 0 0, v.getD 1 0, v.getD 2 0, v.getD 3 0, v.getD 4 0]

private theorem hZD5 : ∀ v ∈ lD5, zro v = ∑ j, (coeffZD5 v j) • zro (bvecD5 j) :=
  forall_mem_of_all_decide (by decide +kernel)

private theorem hgenD5 : ∀ v ∈ lD5, qv v = ∑ j, ((coeffZD5 v j : ℤ) : ℚ) • bD5 j := by
  intro v hv
  have h := congrArg co (hZD5 v hv)
  rwa [co_sum_smul, show co (zro v) = qv v from rfl] at h

private theorem hbSD5 : ∀ i, bD5 i ∈ co '' classSet lD5 := by
  intro i
  fin_cases i
  · show qv [1,0,0,0,0,0] ∈ co '' classSet lD5
    exact mem_co_classSet (by decide +kernel) (by decide +kernel)
  · show qv [0,1,0,0,0,0] ∈ co '' classSet lD5
    exact mem_co_classSet (by decide +kernel) (by decide +kernel)
  · show qv [0,0,1,0,0,0] ∈ co '' classSet lD5
    exact mem_co_classSet (by decide +kernel) (by decide +kernel)
  · show qv [0,0,0,1,0,0] ∈ co '' classSet lD5
    exact mem_co_classSet (by decide +kernel) (by decide +kernel)
  · show qv [0,0,0,0,1,0] ∈ co '' classSet lD5
    exact mem_co_classSet (by decide +kernel) (by decide +kernel)

private theorem hbD5 : LinearIndependent ℚ bD5 := by
  refine linearIndependent_of_submatrix bD5 (![0,1,2,3,4] : Fin 5 → Fin Tag.E6.rank) ?_
  decide +kernel

private theorem compRank_D5 : compRank (classSet lD5) = 5 :=
  compRank_classSet_eq lD5 bD5 hbD5 hbSD5
    (fun v hv => mem_span_range_of_sum (hgenD5 v hv))

private theorem classes_four_insert : classes (reps.getD 0 []) = [lC0, lC1, lC2] := by
  decide +kernel

private theorem classes_four_two : classes (reps.getD 2 []) = [lD4] := by decide +kernel

private theorem classes_four_three : classes (reps.getD 3 []) = [lA5] := by decide +kernel

private theorem kerRoots_four_length : (kerRoots (reps.getD 4 [])).length = 40 := by decide +kernel

private theorem classSet_eq_lD5 {l : List Vec} (hl : l ∈ classes (reps.getD 4 [])) :
    classSet l = classSet lD5 := by
  have hmap : (classes (reps.getD 4 [])).map List.length = [40] := by
    have h := congrArg (fun (L : List (List ℕ)) => L.getD 4 []) classes_lengths
    rw [show (List.range 5 : List ℕ) = [0,1,2,3,4] from rfl] at h
    simp only [List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ] at h
    exact h
  have hlen : l.length = 40 := by
    have hmem : l.length ∈ (classes (reps.getD 4 [])).map List.length :=
      List.mem_map.2 ⟨l, hl, rfl⟩
    rw [hmap] at hmem
    simpa using hmem
  have hsub : ∀ x, x ∈ l → x ∈ lD5 := fun x hx =>
    classesOf_subset (kerRoots (reps.getD 4 [])) l hl x hx
  have hset : ∀ γ, γ ∈ classSet l → γ ∈ classSet lD5 := fun γ hγ => hsub (List.ofFn γ) hγ
  have hncard : (classSet l).ncard = 40 := by rw [classSet_ncard 4 l hl, hlen]
  have hle : (classSet lD5).ncard ≤ (classSet l).ncard := by
    rw [hncard]
    calc (classSet lD5).ncard ≤ lD5.length := ncard_classSet_le lD5
      _ = 40 := kerRoots_four_length
  exact Set.eq_of_subset_of_ncard_le hset hle (finite_classSet lD5)

theorem classes_compRank (k : Fin 5) (l : List Vec) (hl : l ∈ classes (reps.getD k [])) :
    (k = 0 → compRank (classSet l) = 2) ∧ (k = 2 → compRank (classSet l) = 4) ∧
      (k = 3 → compRank (classSet l) = 5) ∧ (k = 4 → compRank (classSet l) = 5) := by
  have h0 : classes (reps.getD 0 []) = [lC0, lC1, lC2] := classes_four_insert
  have h2 : classes (reps.getD 2 []) = [lD4] := classes_four_two
  have h3 : classes (reps.getD 3 []) = [lA5] := classes_four_three
  fin_cases k
  · rw [h0] at hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact ⟨fun _ => compRank_C0, fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => compRank_C1, fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => compRank_C2, fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide),
      fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  · rw [h2] at hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl
    exact ⟨fun h => absurd h (by decide), fun _ => compRank_D4, fun h => absurd h (by decide),
      fun h => absurd h (by decide)⟩
  · rw [h3] at hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl
    exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ => compRank_A5,
      fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide),
      fun h => absurd h (by decide), fun _ => by rw [classSet_eq_lD5 hl]; exact compRank_D5⟩

end CFSG.StandardType.TablePThreeKG

end
