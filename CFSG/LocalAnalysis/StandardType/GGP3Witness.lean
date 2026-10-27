module

public import CFSG.LocalAnalysis.StandardType.GGLatticeWitness

public section

namespace CFSG.StandardType

@[expose] def GGInvTest3 {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (X : Matrix (Option Λ) (Option Λ) ℤ) : Prop :=
  ∃ (ψ : List (Option Λ)) (k : Option Λ) (ρ : Option Λ → ℤ), ρ ∈ ggLCoroots X ∧
    ((ggSWordR X ψ (Pi.single k 1) none : ℤ) : ZMod 3) = 0 ∧
    ∀ v ∈ ggLCoroots X,
      (fun i => (ρ i : ZMod 3) -
          ((∑ i', ggSWordR X ψ (Pi.single k 1) i' * ∑ j, X i' j * ρ j : ℤ) : ZMod 3) *
            (ggSWord X ψ (Pi.single k 1) i : ZMod 3)) ≠ fun i => (v i : ZMod 3)

private theorem p3w_comp_symm_map {Λ Λ' : Type} (e : Λ ≃ Λ') (b : Option Λ) :
    (Equiv.optionCongr e).symm (Option.map e b) = b := by
  rw [← Equiv.optionCongr_apply]
  exact Equiv.symm_apply_apply (Equiv.optionCongr e) b

private theorem p3w_comp_eq_iff {Λ Λ' : Type} (e : Λ ≃ Λ') (x : Option Λ') (k : Option Λ) :
    x = Option.map e k ↔ (Equiv.optionCongr e).symm x = k := by
  constructor
  · intro h
    rw [h]
    exact p3w_comp_symm_map e k
  · intro h
    have h2 : Option.map e ((Equiv.optionCongr e).symm x) = Option.map e k := by rw [h]
    rwa [← Equiv.optionCongr_apply, Equiv.apply_symm_apply] at h2

private theorem p3w_single_comp' {Λ Λ' : Type} [DecidableEq Λ] [DecidableEq Λ']
    (e : Λ ≃ Λ') (k : Option Λ) :
    (Pi.single (Option.map e k) (1 : ℤ) : Option Λ' → ℤ) =
      (Pi.single k (1 : ℤ) : Option Λ → ℤ) ∘ (Equiv.optionCongr e).symm := by
  funext x
  rw [Function.comp_apply, Pi.single_apply, Pi.single_apply]
  by_cases h : x = Option.map e k
  · rw [if_pos h, if_pos ((p3w_comp_eq_iff e x k).mp h)]
  · rw [if_neg h, if_neg (fun hk => h ((p3w_comp_eq_iff e x k).mpr hk))]

private theorem p3w_sRefl_comp {Λ Λ' : Type} [Fintype Λ] [DecidableEq Λ] [Fintype Λ']
    [DecidableEq Λ'] (e : Λ ≃ Λ') {X : Matrix (Option Λ) (Option Λ) ℤ}
    {X' : Matrix (Option Λ') (Option Λ') ℤ}
    (hX : ∀ i j, X' (Option.map e i) (Option.map e j) = X i j)
    (j : Option Λ) (v : Option Λ → ℤ) :
    ggSRefl X' (Option.map e j) (v ∘ (Equiv.optionCongr e).symm) =
      (ggSRefl X j v) ∘ (Equiv.optionCongr e).symm := by
  funext i
  have hrow : (∑ a : Option Λ',
        X' (Option.map e j) a * v ((Equiv.optionCongr e).symm a))
      = ∑ b : Option Λ, X j b * v b := by
    rw [← Equiv.sum_comp (Equiv.optionCongr e)
      (fun a : Option Λ' => X' (Option.map e j) a * v ((Equiv.optionCongr e).symm a))]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Equiv.optionCongr_apply, hX j b, p3w_comp_symm_map e b]
  have hsingle : (Pi.single (Option.map e j) (1 : ℤ) : Option Λ' → ℤ) i
      = (Pi.single (M := fun _ => ℤ) j (1 : ℤ) : Option Λ → ℤ)
          ((Equiv.optionCongr e).symm i) := by
    have h := congrFun (p3w_single_comp' e j) i
    simpa [Function.comp_def] using h
  simp only [ggSRefl, Pi.sub_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul]
  rw [hrow, hsingle]

private theorem p3w_sReflR_comp {Λ Λ' : Type} [Fintype Λ] [DecidableEq Λ] [Fintype Λ']
    [DecidableEq Λ'] (e : Λ ≃ Λ') {X : Matrix (Option Λ) (Option Λ) ℤ}
    {X' : Matrix (Option Λ') (Option Λ') ℤ}
    (hX : ∀ i j, X' (Option.map e i) (Option.map e j) = X i j)
    (j : Option Λ) (c : Option Λ → ℤ) :
    ggSReflR X' (Option.map e j) (c ∘ (Equiv.optionCongr e).symm) =
      (ggSReflR X j c) ∘ (Equiv.optionCongr e).symm := by
  funext i
  have hcol : (∑ a : Option Λ',
        c ((Equiv.optionCongr e).symm a) * X' a (Option.map e j))
      = ∑ b : Option Λ, c b * X b j := by
    rw [← Equiv.sum_comp (Equiv.optionCongr e)
      (fun a : Option Λ' => c ((Equiv.optionCongr e).symm a) * X' a (Option.map e j))]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Equiv.symm_apply_apply, Equiv.optionCongr_apply, hX b j]
  have hsingle : (Pi.single (Option.map e j) (1 : ℤ) : Option Λ' → ℤ) i
      = (Pi.single (M := fun _ => ℤ) j (1 : ℤ) : Option Λ → ℤ)
          ((Equiv.optionCongr e).symm i) := by
    have h := congrFun (p3w_single_comp' e j) i
    simpa [Function.comp_def] using h
  simp only [ggSReflR, Pi.sub_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul]
  rw [hcol, hsingle]

private theorem p3w_sWord_comp {Λ Λ' : Type} [Fintype Λ] [DecidableEq Λ] [Fintype Λ']
    [DecidableEq Λ'] (e : Λ ≃ Λ') {X : Matrix (Option Λ) (Option Λ) ℤ}
    {X' : Matrix (Option Λ') (Option Λ') ℤ}
    (hX : ∀ i j, X' (Option.map e i) (Option.map e j) = X i j)
    (ψ : List (Option Λ)) (v : Option Λ → ℤ) :
    ggSWord X' (ψ.map (Option.map e)) (v ∘ (Equiv.optionCongr e).symm) =
      (ggSWord X ψ v) ∘ (Equiv.optionCongr e).symm := by
  induction ψ with
  | nil => rfl
  | cons j ψ ih =>
      rw [List.map_cons, show ggSWord X' (Option.map e j :: ψ.map (Option.map e))
            (v ∘ (Equiv.optionCongr e).symm)
          = ggSRefl X' (Option.map e j)
              (ggSWord X' (ψ.map (Option.map e)) (v ∘ (Equiv.optionCongr e).symm)) from rfl,
        ih, p3w_sRefl_comp e hX j (ggSWord X ψ v)]
      rfl

private theorem p3w_sWordR_comp {Λ Λ' : Type} [Fintype Λ] [DecidableEq Λ] [Fintype Λ']
    [DecidableEq Λ'] (e : Λ ≃ Λ') {X : Matrix (Option Λ) (Option Λ) ℤ}
    {X' : Matrix (Option Λ') (Option Λ') ℤ}
    (hX : ∀ i j, X' (Option.map e i) (Option.map e j) = X i j)
    (ψ : List (Option Λ)) (c : Option Λ → ℤ) :
    ggSWordR X' (ψ.map (Option.map e)) (c ∘ (Equiv.optionCongr e).symm) =
      (ggSWordR X ψ c) ∘ (Equiv.optionCongr e).symm := by
  induction ψ with
  | nil => rfl
  | cons j ψ ih =>
      rw [List.map_cons, show ggSWordR X' (Option.map e j :: ψ.map (Option.map e))
            (c ∘ (Equiv.optionCongr e).symm)
          = ggSReflR X' (Option.map e j)
              (ggSWordR X' (ψ.map (Option.map e)) (c ∘ (Equiv.optionCongr e).symm)) from rfl,
        ih, p3w_sReflR_comp e hX j (ggSWordR X ψ c)]
      rfl

private theorem p3w_coroots_mem {Λ Λ' : Type} [Fintype Λ] [DecidableEq Λ] [Fintype Λ']
    [DecidableEq Λ'] (e : Λ ≃ Λ') {X : Matrix (Option Λ) (Option Λ) ℤ}
    {X' : Matrix (Option Λ') (Option Λ') ℤ}
    (hX : ∀ i j, X' (Option.map e i) (Option.map e j) = X i j)
    {v' : Option Λ' → ℤ} (hv : v' ∈ ggLCoroots X') :
    v' ∘ (Equiv.optionCongr e) ∈ ggLCoroots X := by
  obtain ⟨ψ, i, rfl⟩ := hv
  refine ⟨ψ.map e.symm, e.symm i, ?_⟩
  have hmap : ψ.map some = ((ψ.map e.symm).map some).map (Option.map e) := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro x _
    simp
  calc (ggSWord X' (ψ.map some) (Pi.single (some i) (1 : ℤ))) ∘ (Equiv.optionCongr e)
      = (ggSWord X' (((ψ.map e.symm).map some).map (Option.map e))
          (Pi.single (Option.map e (some (e.symm i))) (1 : ℤ)))
          ∘ (Equiv.optionCongr e) := by rw [hmap]; congr 2; simp
    _ = ((ggSWord X ((ψ.map e.symm).map some) (Pi.single (some (e.symm i)) (1 : ℤ)))
          ∘ (Equiv.optionCongr e).symm) ∘ (Equiv.optionCongr e) := by
          rw [p3w_single_comp' e (some (e.symm i)),
            p3w_sWord_comp e hX ((ψ.map e.symm).map some) (Pi.single (some (e.symm i)) (1 : ℤ))]
    _ = ggSWord X ((ψ.map e.symm).map some) (Pi.single (some (e.symm i)) (1 : ℤ)) := by
          rw [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]


private theorem p3w_coroots_mem_map {Λ Λ' : Type} [Fintype Λ] [DecidableEq Λ] [Fintype Λ']
    [DecidableEq Λ'] (e : Λ ≃ Λ') {X : Matrix (Option Λ) (Option Λ) ℤ}
    {X' : Matrix (Option Λ') (Option Λ') ℤ}
    (hX : ∀ i j, X' (Option.map e i) (Option.map e j) = X i j)
    {v : Option Λ → ℤ} (hv : v ∈ ggLCoroots X) :
    v ∘ (Equiv.optionCongr e).symm ∈ ggLCoroots X' := by
  obtain ⟨ψ, i, rfl⟩ := hv
  refine ⟨ψ.map e, e i, ?_⟩
  have hmap : (ψ.map e).map some = (ψ.map some).map (Option.map e) := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro x _
    simp
  have hsingle : (Pi.single (some (e i)) (1 : ℤ) : Option Λ' → ℤ)
      = (Pi.single (some i) (1 : ℤ) : Option Λ → ℤ) ∘ (Equiv.optionCongr e).symm := by
    simpa only [Option.map_some] using p3w_single_comp' e (some i)
  calc (ggSWord X (ψ.map some) (Pi.single (some i) (1 : ℤ)))
        ∘ (Equiv.optionCongr e).symm
      = ggSWord X' ((ψ.map some).map (Option.map e))
          ((Pi.single (some i) (1 : ℤ)) ∘ (Equiv.optionCongr e).symm) := by
          rw [p3w_sWord_comp e hX (ψ.map some) (Pi.single (some i) (1 : ℤ))]
    _ = ggSWord X' ((ψ.map e).map some) (Pi.single (some (e i)) (1 : ℤ)) := by
          rw [← hmap, ← hsingle]

private theorem p3w_pair_comp {Λ Λ' : Type} [Fintype Λ] [Fintype Λ']
    (e : Λ ≃ Λ') {X : Matrix (Option Λ) (Option Λ) ℤ}
    {X' : Matrix (Option Λ') (Option Λ') ℤ}
    (hX : ∀ i j, X' (Option.map e i) (Option.map e j) = X i j)
    (c : Option Λ → ℤ) (ρ : Option Λ → ℤ) :
    (∑ i' : Option Λ', c ((Equiv.optionCongr e).symm i') *
        ∑ j' : Option Λ', X' i' j' * ρ ((Equiv.optionCongr e).symm j'))
      = ∑ i : Option Λ, c i * ∑ j : Option Λ, X i j * ρ j := by
  rw [← Equiv.sum_comp (Equiv.optionCongr e)
    (fun i' : Option Λ' => c ((Equiv.optionCongr e).symm i') *
      ∑ j' : Option Λ', X' i' j' * ρ ((Equiv.optionCongr e).symm j'))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Equiv.symm_apply_apply]
  congr 1
  rw [← Equiv.sum_comp (Equiv.optionCongr e)
    (fun j' : Option Λ' =>
      X' (Equiv.optionCongr e i) j' * ρ ((Equiv.optionCongr e).symm j'))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Equiv.symm_apply_apply, Equiv.optionCongr_apply, Equiv.optionCongr_apply, hX i j]

theorem ggInvTest3_of_equiv {Λ Λ' : Type} [Fintype Λ] [DecidableEq Λ] [Fintype Λ']
    [DecidableEq Λ'] (e : Λ ≃ Λ') {X : Matrix (Option Λ) (Option Λ) ℤ}
    {X' : Matrix (Option Λ') (Option Λ') ℤ}
    (hX : ∀ i j, X' (Option.map e i) (Option.map e j) = X i j) (h : GGInvTest3 X) :
    GGInvTest3 X' := by
  obtain ⟨ψ, k, ρ, hρ, ha, hnp⟩ := h
  refine ⟨ψ.map (Option.map e), Option.map e k, ρ ∘ (Equiv.optionCongr e).symm,
    p3w_coroots_mem_map e hX hρ, ?_, ?_⟩
  · have hword := p3w_sWordR_comp e hX ψ (Pi.single k (1 : ℤ))
    rw [← p3w_single_comp' e k] at hword
    have hnone := congrFun hword none
    simp only [Function.comp_apply] at hnone
    have hφnone : (Equiv.optionCongr e).symm none = none := rfl
    rw [hφnone] at hnone
    rw [hnone, ha]
  · intro v' hv' hcon
    refine hnp (v' ∘ (Equiv.optionCongr e)) (p3w_coroots_mem e hX hv') ?_
    have hword := p3w_sWord_comp e hX ψ (Pi.single k (1 : ℤ))
    rw [← p3w_single_comp' e k] at hword
    have hwordR := p3w_sWordR_comp e hX ψ (Pi.single k (1 : ℤ))
    rw [← p3w_single_comp' e k] at hwordR
    have hp := p3w_pair_comp e hX (ggSWordR X ψ (Pi.single k (1 : ℤ))) ρ
    funext i
    have h1 := congrFun hcon ((Equiv.optionCongr e) i)
    simp only [Function.comp_apply]
    rw [← h1]
    have hρi : ((ρ ∘ (Equiv.optionCongr e).symm) ((Equiv.optionCongr e) i) : ZMod 3)
        = (ρ i : ZMod 3) := by
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
    have hwi : (ggSWord X' (ψ.map (Option.map e)) (Pi.single (Option.map e k) (1 : ℤ))
          ((Equiv.optionCongr e) i) : ZMod 3)
        = (ggSWord X ψ (Pi.single k (1 : ℤ)) i : ZMod 3) := by
      rw [hword]
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
    have hE : (∑ i' : Option Λ', ggSWordR X' (ψ.map (Option.map e))
            (Pi.single (Option.map e k) (1 : ℤ)) i' *
            ∑ j : Option Λ', X' i' j * (ρ ∘ (Equiv.optionCongr e).symm) j)
        = ∑ i' : Option Λ, ggSWordR X ψ (Pi.single k (1 : ℤ)) i' *
            ∑ j : Option Λ, X i' j * ρ j := by
      rw [hwordR]
      simp only [Function.comp_apply]
      exact hp
    rw [hρi, hwi, hE]

@[expose] def ggLWtest3 (XL : List (List ℤ)) (n : ℕ) (R : List (List ℤ)) (ψ : List ℕ) (k i₀ : ℕ) :
    Bool :=
  let N := n + 1
  let w := ggLWword XL ψ (ggLWunit N k)
  let c := ggLWwordR XL ψ (ggLWunit N k)
  let ρ := ggLWunit N i₀
  let e := ggLWdot c (XL.map fun row => ggLWdot row ρ)
  let img := List.zipWith (fun x y => x - e * y) ρ w
  decide (ψ.all (· ≤ n) = true) && decide (k ≤ n) && decide (i₀ < n) &&
    decide (c.getD n 0 % 3 = 0) &&
    R.all fun v => !((List.zipWith (fun a b => decide ((a - b) % 3 = 0)) img (v ++ [0])).all id)

private def p3w_vecOf {n : ℕ} (l : List ℤ) : Option (Fin n) → ℤ :=
  fun o => l.getD (match o with | none => n | some i => i.1) 0

private theorem p3w_node {n : ℕ} (l : List ℤ) {i : ℕ} (hi : i ≤ n) :
    p3w_vecOf l (ggLWnode n i) = l.getD i 0 := by
  by_cases h : i < n
  · simp only [p3w_vecOf, ggLWnode, dif_pos h]
  · have hin : i = n := by omega
    rw [hin]
    simp only [p3w_vecOf, ggLWnode, dif_neg (Nat.lt_irrefl n)]

private theorem p3w_node_fin {n : ℕ} (i : Fin n) : ggLWnode n i.1 = some i := by
  simp only [ggLWnode]
  rw [dif_pos i.2]

private theorem p3w_node_some {n : ℕ} (l : List ℤ) (i : Fin n) :
    p3w_vecOf l (some i) = l.getD i.1 0 := by
  rw [show some i = ggLWnode n i.1 from (p3w_node_fin i).symm, p3w_node l (le_of_lt i.2)]

private theorem p3w_node_none {n : ℕ} (l : List ℤ) :
    p3w_vecOf l (none : Option (Fin n)) = l.getD n 0 := rfl

private theorem p3w_sum_option_range {n : ℕ} {M : Type} [AddCommMonoid M]
    (f : Option (Fin n) → M) :
    ∑ o : Option (Fin n), f o = ∑ i ∈ Finset.range (n + 1), f (ggLWnode n i) := by
  rw [Fintype.sum_option, Finset.sum_range_succ]
  rw [show ggLWnode n n = none from dif_neg (Nat.lt_irrefl n)]
  have hfin : (∑ i : Fin n, f (some i)) = ∑ i : Fin n, f (ggLWnode n i.1) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [show some i = ggLWnode n i.1 from (p3w_node_fin i).symm]
  rw [hfin, Fin.sum_univ_eq_sum_range (fun i => f (ggLWnode n i)) n]
  exact add_comm _ _

private theorem p3w_row {n : ℕ} (X : Matrix (Option (Fin n)) (Option (Fin n)) ℤ) {j : ℕ}
    (hj : j ≤ n) :
    (ggLWmat X).getD j [] =
      (List.range (n + 1)).map (fun b => X (ggLWnode n j) (ggLWnode n b)) := by
  have hlt : j < (ggLWmat X).length := by
    simp only [ggLWmat, List.length_map, List.length_range]; omega
  rw [List.getD_eq_getElem _ _ hlt]
  simp only [ggLWmat, List.getElem_map, List.getElem_range]

private theorem p3w_dot_map {N : ℕ} (fb : ℕ → ℤ) (l : List ℤ) (hl : l.length = N) :
    ggLWdot ((List.range N).map fb) l
      = ∑ b ∈ Finset.range N, fb b * l.getD b 0 := by
  rw [ggLWdot, List.zipWith_map_left]
  have hlist : List.zipWith (fun a b => fb a * b) (List.range N) l
      = List.ofFn (fun i : Fin N => fb i.1 * l.getD i.1 0) := by
    apply List.ext_getElem
    · rw [List.length_zipWith, List.length_range, hl, min_self, List.length_ofFn]
    · intro i h1 h2
      have hi : i < l.length :=
        lt_of_lt_of_le h1 (by rw [List.length_zipWith]; exact min_le_right _ _)
      rw [List.getElem_zipWith, List.getElem_range, List.getElem_ofFn]
      rw [← List.getD_eq_getElem l 0 hi]
  rw [hlist, List.sum_ofFn, Fin.sum_univ_eq_sum_range (fun i => fb i * l.getD i 0) N]

private theorem p3w_sRefl_bridge {n : ℕ} (X : Matrix (Option (Fin n)) (Option (Fin n)) ℤ)
    {j : ℕ} (hj : j ≤ n) (l : List ℤ) (hl : l.length = n + 1) :
    ggSRefl X (ggLWnode n j) (p3w_vecOf l) = p3w_vecOf (ggLWrefl (ggLWmat X) j l) := by
  have hsum : (∑ i : Option (Fin n), X (ggLWnode n j) i * p3w_vecOf l i)
      = ∑ b ∈ Finset.range (n + 1), X (ggLWnode n j) (ggLWnode n b) * l.getD b 0 := by
    rw [p3w_sum_option_range]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [p3w_node l (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))]
  have hdot : ggLWdot ((ggLWmat X).getD j []) l
      = ∑ b ∈ Finset.range (n + 1), X (ggLWnode n j) (ggLWnode n b) * l.getD b 0 := by
    rw [p3w_row X hj, p3w_dot_map _ l hl]
  have hlen : (ggLWrefl (ggLWmat X) j l).length = n + 1 := by
    simp only [ggLWrefl, List.length_mapIdx, hl]
  funext o
  rw [show ggSRefl X (ggLWnode n j) (p3w_vecOf l)
      = p3w_vecOf l - (∑ i : Option (Fin n), X (ggLWnode n j) i * p3w_vecOf l i) •
          Pi.single (ggLWnode n j) 1 from rfl]
  rw [hsum, ← hdot]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rcases o with _ | i
  · rw [p3w_node_none,
      show p3w_vecOf (ggLWrefl (ggLWmat X) j l) none
        = (ggLWrefl (ggLWmat X) j l).getD n 0 from rfl]
    rw [List.getD_eq_getElem (ggLWrefl (ggLWmat X) j l) 0 (by rw [hlen]; omega)]
    simp only [ggLWrefl, List.getElem_mapIdx]
    rw [← List.getD_eq_getElem l 0 (by omega)]
    by_cases hjn : j = n
    · rw [hjn, show ggLWnode n n = none from dif_neg (Nat.lt_irrefl n)]
      rw [Pi.single_apply, if_pos rfl, if_pos rfl]
      ring
    · have hjs : j < n := lt_of_le_of_ne hj hjn
      rw [show ggLWnode n j = some ⟨j, hjs⟩ from dif_pos hjs]
      rw [Pi.single_apply, if_neg (by simp), mul_zero, sub_zero,
        if_neg (by omega : ¬ n = j)]
  · rw [p3w_node_some,
      show p3w_vecOf (ggLWrefl (ggLWmat X) j l) (some i)
        = (ggLWrefl (ggLWmat X) j l).getD i.1 0 from rfl]
    rw [List.getD_eq_getElem (ggLWrefl (ggLWmat X) j l) 0 (by rw [hlen]; omega)]
    simp only [ggLWrefl, List.getElem_mapIdx]
    rw [← List.getD_eq_getElem l 0 (by omega)]
    by_cases hjn : j = n
    · rw [hjn, show ggLWnode n n = none from dif_neg (Nat.lt_irrefl n)]
      rw [Pi.single_apply, if_neg (by simp), if_neg (by omega : ¬ i.1 = n)]
      ring
    · have hjs : j < n := lt_of_le_of_ne hj hjn
      rw [show ggLWnode n j = some ⟨j, hjs⟩ from dif_pos hjs]
      rw [Pi.single_apply]
      by_cases hij : i.1 = j
      · rw [if_pos (by simp [Fin.ext_iff, hij]), if_pos hij]; ring
      · rw [if_neg (by simp [Fin.ext_iff, hij]), if_neg hij]; ring



private theorem p3w_dot_comm (a b : List ℤ) : ggLWdot a b = ggLWdot b a := by
  induction a generalizing b with
  | nil => cases b <;> simp [ggLWdot]
  | cons x xs ih =>
      cases b with
      | nil => simp [ggLWdot]
      | cons y ys =>
          simp only [ggLWdot, List.zipWith_cons_cons, List.sum_cons]
          rw [show (List.zipWith (fun x1 x2 : ℤ => x1 * x2) xs ys).sum
                = (List.zipWith (fun x1 x2 : ℤ => x1 * x2) ys xs).sum from ih ys]
          ring

private theorem p3w_word_length {n : ℕ} (X : Matrix (Option (Fin n)) (Option (Fin n)) ℤ)
    (ψ : List ℕ) (l : List ℤ) : (ggLWword (ggLWmat X) ψ l).length = l.length := by
  induction ψ with
  | nil => rfl
  | cons j ψ ih =>
      show (ggLWrefl (ggLWmat X) j (ggLWword (ggLWmat X) ψ l)).length = l.length
      simp only [ggLWrefl, List.length_mapIdx]
      exact ih

private theorem p3w_wordR_length {n : ℕ} (X : Matrix (Option (Fin n)) (Option (Fin n)) ℤ)
    (ψ : List ℕ) (l : List ℤ) : (ggLWwordR (ggLWmat X) ψ l).length = l.length := by
  induction ψ with
  | nil => rfl
  | cons j ψ ih =>
      show (ggLWreflR (ggLWmat X) j (ggLWwordR (ggLWmat X) ψ l)).length = l.length
      simp only [ggLWreflR, List.length_mapIdx]
      exact ih

private theorem p3w_sReflR_bridge {n : ℕ} (X : Matrix (Option (Fin n)) (Option (Fin n)) ℤ)
    {j : ℕ} (hj : j ≤ n) (c : List ℤ) (hc : c.length = n + 1) :
    ggSReflR X (ggLWnode n j) (p3w_vecOf c) = p3w_vecOf (ggLWreflR (ggLWmat X) j c) := by
  have hcol : (∑ i : Option (Fin n), p3w_vecOf c i * X i (ggLWnode n j))
      = ∑ b ∈ Finset.range (n + 1), c.getD b 0 * X (ggLWnode n b) (ggLWnode n j) := by
    rw [p3w_sum_option_range]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [p3w_node c (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))]
  have hmap : (ggLWmat X).map (fun row => row.getD j 0)
      = (List.range (n + 1)).map (fun b => X (ggLWnode n b) (ggLWnode n j)) := by
    simp only [ggLWmat, List.map_map]
    apply List.map_congr_left
    intro a _
    change ((List.range (n + 1)).map (fun b => X (ggLWnode n a) (ggLWnode n b))).getD j 0
      = X (ggLWnode n a) (ggLWnode n j)
    have hlt : j < ((List.range (n + 1)).map (fun b => X (ggLWnode n a) (ggLWnode n b))).length :=
      by
      simp only [List.length_map, List.length_range]; omega
    rw [List.getD_eq_getElem _ _ hlt, List.getElem_map, List.getElem_range]
  have hdot : ggLWdot c ((ggLWmat X).map (fun row => row.getD j 0))
      = ∑ b ∈ Finset.range (n + 1), c.getD b 0 * X (ggLWnode n b) (ggLWnode n j) := by
    rw [hmap, p3w_dot_comm, p3w_dot_map _ c hc]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  have hlen : (ggLWreflR (ggLWmat X) j c).length = n + 1 := by
    simp only [ggLWreflR, List.length_mapIdx, hc]
  funext o
  rw [show ggSReflR X (ggLWnode n j) (p3w_vecOf c)
      = p3w_vecOf c - (∑ i : Option (Fin n), p3w_vecOf c i * X i (ggLWnode n j)) •
          Pi.single (ggLWnode n j) 1 from rfl]
  rw [hcol, ← hdot]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rcases o with _ | i
  · rw [p3w_node_none,
      show p3w_vecOf (ggLWreflR (ggLWmat X) j c) none
        = (ggLWreflR (ggLWmat X) j c).getD n 0 from rfl]
    rw [List.getD_eq_getElem (ggLWreflR (ggLWmat X) j c) 0 (by rw [hlen]; omega)]
    simp only [ggLWreflR, List.getElem_mapIdx]
    rw [← List.getD_eq_getElem c 0 (by omega)]
    by_cases hjn : j = n
    · rw [hjn, show ggLWnode n n = none from dif_neg (Nat.lt_irrefl n)]
      rw [Pi.single_apply, if_pos rfl, if_pos rfl]
      ring
    · have hjs : j < n := lt_of_le_of_ne hj hjn
      rw [show ggLWnode n j = some ⟨j, hjs⟩ from dif_pos hjs]
      rw [Pi.single_apply, if_neg (by simp), mul_zero, sub_zero,
        if_neg (by omega : ¬ n = j)]
  · rw [p3w_node_some,
      show p3w_vecOf (ggLWreflR (ggLWmat X) j c) (some i)
        = (ggLWreflR (ggLWmat X) j c).getD i.1 0 from rfl]
    rw [List.getD_eq_getElem (ggLWreflR (ggLWmat X) j c) 0 (by rw [hlen]; omega)]
    simp only [ggLWreflR, List.getElem_mapIdx]
    rw [← List.getD_eq_getElem c 0 (by omega)]
    by_cases hjn : j = n
    · rw [hjn, show ggLWnode n n = none from dif_neg (Nat.lt_irrefl n)]
      rw [Pi.single_apply, if_neg (by simp), if_neg (by omega : ¬ i.1 = n)]
      ring
    · have hjs : j < n := lt_of_le_of_ne hj hjn
      rw [show ggLWnode n j = some ⟨j, hjs⟩ from dif_pos hjs]
      rw [Pi.single_apply]
      by_cases hij : i.1 = j
      · rw [if_pos (by simp [Fin.ext_iff, hij]), if_pos hij]; ring
      · rw [if_neg (by simp [Fin.ext_iff, hij]), if_neg hij]; ring



private theorem p3w_sWord_bridge {n : ℕ} (X : Matrix (Option (Fin n)) (Option (Fin n)) ℤ)
    (ψ : List ℕ) (hψ : ∀ j ∈ ψ, j ≤ n) (l : List ℤ) (hl : l.length = n + 1) :
    ggSWord X (ψ.map (ggLWnode n)) (p3w_vecOf l) = p3w_vecOf (ggLWword (ggLWmat X) ψ l) := by
  induction ψ generalizing l with
  | nil => rfl
  | cons j ψ ih =>
      have hj : j ≤ n := hψ j (by simp)
      have hψ' : ∀ t ∈ ψ, t ≤ n := fun t ht => hψ t (by simp [ht])
      show ggSRefl X (ggLWnode n j) (ggSWord X (ψ.map (ggLWnode n)) (p3w_vecOf l))
        = p3w_vecOf (ggLWrefl (ggLWmat X) j (ggLWword (ggLWmat X) ψ l))
      rw [ih hψ' l hl,
        p3w_sRefl_bridge X hj (ggLWword (ggLWmat X) ψ l) (by rw [p3w_word_length, hl])]

private theorem p3w_sWordR_bridge {n : ℕ} (X : Matrix (Option (Fin n)) (Option (Fin n)) ℤ)
    (ψ : List ℕ) (hψ : ∀ j ∈ ψ, j ≤ n) (l : List ℤ) (hl : l.length = n + 1) :
    ggSWordR X (ψ.map (ggLWnode n)) (p3w_vecOf l)
      = p3w_vecOf (ggLWwordR (ggLWmat X) ψ l) := by
  induction ψ generalizing l with
  | nil => rfl
  | cons j ψ ih =>
      have hj : j ≤ n := hψ j (by simp)
      have hψ' : ∀ t ∈ ψ, t ≤ n := fun t ht => hψ t (by simp [ht])
      show ggSReflR X (ggLWnode n j) (ggSWordR X (ψ.map (ggLWnode n)) (p3w_vecOf l))
        = p3w_vecOf (ggLWreflR (ggLWmat X) j (ggLWwordR (ggLWmat X) ψ l))
      rw [ih hψ' l hl,
        p3w_sReflR_bridge X hj (ggLWwordR (ggLWmat X) ψ l) (by rw [p3w_wordR_length, hl])]

private theorem p3w_unit_succ {n k : ℕ} (hk : k < n) :
    ggLWunit (n + 1) k = ggLWunit n k ++ [0] := by
  simp only [ggLWunit, List.range_succ, List.map_append, List.map_cons, List.map_nil]
  rw [if_neg (by omega : ¬ n = k)]

private theorem p3w_node_inj {n t k : ℕ} (ht : t ≤ n) (hk : k ≤ n)
    (h : ggLWnode n t = ggLWnode n k) : t = k := by
  by_cases ht' : t < n
  · rw [show ggLWnode n t = some ⟨t, ht'⟩ from dif_pos ht'] at h
    by_cases hk' : k < n
    · rw [show ggLWnode n k = some ⟨k, hk'⟩ from dif_pos hk'] at h
      exact congrArg Fin.val (Option.some.inj h)
    · rw [show ggLWnode n k = none from dif_neg hk'] at h
      exact absurd h (by simp)
  · have htn : t = n := le_antisymm ht (le_of_not_gt ht')
    by_cases hk' : k < n
    · rw [show ggLWnode n t = none from dif_neg ht',
        show ggLWnode n k = some ⟨k, hk'⟩ from dif_pos hk'] at h
      exact absurd h (by simp)
    · have hkn : k = n := le_antisymm hk (le_of_not_gt hk')
      omega

private theorem p3w_unit_bridge_point {n : ℕ} (k : ℕ) (hk : k ≤ n) {t : ℕ} (ht : t ≤ n) :
    p3w_vecOf (ggLWunit (n + 1) k) (ggLWnode n t)
      = (Pi.single (ggLWnode n k) (1 : ℤ) : Option (Fin n) → ℤ) (ggLWnode n t) := by
  rw [p3w_node (ggLWunit (n + 1) k) ht, Pi.single_apply]
  have hone : (ggLWunit (n + 1) k).getD t 0 = if t = k then (1 : ℤ) else 0 := by
    simp only [ggLWunit]
    rw [List.getD_eq_getElem _ _ (by simp [List.length_map, List.length_range]; omega)]
    rw [List.getElem_map, List.getElem_range]
  rw [hone]
  by_cases htk : t = k
  · rw [if_pos htk, if_pos (by rw [htk])]
  · rw [if_neg htk, if_neg (fun h => htk (p3w_node_inj ht hk h))]

private theorem p3w_unit_bridge {n : ℕ} (k : ℕ) (hk : k ≤ n) :
    p3w_vecOf (ggLWunit (n + 1) k) = (Pi.single (ggLWnode n k) (1 : ℤ) : Option (Fin n) → ℤ) := by
  funext o
  rcases o with _ | i
  · rw [← show ggLWnode n n = none from dif_neg (Nat.lt_irrefl n)]
    exact p3w_unit_bridge_point k hk (le_refl n)
  · rw [← p3w_node_fin i]
    exact p3w_unit_bridge_point k hk (le_of_lt i.2)

private theorem p3w_rowC {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) {j : ℕ} (hj : j < n) :
    (ggLWmatC C).getD j [] =
      (List.range n).map (fun b => if hb : b < n then C ⟨j, hj⟩ ⟨b, hb⟩ else 0) := by
  have hlt : j < (ggLWmatC C).length := by
    simp only [ggLWmatC, List.length_map, List.length_range]; omega
  rw [List.getD_eq_getElem _ _ hlt]
  simp only [ggLWmatC, List.getElem_map, List.getElem_range]
  simp only [dif_pos hj]



private theorem p3w_attach_sRefl_bridge {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (k : Fin n)
    {j : ℕ} (hj : j < n) (v : List ℤ) (hv : v.length = n) :
    ggSRefl (ggAttachCartan C k) (ggLWnode n j) (p3w_vecOf (v ++ [0]))
      = p3w_vecOf (ggLWrefl (ggLWmatC C) j v ++ [0]) := by
  have hdot : ggLWdot ((ggLWmatC C).getD j []) v
      = ∑ b ∈ Finset.range n, (if hb : b < n then C ⟨j, hj⟩ ⟨b, hb⟩ else 0) * v.getD b 0 := by
    rw [p3w_rowC C hj, p3w_dot_map (fun b => if hb : b < n then C ⟨j, hj⟩ ⟨b, hb⟩ else 0) v (by rw
      [hv])]
  have hsum : (∑ o : Option (Fin n),
        ggAttachCartan C k (ggLWnode n j) o * p3w_vecOf (v ++ [0]) o)
      = ggLWdot ((ggLWmatC C).getD j []) v := by
    rw [Fintype.sum_option]
    have hnone : ggAttachCartan C k (ggLWnode n j) (none : Option (Fin n))
        * p3w_vecOf (v ++ [0]) (none : Option (Fin n)) = 0 := by
      rw [p3w_node_none]
      have h0 : (v ++ [0]).getD n 0 = (0 : ℤ) := by
        rw [List.getD_append_right v [0] 0 n (by rw [hv])]
        simp
      rw [h0, mul_zero]
    rw [hnone, zero_add]
    have hsome : (∑ i : Fin n, ggAttachCartan C k (ggLWnode n j) (some i)
          * p3w_vecOf (v ++ [0]) (some i))
        = ∑ i : Fin n, C ⟨j, hj⟩ i * v.getD i.1 0 := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [show ggLWnode n j = some ⟨j, hj⟩ from dif_pos hj, ggAttachCartan_some_some,
        p3w_node_some]
      congr 1
      rw [List.getD_append v [0] 0 i.1 (by rw [hv]; exact i.2)]
    rw [hsome, hdot]
    have hF : (∑ i : Fin n, C ⟨j, hj⟩ i * v.getD i.1 0)
        = ∑ i : Fin n,
            (if hb : i.1 < n then C ⟨j, hj⟩ ⟨i.1, hb⟩ * v.getD i.1 0 else 0) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [dif_pos i.2]
    rw [hF, Fin.sum_univ_eq_sum_range
      (fun b => if hb : b < n then C ⟨j, hj⟩ ⟨b, hb⟩ * v.getD b 0 else 0) n]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases hb : b < n
    · simp only [dif_pos hb]
    · simp only [dif_neg hb, zero_mul]
  have hlen : (ggLWrefl (ggLWmatC C) j v).length = n := by
    simp only [ggLWrefl, List.length_mapIdx, hv]
  rw [show ggSRefl (ggAttachCartan C k) (ggLWnode n j) (p3w_vecOf (v ++ [0]))
      = p3w_vecOf (v ++ [0]) - (∑ o : Option (Fin n),
          ggAttachCartan C k (ggLWnode n j) o * p3w_vecOf (v ++ [0]) o) •
          Pi.single (ggLWnode n j) 1 from rfl, hsum]
  funext o
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rcases o with _ | i
  · rw [p3w_node_none]
    have h0 : (v ++ [0]).getD n 0 = (0 : ℤ) := by
      rw [List.getD_append_right v [0] 0 n (by rw [hv])]
      simp
    rw [show ggLWnode n j = some ⟨j, hj⟩ from dif_pos hj,
      Pi.single_apply, if_neg (fun h => by cases h)]
    rw [h0, mul_zero, sub_zero]
    rw [p3w_node_none,
      List.getD_append_right (ggLWrefl (ggLWmatC C) j v) [0] 0 n (by rw [hlen])]
    simp
  · rw [p3w_node_some,
      show ggLWnode n j = some ⟨j, hj⟩ from dif_pos hj, Pi.single_apply]
    rw [List.getD_append v [0] 0 i.1 (by rw [hv]; exact i.2)]
    rw [show p3w_vecOf (ggLWrefl (ggLWmatC C) j v ++ [0]) (some i)
        = (ggLWrefl (ggLWmatC C) j v ++ [0]).getD i.1 0 from rfl]
    rw [List.getD_append (ggLWrefl (ggLWmatC C) j v) [0] 0 i.1 (by rw [hlen]; exact i.2)]
    have hr : (ggLWrefl (ggLWmatC C) j v).getD i.1 0
        = if i.1 = j then v.getD i.1 0 - ggLWdot ((ggLWmatC C).getD j []) v
          else v.getD i.1 0 := by
      rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact i.2)]
      simp only [ggLWrefl, List.getElem_mapIdx]
      rw [← List.getD_eq_getElem v 0 (by rw [hv]; exact i.2)]
    rw [hr]
    by_cases hij : i.1 = j
    · rw [if_pos hij, if_pos (by simp [Fin.ext_iff, hij])]; ring
    · rw [if_neg hij, if_neg (by simp [Fin.ext_iff, hij])]; ring



private theorem p3w_mem_R {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (k : Fin n) (R : List (List ℤ))
    (hclosed : ggLWclosed (ggLWmatC C) n R = true) :
    ∀ v ∈ ggLCoroots (ggAttachCartan C k),
      ∃ l ∈ R, l.length = n ∧ v = p3w_vecOf (l ++ [0]) := by
  have hcl := hclosed
  simp only [ggLWclosed, Bool.and_eq_true, List.all_eq_true] at hcl
  obtain ⟨hunit, hrefl⟩ := hcl
  intro v hv
  obtain ⟨ψ, i, rfl⟩ := hv
  induction ψ with
  | nil =>
      refine ⟨ggLWunit n i.1, ?_, ?_, ?_⟩
      · exact List.contains_iff_mem.mp (hunit i.1 (List.mem_range.mpr i.2))
      · simp only [ggLWunit, List.length_map, List.length_range]
      · rw [← p3w_unit_succ i.2, p3w_unit_bridge i.1 (le_of_lt i.2), p3w_node_fin i]
        rfl
  | cons j ψ ih =>
      obtain ⟨l, hlR, hll, hleq⟩ := ih
      refine ⟨ggLWrefl (ggLWmatC C) j.1 l, ?_, ?_, ?_⟩
      · exact List.contains_iff_mem.mp (hrefl l hlR j.1 (List.mem_range.mpr j.2))
      · simp only [ggLWrefl, List.length_mapIdx, hll]
      · rw [show ggSWord (ggAttachCartan C k) ((j :: ψ).map some) (Pi.single (some i) 1)
            = ggSRefl (ggAttachCartan C k) (some j)
                (ggSWord (ggAttachCartan C k) (ψ.map some) (Pi.single (some i) 1)) from rfl,
          hleq, show some j = ggLWnode n j.1 from (p3w_node_fin j).symm,
          p3w_attach_sRefl_bridge C k j.2 l hll]



private theorem p3w_pair_bridge {n : ℕ} (X : Matrix (Option (Fin n)) (Option (Fin n)) ℤ)
    (cL gL : List ℤ) (hc : cL.length = n + 1) (hg : gL.length = n + 1) :
    (∑ i : Option (Fin n), ∑ j : Option (Fin n), p3w_vecOf cL i * X i j * p3w_vecOf gL j)
      = ggLWdot cL ((ggLWmat X).map fun row => ggLWdot row gL) := by
  have hL : (∑ i : Option (Fin n), ∑ j : Option (Fin n),
        p3w_vecOf cL i * X i j * p3w_vecOf gL j)
      = ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1),
          cL.getD a 0 * X (ggLWnode n a) (ggLWnode n b) * gL.getD b 0 := by
    rw [p3w_sum_option_range]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [p3w_sum_option_range]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [p3w_node cL (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)),
      p3w_node gL (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))]
  have hR : ggLWdot cL ((ggLWmat X).map fun row => ggLWdot row gL)
      = ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1),
          cL.getD a 0 * X (ggLWnode n a) (ggLWnode n b) * gL.getD b 0 := by
    have hmap : (ggLWmat X).map (fun row => ggLWdot row gL)
        = (List.range (n + 1)).map (fun a => ggLWdot ((List.range (n + 1)).map
            (fun b => X (ggLWnode n a) (ggLWnode n b))) gL) := by
      simp only [ggLWmat, List.map_map, Function.comp_def]
    rw [p3w_dot_comm, hmap,
      p3w_dot_map (fun a => ggLWdot ((List.range (n + 1)).map
        (fun b => X (ggLWnode n a) (ggLWnode n b))) gL) cL hc]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [p3w_dot_map (fun b => X (ggLWnode n a) (ggLWnode n b)) gL hg, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [hL, hR]

private theorem p3w_zipWith_getD_of_lt (f : ℤ → ℤ → ℤ) (a b : List ℤ) {t : ℕ}
    (ha : t < a.length) (hb : t < b.length) :
    (List.zipWith f a b).getD t 0 = f (a.getD t 0) (b.getD t 0) := by
  have ht : t < (List.zipWith f a b).length := by
    rw [List.length_zipWith]; exact lt_min ha hb
  rw [List.getD_eq_getElem _ _ ht, List.getElem_zipWith,
    ← List.getD_eq_getElem a 0 ha, ← List.getD_eq_getElem b 0 hb]

private theorem p3w_all_zipWith_mod3 {a b : List ℤ} (hlen : a.length = b.length)
    (h : ∀ t < a.length, (a.getD t 0 - b.getD t 0) % 3 = 0) :
    (List.zipWith (fun x y => decide ((x - y) % 3 = 0)) a b).all id = true := by
  rw [List.all_eq_true]
  intro x hx
  rw [List.mem_iff_getElem] at hx
  obtain ⟨t, ht, htx⟩ := hx
  have hta : t < a.length := by
    rw [List.length_zipWith] at ht
    exact lt_of_lt_of_le ht (min_le_left _ _)
  have htb : t < b.length := by
    rw [← hlen]
    exact hta
  rw [← htx, List.getElem_zipWith (h := ht)]
  rw [← List.getD_eq_getElem a 0 hta, ← List.getD_eq_getElem b 0 htb]
  exact decide_eq_true_eq.mpr (h t hta)


theorem ggInvTest3_of_data {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (k : Fin n)
    (R : List (List ℤ)) (ψ : List ℕ) (k₀ i₀ : ℕ)
    (hclosed : ggLWclosed (ggLWmatC C) n R = true)
    (htest : ggLWtest3 (ggLWmat (ggAttachCartan C k)) n R ψ k₀ i₀ = true) :
    GGInvTest3 (ggAttachCartan C k) := by
  set XL : List (List ℤ) := ggLWmat (ggAttachCartan C k) with hXL
  have hd := htest
  simp only [ggLWtest3, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.not_eq_true'] at hd
  set wL : List ℤ := ggLWword XL ψ (ggLWunit (n + 1) k₀) with hwL
  set cL : List ℤ := ggLWwordR XL ψ (ggLWunit (n + 1) k₀) with hcL
  set ρL : List ℤ := ggLWunit (n + 1) i₀ with hρL
  set e : ℤ := ggLWdot cL (XL.map fun row => ggLWdot row ρL) with he
  set img : List ℤ := List.zipWith (fun x y => x - e * y) ρL wL with himg
  obtain ⟨⟨⟨⟨hψ, hk₀⟩, hi₀⟩, hc₀⟩, hR⟩ := hd
  refine ⟨ψ.map (ggLWnode n), ggLWnode n k₀, Pi.single (ggLWnode n i₀) (1 : ℤ),
    ?_, ?_, ?_⟩
  · refine ⟨[], ⟨i₀, hi₀⟩, ?_⟩
    rw [p3w_node_fin ⟨i₀, hi₀⟩]
    rfl
  · have hN : (ggLWunit (n + 1) k₀).length = n + 1 := by
      simp only [ggLWunit, List.length_map, List.length_range]
    have hsw : ggSWordR (ggAttachCartan C k) (ψ.map (ggLWnode n))
        (Pi.single (ggLWnode n k₀) (1 : ℤ)) = p3w_vecOf cL := by
      rw [← p3w_unit_bridge k₀ hk₀]
      have h := p3w_sWordR_bridge (ggAttachCartan C k) ψ hψ (ggLWunit (n + 1) k₀) hN
      rwa [← hXL, ← hcL] at h
    rw [hsw]
    simp only [p3w_node_none]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (cL.getD n 0) 3).mpr
      (Int.dvd_of_emod_eq_zero hc₀)
  · intro v hv hcon
    obtain ⟨r, hrR, hrlen, hrv⟩ := p3w_mem_R C k R hclosed v hv
    have hN : (ggLWunit (n + 1) k₀).length = n + 1 := by
      simp only [ggLWunit, List.length_map, List.length_range]
    have hNi : (ggLWunit (n + 1) i₀).length = n + 1 := by
      simp only [ggLWunit, List.length_map, List.length_range]
    have hwL_len : wL.length = n + 1 := by
      rw [hwL, p3w_word_length, hN]
    have hcL_len : cL.length = n + 1 := by
      rw [hcL, p3w_wordR_length, hN]
    have hρL_len : ρL.length = n + 1 := by
      rw [hρL, hNi]
    have hw : ggSWord (ggAttachCartan C k) (ψ.map (ggLWnode n))
        (Pi.single (ggLWnode n k₀) (1 : ℤ)) = p3w_vecOf wL := by
      rw [← p3w_unit_bridge k₀ hk₀]
      have h := p3w_sWord_bridge (ggAttachCartan C k) ψ hψ (ggLWunit (n + 1) k₀) hN
      rwa [← hXL, ← hwL] at h
    have hc : ggSWordR (ggAttachCartan C k) (ψ.map (ggLWnode n))
        (Pi.single (ggLWnode n k₀) (1 : ℤ)) = p3w_vecOf cL := by
      rw [← p3w_unit_bridge k₀ hk₀]
      have h := p3w_sWordR_bridge (ggAttachCartan C k) ψ hψ (ggLWunit (n + 1) k₀) hN
      rwa [← hXL, ← hcL] at h
    have hρ : Pi.single (ggLWnode n i₀) (1 : ℤ) = p3w_vecOf ρL := by
      rw [hρL]
      exact (p3w_unit_bridge i₀ (le_of_lt hi₀)).symm
    have hE : (∑ i' : Option (Fin n), ggSWordR (ggAttachCartan C k)
          (ψ.map (ggLWnode n)) (Pi.single (ggLWnode n k₀) (1 : ℤ)) i' *
          ∑ j : Option (Fin n), ggAttachCartan C k i' j *
            (Pi.single (ggLWnode n i₀) (1 : ℤ) : Option (Fin n) → ℤ) j) = e := by
      rw [hc, hρ, he, hXL]
      rw [← p3w_pair_bridge (ggAttachCartan C k) cL ρL hcL_len hρL_len]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    have hpoint : ∀ a ≤ n, (img.getD a 0 - (r ++ [0]).getD a 0) % 3 = 0 := by
      intro a ha
      have h1 := congrFun hcon (ggLWnode n a)
      rw [hrv] at h1
      rw [p3w_node (r ++ [0]) ha] at h1
      rw [hE, hρ, hw] at h1
      rw [p3w_node ρL ha, p3w_node wL ha] at h1
      have himg_a : img.getD a 0 = ρL.getD a 0 - e * wL.getD a 0 := by
        rw [himg, p3w_zipWith_getD_of_lt (fun x y => x - e * y) ρL wL
          (by rw [hρL_len]; omega) (by rw [hwL_len]; omega)]
      have hcast : ((ρL.getD a 0 : ℤ) : ZMod 3) - ((e : ℤ) : ZMod 3) *
            ((wL.getD a 0 : ℤ) : ZMod 3) = ((img.getD a 0 : ℤ) : ZMod 3) := by
        rw [himg_a]
        push_cast
        ring
      rw [hcast] at h1
      have hz : ((img.getD a 0 - (r ++ [0]).getD a 0 : ℤ) : ZMod 3) = 0 := by
        rw [Int.cast_sub, h1, sub_self]
      exact Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hz)
    have himg_len : img.length = n + 1 := by
      rw [himg, List.length_zipWith, hρL_len, hwL_len, min_self]
    have hr0_len : (r ++ [0]).length = n + 1 := by
      rw [List.length_append, hrlen]
      simp
    have hlen : img.length = (r ++ [0]).length := by rw [himg_len, hr0_len]
    have hall : (List.zipWith (fun a b => decide ((a - b) % 3 = 0)) img
        (r ++ [0])).all id = true :=
      p3w_all_zipWith_mod3 hlen (fun t ht => hpoint t (by rw [himg_len] at ht; omega))
    have hfalse := hR r hrR
    rw [hall] at hfalse
    exact absurd hfalse (by decide)

end CFSG.StandardType
