module

public import CFSG.Sporadic.Schreier.Co1OddACCheck
public import CFSG.Sporadic.Schreier.Co1FullOrbits
public import CFSG.Sporadic.Co1.Module.OddNative
public import Certificates.Certificate2135

public section

namespace CFSG.Sporadic.Co1Schreier.OddRows

open CFSG.Sporadic.SmallF2 (toVecD toVecD_injective rowsMatrix rowsMatrix_mulRows
  rowsMatrix_idRows rowsMatrix_powRows rowsMatrix_transposeRows)
open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative Matrix

section Rows

variable {M : Type*} [Monoid M] {φ : M →* Matrix (Fin 24) (Fin 24) (ZMod 2)}

theorem pow_eq_one_of_rows (hφ : Function.Injective φ) {g : M} {X : Array ℕ}
    (hg : φ g = rowsMatrix 24 X) {k : ℕ} (h : powRows 24 X k = idRows 24) : g ^ k = 1 :=
  hφ (by rw [map_pow, hg, ← rowsMatrix_powRows, h, rowsMatrix_idRows, map_one])

theorem mul_eq_one_of_rows (hφ : Function.Injective φ) {g h : M} {X Y : Array ℕ}
    (hg : φ g = rowsMatrix 24 X) (hh : φ h = rowsMatrix 24 Y) (e : mulRows 24 X Y = idRows 24) :
    g * h = 1 :=
  hφ (by rw [map_mul, hg, hh, ← rowsMatrix_mulRows, e, rowsMatrix_idRows, map_one])

theorem commute_of_rows (hφ : Function.Injective φ) {g h : M} {X Y : Array ℕ}
    (hg : φ g = rowsMatrix 24 X) (hh : φ h = rowsMatrix 24 Y)
    (e : mulRows 24 X Y = mulRows 24 Y X) : g * h = h * g :=
  hφ (by rw [map_mul, map_mul, hg, hh, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows, e])

theorem eq_of_rows (hφ : Function.Injective φ) {g h : M} {X : Array ℕ}
    (hg : φ g = rowsMatrix 24 X) (hh : φ h = rowsMatrix 24 X) : g = h :=
  hφ (hg.trans hh.symm)

theorem ne_one_of_rows {g : M} {X : Array ℕ} (hg : φ g = rowsMatrix 24 X)
    (hX : validRows X = true) (h : X ≠ idRows 24) : g ≠ 1 := by
  intro h1
  apply h
  apply CFSG.Sporadic.Co1.Module.Odd.rowsMatrix_injective_of_valid hX
    CFSG.Sporadic.Co1.Module.Odd.validRows_idRows
  rw [← hg, h1, map_one, rowsMatrix_idRows]

end Rows

theorem validRows_powRows {X : Array ℕ} (hX : validRows X = true) (k : ℕ) :
    validRows (powRows 24 X k) = true := by
  induction k with
  | zero => exact CFSG.Sporadic.Co1.Module.Odd.validRows_idRows
  | succ k ih => exact CFSG.Sporadic.Co1.Module.Odd.validRows_mulRows ih hX

theorem validRows_transposeRows (X : Array ℕ) : validRows (transposeRows 24 X) = true := by
  simp only [validRows, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq]
  refine ⟨by simp [transposeRows], fun i hi => ?_⟩
  have h := CFSG.Sporadic.Co1.Module.Odd.transposeRows_lt X i
  rw [Array.getElem?_eq_getElem hi, Option.getD_some] at h
  exact lt_of_lt_of_eq h (by norm_num)

section Programs

variable {G : Type*} [Group G] (K : Subgroup G)

theorem getD_mem {l : List G} (hl : ∀ g ∈ l, g ∈ K) (i : ℕ) : l.getD i 1 ∈ K := by
  rw [List.getD_eq_getElem?_getD]
  cases hk : l[i]? with
  | none => exact K.one_mem
  | some g => exact hl g (List.mem_of_getElem? hk)

theorem lineEval_mem {regs : List G} (hregs : ∀ g ∈ regs, g ∈ K) (fac : List (ℕ × ℕ)) :
    CFSG.Sporadic.Co1.Module.Odd.lineEval regs fac ∈ K := by
  unfold CFSG.Sporadic.Co1.Module.Odd.lineEval
  refine K.list_prod_mem fun x hx => ?_
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
  exact K.pow_mem (getD_mem K hregs p.1) p.2

theorem commute_lineEval {m : G} {regs : List G} (hregs : ∀ g ∈ regs, m * g = g * m)
    (fac : List (ℕ × ℕ)) :
    m * CFSG.Sporadic.Co1.Module.Odd.lineEval regs fac =
      CFSG.Sporadic.Co1.Module.Odd.lineEval regs fac * m := by
  have hc : ∀ g ∈ regs, Commute m g := hregs
  have hget : ∀ i : ℕ, Commute m (regs.getD i 1) := by
    intro i
    rw [List.getD_eq_getElem?_getD]
    cases hk : regs[i]? with
    | none => exact Commute.one_right m
    | some g => exact hc g (List.mem_of_getElem? hk)
  unfold CFSG.Sporadic.Co1.Module.Odd.lineEval
  refine Commute.list_prod_right _ _ fun x hx => ?_
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
  exact (hget p.1).pow_right p.2

theorem map_lineEval {H : Type*} [Group H] (f : G →* H) (regs : List G) (fac : List (ℕ × ℕ)) :
    f (CFSG.Sporadic.Co1.Module.Odd.lineEval regs fac) =
      CFSG.Sporadic.Co1.Module.Odd.lineEval (regs.map f) fac := by
  unfold CFSG.Sporadic.Co1.Module.Odd.lineEval
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  simp only [Function.comp_apply, map_pow]
  congr 1
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases regs[p.1]? with
  | none => simp
  | some g => simp

theorem runEval_mem (prog : List (List (ℕ × ℕ))) :
    ∀ {init : List G}, (∀ g ∈ init, g ∈ K) →
      ∀ g ∈ CFSG.Sporadic.Co1.Module.Odd.runEval init prog, g ∈ K := by
  induction prog with
  | nil => intro init h; exact h
  | cons fac prog ih =>
    intro init h
    refine ih fun g hg => ?_
    rcases List.mem_append.1 hg with hg | hg
    · exact h g hg
    · rw [List.mem_singleton.1 hg]
      exact lineEval_mem K h fac

end Programs

theorem eq_of_agree_rows {P Q : Matrix (Fin 24) (Fin 24) (ZMod 2)} {B B' : Array ℕ}
    (hB : rowsMatrix 24 B' * rowsMatrix 24 B = 1)
    (h : ∀ i < 24, P *ᵥ toVecD 24 (B[i]?.getD 0) = Q *ᵥ toVecD 24 (B[i]?.getD 0)) : P = Q := by
  have hcol : P * (rowsMatrix 24 B)ᵀ = Q * (rowsMatrix 24 B)ᵀ := by
    ext j i
    have hi := congrFun (h i.val i.isLt) j
    simp only [Matrix.mulVec, dotProduct] at hi
    simp only [Matrix.mul_apply, Matrix.transpose_apply, CFSG.Sporadic.SmallF2.rowsMatrix_apply]
    exact hi
  have hB' : (rowsMatrix 24 B)ᵀ * (rowsMatrix 24 B')ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hB, Matrix.transpose_one]
  calc P = P * ((rowsMatrix 24 B)ᵀ * (rowsMatrix 24 B')ᵀ) := by rw [hB', Matrix.mul_one]
    _ = Q * (rowsMatrix 24 B)ᵀ * (rowsMatrix 24 B')ᵀ := by rw [← Matrix.mul_assoc, hcol]
    _ = Q := by rw [Matrix.mul_assoc, hB', Matrix.mul_one]

theorem ncard_co1X_fix (Ms : List (Array ℕ)) :
    {v : Vec24 | v ∈ co1X ∧ ∀ M ∈ Ms, rowsMatrix 24 M *ᵥ v = v}.ncard =
      Native.oddCountFix (Native.fullOrb 2) 98280 (Ms.map (transposeRows 24)) := by
  set p : ℕ → Bool := fun i => (Ms.map (transposeRows 24)).all fun Mt =>
    isFixedN Mt ((Native.fullOrb 2).pts[i]!) with hp
  have hpi : ∀ i < 98280, (p i = true ↔
      ∀ M ∈ Ms, rowsMatrix 24 M *ᵥ toVecD 24 ((Native.fullOrb 2).pts[i]!) =
        toVecD 24 ((Native.fullOrb 2).pts[i]!)) := by
    intro i hi
    rw [hp, List.all_eq_true]
    constructor
    · intro h M hM
      exact (CFSG.Sporadic.Co1.Module.Odd.isFixedN_iff M (fullOrb_two_lt hi)).1
        (h _ (List.mem_map_of_mem hM))
    · intro h Mt hMt
      obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hMt
      exact (CFSG.Sporadic.Co1.Module.Odd.isFixedN_iff M (fullOrb_two_lt hi)).2 (h M hM)
  have hset : {v : Vec24 | v ∈ co1X ∧ ∀ M ∈ Ms, rowsMatrix 24 M *ᵥ v = v} =
      (fun i => toVecD 24 ((Native.fullOrb 2).pts[i]!)) '' {i | i < 98280 ∧ p i = true} := by
    ext v
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, hfix⟩
      rw [← fullOrb_two] at hfix
      exact ⟨i, ⟨hi, (hpi i hi).2 hfix⟩, by rw [fullOrb_two]⟩
    · rintro ⟨i, ⟨hi, hpi'⟩, rfl⟩
      exact ⟨⟨i, hi, by rw [fullOrb_two]⟩, (hpi i hi).1 hpi'⟩
  rw [hset, Set.InjOn.ncard_image (fun i hi j hj e => fullOrb_two_inj hi.1 hj.1 e),
    Native.oddCountFix, CFSG.Sporadic.Co1.Module.Odd.countBelow_eq, zero_add,
    ← Set.ncard_coe_finset]
  congr 1
  ext i
  simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_range]
  exact Iff.rfl

end CFSG.Sporadic.Co1Schreier.OddRows
