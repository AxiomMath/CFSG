module

public import CFSG.Milestones.ASVolI.F48.D43.Field
public import CFSG.Sporadic.ON.VecSpec

public section

namespace CFSG.ASVolI

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.F3.Native CFSG.Sporadic.Fi23.Native
  CFSG.Sporadic.ON.Native


theorem burnsideF48d_hC : burnsideF48d_C.check = true := Tag.rootCertificate_check .D4

theorem burnsideF48d_hS : (Tag.stringData .D4).check burnsideF48d_C = true :=
  Tag.stringData_check .D4

theorem burnsideF48d_idx_ofIdx (a : CFSG.LieType.Ree.Idx burnsideF48d_C) :
    burnsideF48d_idx (burnsideF48d_ofIdx a) = a := by
  revert a
  decide

theorem burnsideF48d_ofIdx_lt (a : CFSG.LieType.Ree.Idx burnsideF48d_C) :
    burnsideF48d_ofIdx a < 28 := by
  revert a
  decide

section Vec

variable (K : Type*) [Field K]

@[expose] noncomputable def burnsideF48d_e (l : ℕ) : RootModule .D4 K :=
  Finsupp.single (toLabel burnsideF48d_hC (burnsideF48d_idx l)) 1

variable {K}

@[expose] noncomputable def burnsideF48d_colVec : Option (ℕ × ℤ) → RootModule .D4 K
  | none => 0
  | some (a, z) => (z : K) • burnsideF48d_e K a

variable [CharP K 3] (ω : K)

@[expose] noncomputable def burnsideF48d_vec (w : Array ℕ) : RootModule .D4 K :=
  ∑ l ∈ Finset.range 28, burnsideF48d_φ ω w[l]! • burnsideF48d_e K l

theorem burnsideF48d_vec_set {w : Array ℕ} {a : ℕ} (ha : a < w.size) (ha28 : a < 28) (x : ℕ) :
    burnsideF48d_vec ω (w.set! a x) = burnsideF48d_vec ω w +
      (burnsideF48d_φ ω x - burnsideF48d_φ ω w[a]!) • burnsideF48d_e K a := by
  unfold burnsideF48d_vec
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 ha28),
    ← Finset.add_sum_erase _ _ (Finset.mem_range.2 ha28), Array.getElem!_set!_self _ _ _ ha]
  have e : ∀ l ∈ (Finset.range 28).erase a, burnsideF48d_φ ω (w.set! a x)[l]! • burnsideF48d_e K l =
      burnsideF48d_φ ω w[l]! • burnsideF48d_e K l := by
    intro l hl
    rw [Array.getElem!_set!_ne _ _ _ _ (Finset.ne_of_mem_erase hl).symm]
  rw [Finset.sum_congr rfl e, sub_smul]
  abel

theorem burnsideF48d_vec_replicate : burnsideF48d_vec ω (Array.replicate 28 0) = 0 := by
  unfold burnsideF48d_vec
  refine Finset.sum_eq_zero fun l hl => ?_
  rw [getElem!_pos _ l (by simpa using hl), Array.getElem_replicate, burnsideF48d_φ_zero,
    zero_smul]

theorem burnsideF48d_vec_unit {b : ℕ} (hb : b < 28) :
    burnsideF48d_vec ω (burnsideF48d_unit b) = burnsideF48d_e K b := by
  unfold burnsideF48d_unit
  rw [burnsideF48d_vec_set ω (by simpa using hb) hb, burnsideF48d_vec_replicate,
    getElem!_pos _ b (by simpa using hb), Array.getElem_replicate, burnsideF48d_φ_one,
    burnsideF48d_φ_zero, sub_zero, one_smul, zero_add]

variable (hω : ω ^ 3 = ω + 1)

include hω in
theorem burnsideF48d_vec_opStep {col : Option (ℕ × ℤ)} (hcol : ∀ a z, col = some (a, z) → a < 28)
    (cw : ℕ) {out : Array ℕ} (hout : out.size = 28) :
    (burnsideF48d_opStep col cw out).size = 28 ∧
      burnsideF48d_vec ω (burnsideF48d_opStep col cw out) =
        burnsideF48d_vec ω out + burnsideF48d_φ ω cw • burnsideF48d_colVec col := by
  rcases col with _ | ⟨a, z⟩
  · simp [burnsideF48d_opStep, burnsideF48d_colVec, hout]
  · have ha := hcol a z rfl
    refine ⟨by simp [burnsideF48d_opStep, Array.size_set!, hout], ?_⟩
    simp only [burnsideF48d_opStep, burnsideF48d_colVec]
    rw [burnsideF48d_vec_set ω (by omega) ha, burnsideF48d_φ_add, burnsideF48d_φ_mul ω hω,
      burnsideF48d_φ_intC, add_sub_cancel_left, smul_smul]

include hω in
theorem burnsideF48d_vec_foldl_opStep (cols : ℕ → Option (ℕ × ℤ)) (cws : ℕ → ℕ) :
    ∀ (L : List ℕ), (∀ k ∈ L, ∀ a z, cols k = some (a, z) → a < 28) → ∀ (out : Array ℕ),
      out.size = 28 →
      (L.foldl (fun out k => burnsideF48d_opStep (cols k) (cws k) out) out).size = 28 ∧
      burnsideF48d_vec ω (L.foldl (fun out k => burnsideF48d_opStep (cols k) (cws k) out) out) =
        burnsideF48d_vec ω out +
          (L.map fun k => burnsideF48d_φ ω (cws k) • burnsideF48d_colVec (cols k)).sum := by
  intro L
  induction L with
  | nil => intro _ out hout; simp [hout]
  | cons k L ih =>
    intro hcol out hout
    obtain ⟨h1, h2⟩ := burnsideF48d_vec_opStep ω hω (hcol k List.mem_cons_self) (cws k) hout
    obtain ⟨h3, h4⟩ := ih (fun k' hk' => hcol k' (List.mem_cons_of_mem _ hk')) _ h1
    refine ⟨h3, ?_⟩
    rw [List.foldl_cons, h4, h2, List.map_cons, List.sum_cons, add_assoc]

end Vec

theorem burnsideF48d_colTab_get (y : Bool) {i k b : ℕ} (hi : i < 4) (hk : k < 4) (hb : b < 28) :
    ((((burnsideF48d_colTab ())[if y then 1 else 0]!)[i]!)[k]!)[b]! = burnsideF48d_col y i k b := by
  unfold burnsideF48d_colTab
  cases y <;>
  simp [getElem!_pos, hi, hk, hb, Array.getElem_map, Array.getElem_range]

theorem burnsideF48d_col_lt (y : Bool) (i k b : ℕ) :
    ∀ a z, burnsideF48d_col y i k b = some (a, z) → a < 28 := by
  intro a z h
  unfold burnsideF48d_col at h
  split at h
  · obtain ⟨p, -, hp⟩ := Option.map_eq_some_iff.1 h
    cases hp
    exact burnsideF48d_ofIdx_lt _
  · cases h

section Ops

variable {K : Type*} [Field K]

theorem burnsideF48d_colVec_map (u : CFSG.LieType.Ree.Col burnsideF48d_C) :
    burnsideF48d_colVec (K := K) (u.map fun p => (burnsideF48d_ofIdx p.1, p.2)) =
      toVec burnsideF48d_hC K u := by
  rcases u with _ | ⟨a, z⟩
  · rfl
  · simp only [Option.map_some, burnsideF48d_colVec, toVec_some, burnsideF48d_e,
      burnsideF48d_idx_ofIdx]

theorem burnsideF48d_colVec_col (y : Bool) {i : ℕ} (hi : i < 4) (k b : ℕ) :
    burnsideF48d_colVec (K := K) (burnsideF48d_col y i k b) =
      (if y then yCoeff .D4 K ⟨i, hi⟩ k else xCoeff .D4 K ⟨i, hi⟩ k) (burnsideF48d_e K b) := by
  unfold burnsideF48d_col
  rw [dif_pos hi]
  cases y
  · simp only [Bool.false_eq_true, if_false]
    rw [burnsideF48d_colVec_map, burnsideF48d_e,
      xCoeff_toLabel burnsideF48d_hC K burnsideF48d_hS]
  · simp only [if_true]
    rw [burnsideF48d_colVec_map, burnsideF48d_e,
      yCoeff_toLabel burnsideF48d_hC K burnsideF48d_hS]

variable (K) in
@[expose] noncomputable def burnsideF48d_op (y : Bool) (i : ℕ) (c : K) :
    Module.End K (RootModule .D4 K) :=
  if hi : i < 4 then (if y then yOp .D4 K ⟨i, hi⟩ c else xOp .D4 K ⟨i, hi⟩ c) else 1

theorem burnsideF48d_op_eq_sum (y : Bool) {i : ℕ} (hi : i < 4) (c : K) :
    burnsideF48d_op K y i c = ∑ k ∈ Finset.range 4,
      c ^ k • (if y then yCoeff .D4 K ⟨i, hi⟩ k else xCoeff .D4 K ⟨i, hi⟩ k) := by
  unfold burnsideF48d_op
  rw [dif_pos hi]
  cases y
  · simp only [Bool.false_eq_true, if_false]
    exact xOp_eq_sum_xCoeff _ c
  · simp only [if_true]
    exact yOp_eq_sum_yCoeff _ c

variable [CharP K 3] (ω : K) (hω : ω ^ 3 = ω + 1)

attribute [local irreducible] burnsideF48d_colTab in
include hω in
theorem burnsideF48d_vec_applyOp (y : Bool) {i : ℕ} (hi : i < 4) (c : ℕ) (w : Array ℕ) :
    (burnsideF48d_applyOp (burnsideF48d_colTab ()) y i c w).size = 28 ∧
      burnsideF48d_vec ω (burnsideF48d_applyOp (burnsideF48d_colTab ()) y i c w) =
        burnsideF48d_op K y i (burnsideF48d_φ ω c) (burnsideF48d_vec ω w) := by
  have hcoord : ∀ (b : ℕ), b < 28 → ∀ out : Array ℕ, out.size = 28 →
      (burnsideF48d_opCoord (burnsideF48d_colTab ()) y i c w out b).size = 28 ∧
      burnsideF48d_vec ω (burnsideF48d_opCoord (burnsideF48d_colTab ()) y i c w out b) =
        burnsideF48d_vec ω out + burnsideF48d_φ ω w[b]! •
          burnsideF48d_op K y i (burnsideF48d_φ ω c) (burnsideF48d_e K b) := by
    intro b hb out hout
    unfold burnsideF48d_opCoord
    by_cases h0 : w[b]! = 0
    · rw [if_pos h0, h0, burnsideF48d_φ_zero, zero_smul, add_zero]
      exact ⟨hout, rfl⟩
    · rw [if_neg h0]
      obtain ⟨h1, h2⟩ := burnsideF48d_vec_foldl_opStep ω hω
        (fun k => ((((burnsideF48d_colTab ())[if y then 1 else 0]!)[i]!)[k]!)[b]!)
        (fun k => burnsideF48d_mulC w[b]! (burnsideF48d_powC c k)) (List.range 4)
        (fun k hk a z h => by
          rw [burnsideF48d_colTab_get y hi (List.mem_range.1 hk) hb] at h
          exact burnsideF48d_col_lt y i k b a z h) out hout
      refine ⟨h1, ?_⟩
      rw [h2, burnsideF48d_op_eq_sum y hi, LinearMap.sum_apply, Finset.smul_sum]
      congr 1
      simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append,
        List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
        Finset.sum_range_succ, Finset.sum_range_zero]
      rw [burnsideF48d_colTab_get y hi (by norm_num : (0 : ℕ) < 4) hb,
        burnsideF48d_colTab_get y hi (by norm_num : (1 : ℕ) < 4) hb,
        burnsideF48d_colTab_get y hi (by norm_num : (2 : ℕ) < 4) hb,
        burnsideF48d_colTab_get y hi (by norm_num : (3 : ℕ) < 4) hb]
      simp only [burnsideF48d_colVec_col y hi, burnsideF48d_φ_mul ω hω, burnsideF48d_φ_pow ω hω,
        LinearMap.smul_apply, smul_smul, zero_add, add_zero]
  have hall : ∀ (L : List ℕ), (∀ b ∈ L, b < 28) → ∀ out : Array ℕ, out.size = 28 →
      (L.foldl (burnsideF48d_opCoord (burnsideF48d_colTab ()) y i c w) out).size = 28 ∧
      burnsideF48d_vec ω (L.foldl (burnsideF48d_opCoord (burnsideF48d_colTab ()) y i c w) out) =
        burnsideF48d_vec ω out + (L.map fun b => burnsideF48d_φ ω w[b]! •
          burnsideF48d_op K y i (burnsideF48d_φ ω c) (burnsideF48d_e K b)).sum := by
    intro L
    induction L with
    | nil => intro _ out hout; simp [hout]
    | cons b L ih =>
      intro hL out hout
      obtain ⟨h1, h2⟩ := hcoord b (hL b List.mem_cons_self) out hout
      obtain ⟨h3, h4⟩ := ih (fun b' hb' => hL b' (List.mem_cons_of_mem _ hb')) _ h1
      refine ⟨h3, ?_⟩
      rw [List.foldl_cons, h4, h2, List.map_cons, List.sum_cons, add_assoc]
  obtain ⟨h1, h2⟩ := hall (List.range 28) (fun b hb => List.mem_range.1 hb)
    (Array.replicate 28 0) (by simp)
  refine ⟨h1, ?_⟩
  unfold burnsideF48d_applyOp
  rw [h2, burnsideF48d_vec_replicate, zero_add, burnsideF48d_vec, map_sum]
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul]

@[expose] noncomputable def burnsideF48d_opEnd (op : Bool × ℕ × ℕ) :
    Module.End K (RootModule .D4 K) :=
  burnsideF48d_op K op.1 op.2.1 (burnsideF48d_φ ω op.2.2)

@[expose] noncomputable def burnsideF48d_genEnd (k : ℕ) : Module.End K (RootModule .D4 K) :=
  ((burnsideF48d_genSpec k).map (burnsideF48d_opEnd ω)).prod

theorem burnsideF48d_genSpec_lt (k : ℕ) : ∀ op ∈ burnsideF48d_genSpec k, op.2.1 < 4 := by
  intro op hop
  by_cases h0 : k = 0
  · simp only [burnsideF48d_genSpec, h0, if_true, List.mem_singleton] at hop
    rw [hop]; norm_num
  by_cases h1 : k = 1
  · simp only [burnsideF48d_genSpec, h1, if_true, List.mem_singleton, one_ne_zero,
      if_false] at hop
    rw [hop]; norm_num
  simp only [burnsideF48d_genSpec, h0, h1, if_false, List.mem_cons, List.mem_nil_iff,
    or_false] at hop
  rcases hop with rfl | rfl | rfl <;> norm_num

include hω in
theorem burnsideF48d_vec_genCol (k : ℕ) {b : ℕ} (hb : b < 28) :
    (burnsideF48d_genCol (burnsideF48d_colTab ()) k b).size = 28 ∧
      burnsideF48d_vec ω (burnsideF48d_genCol (burnsideF48d_colTab ()) k b) =
        burnsideF48d_genEnd ω k (burnsideF48d_e K b) := by
  have key : ∀ ops : List (Bool × ℕ × ℕ), (∀ op ∈ ops, op.2.1 < 4) →
      (ops.foldr (fun op w => burnsideF48d_applyOp (burnsideF48d_colTab ()) op.1 op.2.1 op.2.2 w)
        (burnsideF48d_unit b)).size = 28 ∧
      burnsideF48d_vec ω (ops.foldr (fun op w =>
        burnsideF48d_applyOp (burnsideF48d_colTab ()) op.1 op.2.1 op.2.2 w)
        (burnsideF48d_unit b)) = (ops.map (burnsideF48d_opEnd ω)).prod (burnsideF48d_e K b) := by
    intro ops
    induction ops with
    | nil =>
      intro _
      refine ⟨by simp [burnsideF48d_unit, Array.size_set!], ?_⟩
      rw [List.foldr_nil, burnsideF48d_vec_unit ω hb, List.map_nil, List.prod_nil,
        Module.End.one_apply]
    | cons op ops ih =>
      intro hops
      obtain ⟨-, h2⟩ := ih fun op' h => hops op' (List.mem_cons_of_mem _ h)
      obtain ⟨h3, h4⟩ := burnsideF48d_vec_applyOp ω hω op.1 (hops op List.mem_cons_self) op.2.2
        (ops.foldr (fun op w =>
          burnsideF48d_applyOp (burnsideF48d_colTab ()) op.1 op.2.1 op.2.2 w)
          (burnsideF48d_unit b))
      refine ⟨by rw [List.foldr_cons]; exact h3, ?_⟩
      rw [List.foldr_cons, h4, h2, List.map_cons, List.prod_cons, Module.End.mul_apply]
      rfl
  exact key _ (burnsideF48d_genSpec_lt k)

end Ops

section Real

variable {K : Type*} [Field K] [CharP K 3] (ω : K)

variable (K) in
noncomputable abbrev burnsideF48d_z : ZMod 3 →+* K := ZMod.castHom (dvd_refl 3) K

@[expose] noncomputable def burnsideF48d_b (q : ℕ) : RootModule .D4 K :=
  if q < 84 then ω ^ (q % 3) • burnsideF48d_e K (q / 3) else 0

@[expose] noncomputable def burnsideF48d_Ψ (r : Fin 154 → ZMod 3) : RootModule .D4 K :=
  ∑ q : Fin 154, burnsideF48d_z K (r q) • burnsideF48d_b ω q

theorem burnsideF48d_Ψ_add (r s : Fin 154 → ZMod 3) :
    burnsideF48d_Ψ ω (r + s) = burnsideF48d_Ψ ω r + burnsideF48d_Ψ ω s := by
  simp only [burnsideF48d_Ψ, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]

theorem burnsideF48d_Ψ_smul (x : ZMod 3) (r : Fin 154 → ZMod 3) :
    burnsideF48d_Ψ ω (x • r) = burnsideF48d_z K x • burnsideF48d_Ψ ω r := by
  simp only [burnsideF48d_Ψ, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]

theorem burnsideF48d_Ψ_zero : burnsideF48d_Ψ ω (0 : Fin 154 → ZMod 3) = 0 := by
  simp [burnsideF48d_Ψ]

theorem burnsideF48d_Ψ_neg (r : Fin 154 → ZMod 3) :
    burnsideF48d_Ψ ω (-r) = -burnsideF48d_Ψ ω r := by
  unfold burnsideF48d_Ψ
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [show burnsideF48d_z K ((-r) q) = -burnsideF48d_z K (r q) from map_neg _ _, neg_smul]

theorem burnsideF48d_Ψ_sum {ι : Type*} (S : Finset ι) (f : ι → Fin 154 → ZMod 3) :
    burnsideF48d_Ψ ω (∑ i ∈ S, f i) = ∑ i ∈ S, burnsideF48d_Ψ ω (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [burnsideF48d_Ψ_zero]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, burnsideF48d_Ψ_add, ih]

theorem burnsideF48d_map_Ψ (g : Module.End K (RootModule .D4 K)) (r : Fin 154 → ZMod 3) :
    g (burnsideF48d_Ψ ω r) = ∑ q : Fin 154, burnsideF48d_z K (r q) • g (burnsideF48d_b ω q) := by
  simp only [burnsideF48d_Ψ, map_sum, map_smul]

theorem burnsideF48d_Ψ_combW {Y : Array W} (hY : RowsWF (toVM Y)) {r : W} (hr : r.toV.wf = true)
    (g : Module.End K (RootModule .D4 K))
    (hYg : ∀ q : Fin 154, burnsideF48d_Ψ ω (vecOf Y[q.val]!) = g (burnsideF48d_b ω q)) :
    burnsideF48d_Ψ ω (vecOf (combW 154 Y r)) = g (burnsideF48d_Ψ ω (vecOf r)) := by
  rw [vecOf_combW hY hr, burnsideF48d_Ψ_sum, burnsideF48d_map_Ψ]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [burnsideF48d_Ψ_smul, hYg]

theorem burnsideF48d_sum_range_three_mul {M : Type*} [AddCommMonoid M] (F : ℕ → M) (n : ℕ) :
    ∑ q ∈ Finset.range (3 * n), F q = ∑ l ∈ Finset.range n, ∑ j ∈ Finset.range 3, F (3 * l + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 * n + 3 by ring, Finset.sum_range_add, ih,
      Finset.sum_range_succ (fun l => ∑ j ∈ Finset.range 3, F (3 * l + j)) n]

theorem burnsideF48d_Ψ_eq (r : Fin 154 → ZMod 3) :
    burnsideF48d_Ψ ω r = ∑ l ∈ Finset.range 28, ∑ j ∈ Finset.range 3,
      (if h : 3 * l + j < 154 then burnsideF48d_z K (r ⟨3 * l + j, h⟩) else 0) •
        (ω ^ j • burnsideF48d_e K l) := by
  set F : ℕ → RootModule .D4 K := fun q => if h : q < 154 then
    burnsideF48d_z K (r ⟨q, h⟩) • burnsideF48d_b ω q else 0 with hF
  have h1 : burnsideF48d_Ψ ω r = ∑ q ∈ Finset.range 154, F q := by
    rw [burnsideF48d_Ψ, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hF]
    simp only [dif_pos q.isLt]
  have h2 : ∑ q ∈ Finset.range 154, F q = ∑ q ∈ Finset.range (3 * 28), F q := by
    rw [show (154 : ℕ) = 3 * 28 + 70 by norm_num, Finset.sum_range_add]
    rw [Finset.sum_eq_zero (s := Finset.range 70) (fun q _ => by
      rw [hF]
      dsimp only
      split_ifs with h
      · rw [burnsideF48d_b, if_neg (by omega), smul_zero]
      · rfl), add_zero]
  rw [h1, h2, burnsideF48d_sum_range_three_mul]
  refine Finset.sum_congr rfl fun l hl => Finset.sum_congr rfl fun j hj => ?_
  have hl' : l < 28 := Finset.mem_range.1 hl
  have hj' : j < 3 := Finset.mem_range.1 hj
  rw [hF]
  simp only [dif_pos (show 3 * l + j < 154 by omega)]
  rw [burnsideF48d_b, if_pos (by omega), show (3 * l + j) % 3 = j by omega,
    show (3 * l + j) / 3 = l by omega]

theorem burnsideF48d_Ψ_realW (w : Array ℕ) :
    burnsideF48d_Ψ ω (vecOf (burnsideF48d_realW w)) = burnsideF48d_vec ω w := by
  rw [burnsideF48d_Ψ_eq, burnsideF48d_vec]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' : l < 28 := Finset.mem_range.1 hl
  have hv : ∀ (j : ℕ) (hj : j < 3), vecOf (burnsideF48d_realW w) ⟨3 * l + j, by omega⟩ =
      ((w[l]! / 3 ^ j % 3 : ℕ) : ZMod 3) := by
    intro j hj
    obtain ⟨hp, hm⟩ := V.ofFn_lt 154 fun q => if q < 84 then w[q / 3]! / 3 ^ (q % 3) % 3 else 0
    rw [vecOf_apply, Fin.val_mk, burnsideF48d_realW,
      W.toV_ofV (lt_of_lt_of_le hp (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
        (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by norm_num))),
      V.val_ofFn, if_pos (by omega), if_pos (by omega), show (3 * l + j) / 3 = l by omega,
      show (3 * l + j) % 3 = j by omega]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [dif_pos (by omega : 3 * l + 0 < 154), dif_pos (by omega : 3 * l + 1 < 154),
    dif_pos (by omega : 3 * l + 2 < 154)]
  rw [hv 0 (by norm_num), hv 1 (by norm_num), hv 2 (by norm_num)]
  simp only [map_natCast, pow_zero, pow_one, Nat.div_one, one_smul, smul_smul, ← add_smul]
  congr 1

variable (hω : ω ^ 3 = ω + 1)

theorem burnsideF48d_getElem!_map {a : Array ℕ} (ha : a.size = 28) (f : ℕ → ℕ) {l : ℕ}
    (hl : l < 28) : (a.map f)[l]! = f a[l]! := by
  rw [getElem!_pos _ l (by simp [ha, hl]), Array.getElem_map, getElem!_pos a l (by rw [ha]; exact hl)]

include hω in
theorem burnsideF48d_vec_map_mulC {a : Array ℕ} (ha : a.size = 28) (c : ℕ) :
    burnsideF48d_vec ω (a.map (burnsideF48d_mulC c)) =
      burnsideF48d_φ ω c • burnsideF48d_vec ω a := by
  rw [burnsideF48d_vec, burnsideF48d_vec, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [burnsideF48d_getElem!_map ha _ (Finset.mem_range.1 hl), burnsideF48d_φ_mul ω hω, smul_smul]

include hω in
theorem burnsideF48d_Ψ_rowsOf {cols : Array (Array ℕ)} (g : Module.End K (RootModule .D4 K))
    (hcols : ∀ l < 28, (cols[l]!).size = 28 ∧
      burnsideF48d_vec ω cols[l]! = g (burnsideF48d_e K l)) (q : Fin 154) :
    burnsideF48d_Ψ ω (vecOf (burnsideF48d_rowsOf cols)[q.val]!) = g (burnsideF48d_b ω q) := by
  have e : (burnsideF48d_rowsOf cols)[q.val]! = if q.val < 84 then
      burnsideF48d_realW ((cols[q.val / 3]!).map
        (burnsideF48d_mulC (burnsideF48d_powC 3 (q.val % 3)))) else W.zero := by
    rw [burnsideF48d_rowsOf, getElem!_pos _ q.val (by simp), Array.getElem_ofFn]
  rw [e]
  by_cases hq : q.val < 84
  · have hl : q.val / 3 < 28 := by omega
    rw [if_pos hq, burnsideF48d_Ψ_realW, burnsideF48d_b, if_pos hq,
      burnsideF48d_vec_map_mulC ω hω (hcols _ hl).1, (hcols _ hl).2,
      burnsideF48d_φ_pow ω hω, burnsideF48d_φ_three, map_smul]
  · rw [if_neg hq, burnsideF48d_b, if_neg hq, map_zero]
    have : vecOf W.zero = 0 := by
      funext j
      rw [vecOf_apply, W.toV_zero, V.val_zero]
      rfl
    rw [this, burnsideF48d_Ψ_zero]

theorem burnsideF48d_rowsWF (cols : Array (Array ℕ)) :
    RowsWF (toVM (burnsideF48d_rowsOf cols)) := by
  intro j
  have hs : (burnsideF48d_rowsOf cols).size = 154 := by
    rw [burnsideF48d_rowsOf, Array.size_ofFn]
  rw [toVM_getElem!]
  by_cases hj : j < 154
  · rw [burnsideF48d_rowsOf, getElem!_pos _ j (by rw [Array.size_ofFn]; exact hj),
      Array.getElem_ofFn]
    split_ifs
    · obtain ⟨hp, hm⟩ := V.ofFn_lt 154 fun q => if q < 84 then
        ((cols[j / 3]!).map (burnsideF48d_mulC (burnsideF48d_powC 3 (j % 3))))[q / 3]! /
          3 ^ (q % 3) % 3 else 0
      rw [burnsideF48d_realW, W.toV_ofV
        (lt_of_lt_of_le hp (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
        (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by norm_num)))]
      exact V.wf_ofFn _ _
    · rw [W.toV_zero]; exact V.wf_zero
  · rw [getElem!_neg _ j (by rw [hs]; exact hj), W.toV_default]
    exact V.wf_zero

attribute [local irreducible] burnsideF48d_colTab burnsideF48d_genCol in
include hω in
theorem burnsideF48d_Ψ_genRows (k : ℕ) (q : Fin 154) :
    burnsideF48d_Ψ ω (vecOf (burnsideF48d_genRows (burnsideF48d_colTab ()) k)[q.val]!) =
      burnsideF48d_genEnd ω k (burnsideF48d_b ω q) := by
  refine burnsideF48d_Ψ_rowsOf ω hω _ (fun l hl => ?_) q
  rw [getElem!_pos _ l (by rw [Array.size_map, Array.size_range]; exact hl), Array.getElem_map,
    Array.getElem_range]
  exact burnsideF48d_vec_genCol ω hω k hl

end Real

theorem burnsideF48d_root_inj {m m' : ℕ} (hm : m < burnsideF48d_C.roots.length)
    (hm' : m' < burnsideF48d_C.roots.length)
    (h : burnsideF48d_C.root m = burnsideF48d_C.root m') : m = m' := by
  have hn := Tag.rootCertificate_checkNodup Tag.D4
  simp only [RootCertificate.checkNodup, decide_eq_true_eq] at hn
  exact List.inj_on_of_nodup_map hn (List.mem_range.2 hm) (List.mem_range.2 hm')
    (congrArg List.ofFn h)

theorem burnsideF48d_toLabel_injective : Function.Injective (toLabel burnsideF48d_hC) := by
  rintro (j | m) (j' | m') h
  · simpa [toLabel] using h
  · simp [toLabel] at h
  · simp [toLabel] at h
  · simp only [toLabel, Sum.inr.injEq, Subtype.mk.injEq] at h
    exact congrArg Sum.inr (Fin.ext (burnsideF48d_root_inj m.2 m'.2 h))

theorem burnsideF48d_ofIdx_idx : ∀ l < 28, burnsideF48d_ofIdx (burnsideF48d_idx l) = l := by
  decide

theorem burnsideF48d_label_inj {l l' : ℕ} (hl : l < 28) (hl' : l' < 28)
    (h : toLabel burnsideF48d_hC (burnsideF48d_idx l) = toLabel burnsideF48d_hC (burnsideF48d_idx l')) :
    l = l' := by
  have := congrArg burnsideF48d_ofIdx (burnsideF48d_toLabel_injective h)
  rwa [burnsideF48d_ofIdx_idx l hl, burnsideF48d_ofIdx_idx l' hl'] at this

section Inj

variable {K : Type*} [Field K] [CharP K 3] (ω : K)

theorem burnsideF48d_e_apply {l l' : ℕ} (hl : l < 28) (hl' : l' < 28) :
    burnsideF48d_e K l' (toLabel burnsideF48d_hC (burnsideF48d_idx l)) = if l' = l then 1 else 0 := by
  rw [burnsideF48d_e, Finsupp.single_apply]
  by_cases h : l' = l
  · rw [if_pos (by rw [h]), if_pos h]
  · rw [if_neg (fun h' => h (burnsideF48d_label_inj hl' hl h')), if_neg h]

theorem burnsideF48d_Ψ_apply (r : Fin 154 → ZMod 3) {l : ℕ} (hl : l < 28) :
    burnsideF48d_Ψ ω r (toLabel burnsideF48d_hC (burnsideF48d_idx l)) =
      burnsideF48d_z K (r ⟨3 * l, by omega⟩) + burnsideF48d_z K (r ⟨3 * l + 1, by omega⟩) * ω +
        burnsideF48d_z K (r ⟨3 * l + 2, by omega⟩) * ω ^ 2 := by
  rw [burnsideF48d_Ψ_eq, Finsupp.finset_sum_apply,
    Finset.sum_eq_single_of_mem l (Finset.mem_range.2 hl) (fun l' hl' hne => by
      rw [Finsupp.finset_sum_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Finsupp.smul_apply, Finsupp.smul_apply, burnsideF48d_e_apply hl (Finset.mem_range.1 hl'),
        if_neg hne, smul_zero, smul_zero]),
    Finsupp.finset_sum_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Finsupp.smul_apply,
    burnsideF48d_e_apply hl hl, if_true, smul_eq_mul, mul_one, pow_zero, pow_one]
  rw [dif_pos (by omega : 3 * l + 0 < 154), dif_pos (by omega : 3 * l + 1 < 154),
    dif_pos (by omega : 3 * l + 2 < 154)]
  simp only [add_zero, mul_one]

theorem burnsideF48d_z_eq (x : ZMod 3) : burnsideF48d_z K x = (x.val : K) := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

variable (hω : ω ^ 3 = ω + 1)

include hω in
theorem burnsideF48d_Ψ_inj {r s : Fin 154 → ZMod 3} (hr : ∀ q : Fin 154, 84 ≤ q.val → r q = 0)
    (hs : ∀ q : Fin 154, 84 ≤ q.val → s q = 0) (h : burnsideF48d_Ψ ω r = burnsideF48d_Ψ ω s) :
    r = s := by
  funext q
  by_cases hq : 84 ≤ q.val
  · rw [hr q hq, hs q hq]
  have hl : q.val / 3 < 28 := by omega
  set l := q.val / 3 with hldef
  have hcoord := congrArg (fun v => v (toLabel burnsideF48d_hC (burnsideF48d_idx l))) h
  simp only [burnsideF48d_Ψ_apply ω _ hl, burnsideF48d_z_eq] at hcoord
  have hval : ∀ x : ZMod 3, x.val < 3 := fun x => ZMod.val_lt x
  set d0 := (r ⟨3 * l, by omega⟩).val
  set d1 := (r ⟨3 * l + 1, by omega⟩).val
  set d2 := (r ⟨3 * l + 2, by omega⟩).val
  set e0 := (s ⟨3 * l, by omega⟩).val
  set e1 := (s ⟨3 * l + 1, by omega⟩).val
  set e2 := (s ⟨3 * l + 2, by omega⟩).val
  have hd : d0 + 3 * d1 + 9 * d2 = e0 + 3 * e1 + 9 * e2 := by
    have h1 := burnsideF48d_φ_digits ω (hval (r ⟨3 * l, by omega⟩)) (hval (r ⟨3 * l + 1, by omega⟩))
      (hval (r ⟨3 * l + 2, by omega⟩))
    have h2 := burnsideF48d_φ_digits ω (hval (s ⟨3 * l, by omega⟩)) (hval (s ⟨3 * l + 1, by omega⟩))
      (hval (s ⟨3 * l + 2, by omega⟩))
    refine burnsideF48d_φ_injOn ω hω ?_ ?_ (h1.trans (hcoord.trans h2.symm))
    · have := hval (r ⟨3 * l, by omega⟩); have := hval (r ⟨3 * l + 1, by omega⟩)
      have := hval (r ⟨3 * l + 2, by omega⟩); omega
    · have := hval (s ⟨3 * l, by omega⟩); have := hval (s ⟨3 * l + 1, by omega⟩)
      have := hval (s ⟨3 * l + 2, by omega⟩); omega
  have h0 := hval (r ⟨3 * l, by omega⟩); have h1 := hval (r ⟨3 * l + 1, by omega⟩)
  have h2 := hval (r ⟨3 * l + 2, by omega⟩); have h3 := hval (s ⟨3 * l, by omega⟩)
  have h4 := hval (s ⟨3 * l + 1, by omega⟩); have h5 := hval (s ⟨3 * l + 2, by omega⟩)
  have hcases : q.val % 3 = 0 ∨ q.val % 3 = 1 ∨ q.val % 3 = 2 := by omega
  rcases hcases with hm | hm | hm
  · have e : q = ⟨3 * l, by omega⟩ := Fin.ext (by simp only; omega)
    rw [e]
    apply ZMod.val_injective
    show d0 = e0
    omega
  · have e : q = ⟨3 * l + 1, by omega⟩ := Fin.ext (by simp only; omega)
    rw [e]
    apply ZMod.val_injective
    show d1 = e1
    omega
  · have e : q = ⟨3 * l + 2, by omega⟩ := Fin.ext (by simp only; omega)
    rw [e]
    apply ZMod.val_injective
    show d2 = e2
    omega

end Inj

theorem burnsideF48d_testBit_of_shr {x : UInt64} (h : x >>> 20 = 0) {t : ℕ} (ht : 20 ≤ t) :
    x.toNat.testBit t = false := by
  have e := congrArg (fun y : UInt64 => y.toNat.testBit (t - 20)) h
  simp only [UInt64.toNat_shiftRight, Nat.testBit_shiftRight, UInt64.toNat_zero,
    Nat.zero_testBit] at e
  have h20 : (20 : UInt64).toNat % 64 = 20 := by decide
  rwa [h20, show 20 + (t - 20) = t by omega] at e

theorem burnsideF48d_testBit_join_low {x0 x1 x2 x3 : UInt64} (h1 : x1 >>> 20 = 0) (h2 : x2 = 0)
    (h3 : x3 = 0) {t : ℕ} (ht : 84 ≤ t) : (join x0 x1 x2 x3).testBit t = false := by
  rw [testBit_join]
  unfold limb
  by_cases hq : t / 64 = 1
  · rw [if_neg (by omega), if_pos hq]
    exact burnsideF48d_testBit_of_shr h1 (by omega)
  · rw [if_neg (by omega), if_neg hq]
    split_ifs <;> simp [h2, h3]

theorem burnsideF48d_vecOf_high {a : W} (h : burnsideF48d_low84 a = true) (q : Fin 154)
    (hq : 84 ≤ q.val) : vecOf a q = 0 := by
  simp only [burnsideF48d_low84, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hp1, hm1⟩, hp2⟩, hm2⟩, hp3⟩, hm3⟩ := h
  rw [vecOf_apply, V.val_eq_bitVal]
  show bitVal ((join a.p0 a.p1 a.p2 a.p3).testBit q.val) ((join a.m0 a.m1 a.m2 a.m3).testBit q.val) = 0
  rw [burnsideF48d_testBit_join_low hp1 hp2 hp3 hq, burnsideF48d_testBit_join_low hm1 hm2 hm3 hq]
  rfl

end CFSG.ASVolI
