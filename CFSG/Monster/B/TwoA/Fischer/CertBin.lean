module

public import CFSG.Monster.B.Dyadic.BinElim
public import Certificates.Data.CFSGNative.MonsterB.BinaryRank

public section

namespace CFSG.Monster.B.TwoA.Fischer.Cert

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Binary
  CFSG.Monster.B.Binary.Native
open scoped Matrix

theorem toVecD_eq_zero_iff {d x : ℕ} (hx : x < 2 ^ d) : toVecD d x = 0 ↔ x = 0 := by
  constructor
  · intro h
    exact toVecD_injective hx (Nat.two_pow_pos d) (h.trans (toVecD_zero d).symm)
  · rintro rfl
    exact toVecD_zero d

theorem toVecD_one_shiftLeft (d : ℕ) (i : Fin d) : toVecD d (1 <<< (i : ℕ)) = Pi.single i 1 := by
  funext j
  rw [toVecD_apply, Nat.one_shiftLeft, Nat.testBit_two_pow, Pi.single_apply]
  by_cases h : j = i
  · subst h
    simp
  · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e.symm)
    simp [h, h']

theorem ite_xor_zmod (X C : Bool) :
    ((if X = true then (1 : ZMod 2) else 0) + if C = true then 1 else 0) =
      if (X ^^ C) = true then 1 else 0 := by
  cases X <;> cases C <;> decide

theorem ite_and_zmod (a b : Bool) :
    ((if a = true then (1 : ZMod 2) else 0) * if b = true then 1 else 0) =
      if (a && b) = true then 1 else 0 := by
  cases a <;> cases b <;> decide

@[expose] def dotBit (d a b : ℕ) : Bool :=
  (List.range d).foldl (fun acc j => acc ^^ (a.testBit j && b.testBit j)) false

theorem dotBit_succ (d a b : ℕ) :
    dotBit (d + 1) a b = (dotBit d a b ^^ (a.testBit d && b.testBit d)) := by
  rw [dotBit, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← dotBit]

theorem toVecD_dotProduct : ∀ (d a b : ℕ),
    toVecD d a ⬝ᵥ toVecD d b = if dotBit d a b then 1 else 0
  | 0, a, b => by simp [dotBit, dotProduct]
  | d + 1, a, b => by
    rw [dotProduct, Fin.sum_univ_castSucc]
    have ih := toVecD_dotProduct d a b
    rw [dotProduct] at ih
    simp only [toVecD_apply, Fin.val_castSucc, Fin.val_last] at ih ⊢
    rw [ih, dotBit_succ, ite_and_zmod, ite_xor_zmod]

@[expose] def strictSorted : List ℕ → Bool
  | a :: b :: l => decide (a < b) && strictSorted (b :: l)
  | _ => true

theorem pairwise_of_strictSorted : ∀ {l : List ℕ}, strictSorted l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    rw [strictSorted, Bool.and_eq_true, decide_eq_true_iff] at h
    have ih := pairwise_of_strictSorted h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact lt_trans h.1 (List.rel_of_pairwise_cons ih hc)

theorem nodup_of_strictSorted {l : List ℕ} (h : strictSorted l = true) : l.Nodup :=
  (pairwise_of_strictSorted h).nodup

theorem sum_map_range (f : ℕ → ℕ) :
    ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => rfl
  | n + 1 => by rw [List.sum_range_succ, Finset.sum_range_succ, sum_map_range f n]

theorem card_filter_tableRank (d : ℕ) (T : Array ℕ) :
    (Finset.univ.filter fun p : Fin d => T[(p : ℕ)]! ≠ 0).card = tableRank d T := by
  rw [tableRank, sum_map_range, Finset.card_filter,
    Fin.sum_univ_eq_sum_range (fun p => if T[p]! ≠ 0 then 1 else 0) d]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : T[p]! = 0 <;> simp [hp]

@[expose] def spanRankIs (d : ℕ) (vs : List ℕ) (r : ℕ) : Bool :=
  allBelow d vs && rankOpt d r (elimTable d vs)

theorem allBelow_iff {d : ℕ} {vs : List ℕ} : allBelow d vs = true ↔ ∀ v ∈ vs, v < 2 ^ d := by
  rw [allBelow, allBelowB, List.all_eq_true]
  exact forall₂_congr fun _ _ => decide_eq_true_iff

theorem spanRankIs_spec {d : ℕ} {vs : List ℕ} {r : ℕ} (h : spanRankIs d vs r = true) :
    (∀ v ∈ vs, v < 2 ^ d) ∧ ∃ T, elimTable d vs = some T ∧ tableRank d T = r := by
  rw [spanRankIs, Bool.and_eq_true, allBelow_iff] at h
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  cases hT : elimTable d vs with
  | none =>
    rw [hT] at h2
    exact absurd h2 Bool.false_ne_true
  | some T =>
    rw [hT] at h2
    simp only [rankOpt, Bool.and_eq_true, beq_iff_eq] at h2
    exact ⟨T, rfl, h2.2⟩

theorem finrank_listSpan {d : ℕ} {vs : List ℕ} {r : ℕ} (h : spanRankIs d vs r = true) :
    Module.finrank (ZMod 2) (listSpan d vs) = r := by
  obtain ⟨hvs, T, hT, hr⟩ := spanRankIs_spec h
  obtain ⟨hinv, -⟩ := elimTable_spec hvs hT
  rw [← entrySpan_elimTable hvs hT, finrank_entrySpan hinv.entry, card_filter_tableRank, hr]

theorem mem_listSpan {d : ℕ} {vs : List ℕ} {v : ℕ} (hv : v ∈ vs) : toVecD d v ∈ listSpan d vs :=
  Submodule.subset_span ⟨v, hv, rfl⟩

theorem dotProduct_listSpan {d : ℕ} {vs : List ℕ} {y : Fin d → ZMod 2}
    (h : ∀ v ∈ vs, toVecD d v ⬝ᵥ y = 0) : ∀ w ∈ listSpan d vs, w ⬝ᵥ y = 0 := by
  intro w hw
  refine Submodule.span_induction (p := fun w _ => w ⬝ᵥ y = 0) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨v, hv, rfl⟩
    exact h v hv
  · exact zero_dotProduct y
  · intro a b _ _ ha hb
    rw [add_dotProduct, ha, hb, add_zero]
  · intro c a _ ha
    rw [smul_dotProduct, ha, smul_zero]

@[expose] def freeIs (d : ℕ) (vs Q : List ℕ) : Bool :=
  allBelow d vs &&
    match elimTable d vs with
    | some T => (List.range d).all fun p => (T[p]! == 0) == Q.contains p
    | none => false

theorem freeIs_spec {d : ℕ} {vs Q : List ℕ} (h : freeIs d vs Q = true) :
    (∀ v ∈ vs, v < 2 ^ d) ∧ ∃ T, elimTable d vs = some T ∧ ∀ p < d, (T[p]! = 0 ↔ p ∈ Q) := by
  rw [freeIs, Bool.and_eq_true, allBelow_iff] at h
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  cases hT : elimTable d vs with
  | none =>
    rw [hT] at h2
    exact absurd h2 Bool.false_ne_true
  | some T =>
    rw [hT] at h2
    simp only [List.all_eq_true, List.mem_range] at h2
    refine ⟨T, rfl, fun p hp => ?_⟩
    have e : (T[p]! == 0) = Q.contains p := beq_iff_eq.1 (h2 p hp)
    rw [← List.contains_iff_mem, ← e, beq_iff_eq]

theorem eq_sum_of_table {d : ℕ} {rs : List ℕ} {T : Array ℕ} (hrs : ∀ r ∈ rs, r < 2 ^ d)
    (hT : elimTable d rs = some T) (u : Fin d → Fin d → ZMod 2)
    (hu : ∀ p : Fin d, T[(p : ℕ)]! = 0 → (∀ r ∈ rs, toVecD d r ⬝ᵥ u p = 0) ∧
      ∀ p' : Fin d, T[(p' : ℕ)]! = 0 → u p p' = if p' = p then 1 else 0)
    {v : Fin d → ZMod 2} (hv : ∀ r ∈ rs, toVecD d r ⬝ᵥ v = 0) :
    v = ∑ p : Fin d, if T[(p : ℕ)]! = 0 then v p • u p else 0 := by
  obtain ⟨hinv, -⟩ := elimTable_spec hrs hT
  have hworth : ∀ r ∈ rs,
      toVecD d r ⬝ᵥ (∑ p : Fin d, if T[(p : ℕ)]! = 0 then v p • u p else 0) = 0 := by
    intro r hr
    rw [dotProduct_sum]
    refine Finset.sum_eq_zero fun p _ => ?_
    by_cases hp : T[(p : ℕ)]! = 0
    · rw [ite_eq_left hp, dotProduct_smul, (hu p hp).1 r hr, smul_zero]
    · rw [ite_eq_right hp]
      exact dotProduct_zero _
  have hent : ∀ y : Fin d → ZMod 2, (∀ r ∈ rs, toVecD d r ⬝ᵥ y = 0) →
      ∀ p : Fin d, T[(p : ℕ)]! ≠ 0 → y ⬝ᵥ toVecD d T[(p : ℕ)]! = 0 := by
    intro y hy p _
    rw [dotProduct_comm]
    exact dotProduct_listSpan hy _ (hinv.mem p p.2)
  refine orth_unique hinv.entry (hent v hv) (hent _ hworth) fun p hp => ?_
  have hwp : (∑ p' : Fin d, if T[(p' : ℕ)]! = 0 then v p' • u p' else 0) p =
      ∑ p' : Fin d, if T[(p' : ℕ)]! = 0 then v p' * u p' p else 0 := by
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun p' _ => ?_
    by_cases hp' : T[(p' : ℕ)]! = 0
    · rw [ite_eq_left hp', ite_eq_left hp', Pi.smul_apply, smul_eq_mul]
    · rw [ite_eq_right hp', ite_eq_right hp', Pi.zero_apply]
  rw [hwp, Finset.sum_eq_single p]
  · rw [ite_eq_left hp, (hu p hp).2 p hp, ite_eq_left rfl, mul_one]
  · intro b _ hb
    by_cases hb' : T[(b : ℕ)]! = 0
    · rw [ite_eq_left hb', (hu b hb').2 p hp, ite_eq_right (Ne.symm hb), mul_zero]
    · exact ite_eq_right hb'
  · intro h
    exact absurd (Finset.mem_univ p) h

theorem rank_eq_finrank_listSpan {m : Type*} [Fintype m] {d : ℕ}
    (A : Matrix m (Fin d) (ZMod 2)) (vs : List ℕ)
    (h : Set.range A.row = {w | ∃ v ∈ vs, toVecD d v = w}) :
    A.rank = Module.finrank (ZMod 2) (listSpan d vs) := by
  rw [Matrix.rank_eq_finrank_span_row, h]
  rfl

@[expose] def stackSubOne {ι : Type*} {d : ℕ} (M : ι → Matrix (Fin d) (Fin d) (ZMod 2)) :
    Matrix (ι × Fin d) (Fin d) (ZMod 2) :=
  Matrix.of fun p => (M p.1 - 1) p.2

theorem mem_ker_stackSubOne {ι : Type*} [Fintype ι] {d : ℕ}
    (M : ι → Matrix (Fin d) (Fin d) (ZMod 2)) (v : Fin d → ZMod 2) :
    v ∈ LinearMap.ker (stackSubOne M).mulVecLin ↔ ∀ k, M k *ᵥ v = v := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro h k
    have hk : (M k - 1) *ᵥ v = 0 := funext fun i => congrFun h (k, i)
    rwa [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hk
  · intro h
    funext p
    have hk : (M p.1 - 1) *ᵥ v = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, h p.1, sub_self]
    exact congrFun hk p.2

theorem transpose_sub_one_row (d : ℕ) (C : Array ℕ) (i : Fin d) :
    ((rowsMatrix d C)ᵀ - 1) i = toVecD d ((transposeRows d C)[(i : ℕ)]! ^^^ (1 <<< (i : ℕ))) := by
  rw [← rowsMatrix_transposeRows, toVecD_xor, toVecD_one_shiftLeft]
  funext j
  have hi : (i : ℕ) < (transposeRows d C).size := by
    rw [transposeRows, Array.size_ofFn]
    exact i.2
  rw [Matrix.sub_apply, Matrix.one_apply, rowsMatrix_apply, Pi.add_apply,
    getElem?_pos (transposeRows d C) (i : ℕ) hi, Option.getD_some,
    getElem!_pos (transposeRows d C) (i : ℕ) hi, Pi.single_apply, sub_eq_add_neg,
    ZMod.neg_eq_self_mod_two]
  by_cases h : j = i
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem transpose_mulVec (d : ℕ) (C : Array ℕ) (v : ℕ) :
    (rowsMatrix d C)ᵀ *ᵥ toVecD d v = toVecD d (vecMulN d C v) := by
  rw [Matrix.mulVec_transpose, toVecD_vecMulN]

theorem range_rowsMatrix {d : ℕ} {X : Array ℕ} (hX : X.size = d) :
    Set.range (rowsMatrix d X).row = {w | ∃ v ∈ X.toList, toVecD d v = w} := by
  ext w
  constructor
  · rintro ⟨i, rfl⟩
    have hi : (i : ℕ) < X.size := hX ▸ i.2
    refine ⟨X[(i : ℕ)], Array.mem_toList_iff.2 (Array.getElem_mem hi), ?_⟩
    funext j
    rw [Matrix.row_apply, rowsMatrix_apply, getElem?_pos X (i : ℕ) hi, Option.getD_some]
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.1 hv)
    refine ⟨⟨i, hX ▸ hi⟩, ?_⟩
    funext j
    rw [Matrix.row_apply, rowsMatrix_apply]
    simp only [getElem?_pos X i hi, Option.getD_some]

theorem rank_transpose_rowsMatrix {d : ℕ} {X : Array ℕ} (hX : X.size = d) :
    ((rowsMatrix d X)ᵀ).rank = Module.finrank (ZMod 2) (listSpan d X.toList) := by
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.col_transpose, range_rowsMatrix hX]
  rfl

theorem toVecD_of_lt {d k m : ℕ} (hm : m < 2 ^ k) (j : Fin d) (hj : k ≤ (j : ℕ)) :
    toVecD d m j = 0 := by
  rw [toVecD_apply, Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right
    (by norm_num) hj))]
  rfl

theorem exists_toVecD_iff {d k : ℕ} (v : Fin d → ZMod 2) :
    (∀ j : Fin d, k ≤ (j : ℕ) → v j = 0) ↔ ∃ m < 2 ^ k, v = toVecD d m := by
  constructor
  · intro hv
    refine ⟨ofBits k fun j => if h : j < d then v ⟨j, h⟩ == 1 else false, ?_, ?_⟩
    · exact ofBits_lt k _
    · funext j
      rw [toVecD_apply, ofBits_testBit]
      by_cases hj : (j : ℕ) < k
      · simp only [hj, decide_true, Bool.true_and, j.2, dite_true]
        rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (v j) with h | h <;> simp [h]
      · simp only [hj, decide_false, Bool.false_and]
        exact hv j (by omega)
  · rintro ⟨m, hm, rfl⟩ j hj
    exact toVecD_of_lt hm j hj

end CFSG.Monster.B.TwoA.Fischer.Cert
