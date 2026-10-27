module

public import CFSG.Quasithin.H13.L32NMat8Inputs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.H13.Mat8Cert

@[expose] def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

theorem b2z_xor (a b : Bool) : b2z (a ^^ b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

theorem b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

theorem b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

@[expose] def vec8 (n : ℕ) : Fin 8 → ZMod 2 := fun i => b2z (n.testBit i)

@[expose] def code8 (v : Fin 8 → ZMod 2) : ℕ :=
  (v 0).val + 2 * (v 1).val + 4 * (v 2).val + 8 * (v 3).val + 16 * (v 4).val +
    32 * (v 5).val + 64 * (v 6).val + 128 * (v 7).val

theorem vec8_code8 (v : Fin 8 → ZMod 2) : vec8 (code8 v) = v := by
  have key : ∀ a b c d e f g h : ZMod 2,
      vec8 (code8 ![a, b, c, d, e, f, g, h]) = ![a, b, c, d, e, f, g, h] := by
    decide
  have hv : v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7] := by
    ext i
    fin_cases i <;> rfl
  rw [hv]
  exact key _ _ _ _ _ _ _ _

theorem code8_lt (v : Fin 8 → ZMod 2) : code8 v < 256 := by
  have h0 := ZMod.val_lt (v 0)
  have h1 := ZMod.val_lt (v 1)
  have h2 := ZMod.val_lt (v 2)
  have h3 := ZMod.val_lt (v 3)
  have h4 := ZMod.val_lt (v 4)
  have h5 := ZMod.val_lt (v 5)
  have h6 := ZMod.val_lt (v 6)
  have h7 := ZMod.val_lt (v 7)
  simp only [code8]
  omega

theorem vec8_inj {m n : ℕ} (hm : m < 256) (hn : n < 256) (h : vec8 m = vec8 n) : m = n := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8
  · exact b2z_inj (congrFun h ⟨i, hi⟩)
  · have h256 : (256 : ℕ) = 2 ^ 8 := by norm_num
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (h256 ▸ hm) (Nat.pow_le_pow_right (by norm_num)
      (by omega))), Nat.testBit_lt_two_pow (lt_of_lt_of_le (h256 ▸ hn) (Nat.pow_le_pow_right
      (by norm_num) (by omega)))]

theorem code8_vec8 {n : ℕ} (hn : n < 256) : code8 (vec8 n) = n :=
  vec8_inj (code8_lt _) hn (vec8_code8 _)

theorem vec8_xor (m n : ℕ) : vec8 (m ^^^ n) = vec8 m + vec8 n := by
  ext i
  simp only [vec8, Nat.testBit_xor, b2z_xor, Pi.add_apply]

theorem vec8_zero : vec8 0 = 0 := by
  ext i
  simp [vec8, b2z]

theorem vec8_ite (c : Bool) (a : ℕ) : vec8 (if c then a else 0) = b2z c • vec8 a := by
  cases c <;> simp [vec8_zero, b2z]

@[expose] def dec8 (A : List ℕ) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun i j => vec8 (A.getD j 0) i

theorem fin_vals8 : ((0 : Fin 8) : ℕ) = 0 ∧ ((1 : Fin 8) : ℕ) = 1 ∧ ((2 : Fin 8) : ℕ) = 2 ∧
    ((3 : Fin 8) : ℕ) = 3 ∧ ((4 : Fin 8) : ℕ) = 4 ∧ ((5 : Fin 8) : ℕ) = 5 ∧
    ((6 : Fin 8) : ℕ) = 6 ∧ ((7 : Fin 8) : ℕ) = 7 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem dec8_mulVec (A : List ℕ) (v : ℕ) : (dec8 A).mulVec (vec8 v) = vec8 (mv8 A v) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ := fin_vals8
  ext i
  simp only [mv8, vec8_xor, vec8_ite, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct, Fin.sum_univ_eight, dec8, Matrix.of_apply]
  simp only [vec8, bt, f0, f1, f2, f3, f4, f5, f6, f7]
  ring

theorem dec8_mul8 (A B : List ℕ) (hB : B.length = 8) : dec8 (mul8 A B) = dec8 A * dec8 B := by
  ext i j
  have hj : (j : ℕ) < B.length := by rw [hB]; exact j.isLt
  have hget : (mul8 A B).getD j 0 = mv8 A (B.getD j 0) := by
    simp only [mul8, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
      Option.map_some, Option.getD_some]
  simp only [dec8, Matrix.of_apply, Matrix.mul_apply]
  rw [hget, ← dec8_mulVec]
  simp only [Matrix.mulVec, dotProduct, dec8, Matrix.of_apply]

theorem dec8_one8 : dec8 one8 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

@[expose] def Valid8 (A : List ℕ) : Prop := A.length = 8 ∧ ∀ c ∈ A, c < 256

theorem getD_lt_of_valid8 {A : List ℕ} (hA : Valid8 A) (j : ℕ) : A.getD j 0 < 256 := by
  by_cases hj : j < A.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact hA.2 _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    norm_num

theorem dec8_injOn {A A' : List ℕ} (hA : Valid8 A) (hA' : Valid8 A')
    (h : dec8 A = dec8 A') : A = A' := by
  apply List.ext_getElem (hA.1.trans hA'.1.symm)
  intro j hj hj'
  have hj8 : j < 8 := hA.1 ▸ hj
  have hcol : vec8 (A.getD j 0) = vec8 (A'.getD j 0) := by
    ext i
    have := congrFun (congrFun h i) ⟨j, hj8⟩
    simpa [dec8] using this
  have h1 := vec8_inj (getD_lt_of_valid8 hA j) (getD_lt_of_valid8 hA' j) hcol
  rwa [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj'] at h1

@[expose] def colsOf (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) : List ℕ :=
  List.ofFn fun j => code8 fun i => M i j

theorem valid8_colsOf (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) : Valid8 (colsOf M) := by
  refine ⟨List.length_ofFn, fun c hc => ?_⟩
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
  exact code8_lt _

theorem dec8_colsOf (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) : dec8 (colsOf M) = M := by
  ext i j
  simp only [dec8, colsOf, Matrix.of_apply]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  exact congrFun (vec8_code8 _) i

theorem colsOf_dec8 {A : List ℕ} (hA : Valid8 A) : colsOf (dec8 A) = A :=
  dec8_injOn (valid8_colsOf _) hA (dec8_colsOf _)

theorem colsOf_eq_iff {M : Matrix (Fin 8) (Fin 8) (ZMod 2)} {A : List ℕ} (hA : Valid8 A) :
    colsOf M = A ↔ dec8 A = M := by
  constructor
  · rintro rfl; exact dec8_colsOf M
  · rintro rfl; exact colsOf_dec8 hA

theorem length_mul8 (A B : List ℕ) : (mul8 A B).length = B.length := List.length_map _

theorem mv8_lt {A : List ℕ} (hA : Valid8 A) (v : ℕ) : mv8 A v < 256 := by
  have key : ∀ a b : ℕ, a < 256 → b < 256 → a ^^^ b < 256 := fun a b ha hb => by
    have h256 : (256 : ℕ) = 2 ^ 8 := by norm_num
    rw [h256] at ha hb ⊢
    exact Nat.xor_lt_two_pow ha hb
  have hite : ∀ (c : Bool) (j : ℕ), (if c then A.getD j 0 else 0) < 256 := fun c j => by
    split
    · exact getD_lt_of_valid8 hA j
    · norm_num
  simp only [mv8]
  exact key _ _ (key _ _ (key _ _ (key _ _ (key _ _ (key _ _ (key _ _ (hite _ _) (hite _ _))
    (hite _ _)) (hite _ _)) (hite _ _)) (hite _ _)) (hite _ _)) (hite _ _)

theorem valid8_mul8 {A B : List ℕ} (hA : Valid8 A) (hB : Valid8 B) : Valid8 (mul8 A B) := by
  refine ⟨(length_mul8 A B).trans hB.1, fun c hc => ?_⟩
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hc
  exact mv8_lt hA v

theorem colsOf_mul (M N : Matrix (Fin 8) (Fin 8) (ZMod 2)) :
    colsOf (M * N) = mul8 (colsOf M) (colsOf N) := by
  refine dec8_injOn (valid8_colsOf _) (valid8_mul8 (valid8_colsOf _) (valid8_colsOf _)) ?_
  rw [dec8_colsOf, dec8_mul8 _ _ (valid8_colsOf N).1, dec8_colsOf, dec8_colsOf]

theorem colsOf_one : colsOf 1 = one8 := by
  rw [colsOf_eq_iff (by refine ⟨rfl, ?_⟩; decide), dec8_one8]

theorem mulVec_vec8 (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) (v : ℕ) :
    M.mulVec (vec8 v) = vec8 (mv8 (colsOf M) v) := by
  rw [← dec8_mulVec, dec8_colsOf]

theorem length_evalW (gens : List (List ℕ)) (w : List ℕ) : (evalW gens w).length = 8 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    show (mul8 (gens.getD i one8) (evalW gens w)).length = 8
    rw [length_mul8, ih]

theorem evalW_cons (gens : List (List ℕ)) (i : ℕ) (w : List ℕ) :
    evalW gens (i :: w) = mul8 (gens.getD i one8) (evalW gens w) := rfl

theorem valid8_one8 : Valid8 one8 := ⟨rfl, by decide⟩

theorem valid8_evalW (gens : List (List ℕ)) (hgens : ∀ g ∈ gens, Valid8 g) (w : List ℕ) :
    Valid8 (evalW gens w) := by
  induction w with
  | nil => exact valid8_one8
  | cons i w ih =>
    rw [evalW_cons]
    refine valid8_mul8 ?_ ih
    by_cases hi : i < gens.length
    · rw [List.getD_eq_getElem _ _ hi]; exact hgens _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]; exact valid8_one8

@[expose] def genSub (gens : List (List ℕ)) : Subgroup (GL (Fin 8) (ZMod 2)) :=
  Subgroup.closure {g | colsOf (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ gens}

theorem exists_evalW (gens : List (List ℕ)) (hgens : ∀ g ∈ gens, Valid8 g)
    (hunit : ∀ g ∈ gens, ∃ u : GL (Fin 8) (ZMod 2), (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g)
    (w : List ℕ) :
    ∃ u ∈ genSub gens, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 (evalW gens w) := by
  induction w with
  | nil => exact ⟨1, one_mem _, by rw [Units.val_one]; exact dec8_one8.symm⟩
  | cons i w ih =>
    obtain ⟨u, hu, hu'⟩ := ih
    rw [evalW_cons, dec8_mul8 _ _ (length_evalW gens w), ← hu']
    by_cases hi : i < gens.length
    · rw [List.getD_eq_getElem _ _ hi]
      obtain ⟨v, hv⟩ := hunit _ (List.getElem_mem hi)
      refine ⟨v * u, mul_mem (Subgroup.subset_closure ?_) hu, by rw [Units.val_mul, hv]⟩
      show colsOf (v : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ gens
      rw [hv, colsOf_dec8 (hgens _ (List.getElem_mem hi))]
      exact List.getElem_mem hi
    · rw [List.getD_eq_default _ _ (by omega), dec8_one8, one_mul]
      exact ⟨u, hu, rfl⟩

theorem mem_genSub_iff (gens L : List (List ℕ)) (hgens : ∀ g ∈ gens, Valid8 g)
    (hunit : ∀ g ∈ gens, ∃ u : GL (Fin 8) (ZMod 2), (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g)
    (hL : ∀ x ∈ L, ∃ w, x = evalW gens w) (hone : one8 ∈ L)
    (hclosed : ∀ x ∈ L, ∀ g ∈ gens, mul8 g x ∈ L) (u : GL (Fin 8) (ZMod 2)) :
    u ∈ genSub gens ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ L := by
  constructor
  · intro hu
    have hstep : ∀ s : GL (Fin 8) (ZMod 2),
        colsOf (s : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ gens →
        ∀ y : GL (Fin 8) (ZMod 2), colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ L →
        colsOf ((s * y : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ L := by
      intro s hs y hy
      rw [Units.val_mul, colsOf_mul]
      exact hclosed _ hy _ hs
    have hpow : ∀ s : GL (Fin 8) (ZMod 2),
        colsOf (s : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ gens → ∀ (m : ℕ)
        (y : GL (Fin 8) (ZMod 2)), colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ L →
        colsOf ((s ^ m * y : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ L := by
      intro s hs m
      induction m with
      | zero => intro y hy; rwa [pow_zero, one_mul]
      | succ m ih =>
        intro y hy
        rw [pow_succ', mul_assoc]
        exact hstep s hs _ (ih y hy)
    unfold genSub at hu
    refine Subgroup.closure_induction_left (p := fun (u : GL (Fin 8) (ZMod 2)) _ =>
      colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ L) ?_ ?_ ?_ hu
    · rw [Units.val_one, colsOf_one]; exact hone
    · intro s hs y _ hy
      exact hstep s hs y hy
    · intro s hs y _ hy
      have hfin : IsOfFinOrder s := isOfFinOrder_of_finite s
      have hinv : s⁻¹ = s ^ (orderOf s - 1) := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ,
          Nat.sub_add_cancel (orderOf_pos_iff.mpr hfin), pow_orderOf_eq_one]
      rw [hinv]
      exact hpow s hs _ y hy
  · intro hu
    obtain ⟨w, hw⟩ := hL _ hu
    obtain ⟨v, hv, hv'⟩ := exists_evalW gens hgens hunit w
    have : u = v := by
      apply Units.ext
      rw [hv', ← hw, dec8_colsOf]
    exact this ▸ hv

theorem card_genSub (gens L : List (List ℕ)) (hgens : ∀ g ∈ gens, Valid8 g)
    (hunit : ∀ g ∈ gens, ∃ u : GL (Fin 8) (ZMod 2), (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g)
    (hL : ∀ x ∈ L, ∃ w, x = evalW gens w) (hvalid : ∀ x ∈ L, Valid8 x) (hone : one8 ∈ L)
    (hclosed : ∀ x ∈ L, ∀ g ∈ gens, mul8 g x ∈ L) (hnd : L.Nodup) :
    Nat.card (genSub gens) = L.length := by
  have hmem := mem_genSub_iff gens L hgens hunit hL hone hclosed
  let f : genSub gens → {x // x ∈ L} := fun u =>
    ⟨colsOf ((u : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)), (hmem u).mp u.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun u v h => ?_, fun ⟨x, hx⟩ => ?_⟩
    · have h' := congrArg Subtype.val h
      apply Subtype.ext
      apply Units.ext
      rw [← dec8_colsOf (u : GL (Fin 8) (ZMod 2)).val, ← dec8_colsOf (v : GL (Fin 8) (ZMod 2)).val]
      exact congrArg dec8 h'
    · obtain ⟨w, hw⟩ := hL _ hx
      obtain ⟨v, hv, hv'⟩ := exists_evalW gens hgens hunit w
      refine ⟨⟨v, hv⟩, Subtype.ext ?_⟩
      show colsOf ((v : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) = x
      rw [hv', ← hw, colsOf_dec8 (hvalid x hx)]
  rw [Nat.card_eq_of_bijective f hf,
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (List.mem_toFinset (l := L) (a := x)).symm),
    Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd]

@[expose] def q4V (v : Fin 8 → ZMod 2) : ZMod 2 := v 0 * v 4 + v 1 * v 5 + v 2 * v 6 + v 3 * v 7

theorem q4N_spec (v : ℕ) : b2z (q4N v) = q4V (vec8 v) := by
  simp only [q4N, q4V, vec8, b2z_xor, b2z_and]
  rfl

@[expose] def b4V (v w : Fin 8 → ZMod 2) : ZMod 2 := q4V (v + w) + q4V v + q4V w

theorem b4N_spec (v w : ℕ) : b2z (b4N v w) = b4V (vec8 v) (vec8 w) := by
  simp only [b4N, b2z_xor, q4N_spec, vec8_xor, b4V]

theorem spanN_mem (vs : List ℕ) (W : Submodule (ZMod 2) (Fin 8 → ZMod 2))
    (hW : ∀ v ∈ vs, vec8 v ∈ W) : ∀ c ∈ spanN vs, vec8 c ∈ W := by
  unfold spanN
  suffices key : ∀ (vs' : List ℕ) (S : List ℕ), (∀ v ∈ vs', vec8 v ∈ W) →
      (∀ c ∈ S, vec8 c ∈ W) → ∀ c ∈ vs'.foldl
        (fun S v => if S.contains v then S else S ++ S.map (· ^^^ v)) S, vec8 c ∈ W by
    refine key vs [0] hW ?_
    intro c hc
    rw [List.mem_singleton.mp hc, vec8_zero]
    exact W.zero_mem
  intro vs'
  induction vs' with
  | nil => intro S _ hS; exact hS
  | cons v vs' ih =>
    intro S hv hS
    rw [List.foldl_cons]
    refine ih _ (fun w hw => hv w (List.mem_cons_of_mem _ hw)) ?_
    split
    · exact hS
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hS c hc
      · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
        rw [vec8_xor]
        exact W.add_mem (hS c' hc') (hv v List.mem_cons_self)

end CFSG.Quasithin.H13.Mat8Cert
