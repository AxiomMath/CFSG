module

public import CFSG.RankThree.Native.ONTripleModel
public import CFSG.RankThree.Native.ONTripleCollapseA
public import CFSG.RankThree.Native.ONTripleCollapseB
public import CFSG.Certificates.PerfectCoverBound

public noncomputable section

namespace CFSG.RankThree.Native.ONTriple

open CFSG.CosetTable CFSG.Sporadic.Bridge TauCeti
open scoped commutatorElement

attribute [local irreducible] dotProduct

variable {G : Type*} [Group G]

theorem pow_mod_three_of_cube {g : G} (hg : g ^ 3 = 1) (n : ℕ) : g ^ (n % 3) = g ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hg, one_pow, one_mul]

theorem eq_one_of_sq_of_cube {ζ : G} (h3 : ζ ^ 3 = 1) (h2 : ζ ^ 2 = 1) : ζ = 1 := by
  calc ζ = ζ ^ 3 * (ζ ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; group

theorem coxeter_exact {u v ζ : G} (hu : u ^ 2 = 1) (hv : v ^ 2 = 1)
    (hζ : ζ ∈ Subgroup.center G) (h3 : ζ ^ 3 = 1) {m : ℕ} (h : (u * v) ^ m = ζ) : ζ = 1 := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hu)
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hv)
  have hc : u * (u * v) * u⁻¹ = (u * v)⁻¹ := by
    rw [mul_inv_rev, hui, hvi, ← mul_assoc, ← sq, hu, one_mul]
  have h1 : u * ζ * u⁻¹ = ζ⁻¹ := by
    rw [← h, ← conj_pow, hc, inv_pow]
  have h2 : u * ζ * u⁻¹ = ζ := by
    rw [Subgroup.mem_center_iff.1 hζ u, mul_assoc, mul_inv_cancel, mul_one]
  apply eq_one_of_sq_of_cube h3
  rw [sq]
  nth_rewrite 2 [← h2]
  rw [h1, mul_inv_cancel]

theorem center_sq_mul {x ζ : G} (hζ : ζ ∈ Subgroup.center G) : (x * ζ) ^ 2 = x ^ 2 * ζ ^ 2 := by
  have hc := Subgroup.mem_center_iff.1 hζ x
  rw [sq, sq, sq, mul_assoc, ← mul_assoc ζ x, ← hc, mul_assoc, mul_assoc]

abbrev onRels : List (List (ℕ × Bool)) := CFSG.Sporadic.Bridge.ONGPL.Native.rels

theorem onRels_length : onRels.length = 29 := by decide

theorem onRels_getD_mem {i : ℕ} (hi : i < 29) : onRels.getD i [] ∈ onRels := by
  rw [List.getD_eq_getElem _ _ (by rw [onRels_length]; exact hi)]
  exact List.getElem_mem _

structure LiftData (X : ℕ → G) (K : Subgroup G) : Prop where
  central : K ≤ Subgroup.center G
  cube : ∀ k ∈ K, k ^ 3 = 1
  inv : ∀ i < 6, X i ^ 2 = 1
  g4 : X 6 ^ 4 = 1
  rel : ∀ v ∈ onRels, wordProd X v ∈ K

namespace LiftData

variable {X : ℕ → G} {K : Subgroup G}

theorem rel_get (hX : LiftData X K) (i : ℕ) (hi : i < 29) : wordProd X (onRels.getD i []) ∈ K :=
  hX.rel _ (onRels_getD_mem hi)

theorem cox (hX : LiftData X K) {u v : G} (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) {i : ℕ} {m : ℕ}
    (hmem : wordProd X (onRels.getD i []) ∈ K) (h : wordProd X (onRels.getD i []) = (u * v) ^ m) :
    wordProd X (onRels.getD i []) = 1 :=
  coxeter_exact hu hv (hX.central hmem) (hX.cube _ hmem) h.symm

theorem inv_eq (hX : LiftData X K) {i : ℕ} (hi : i < 6) : (X i)⁻¹ = X i :=
  inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hX.inv i hi)

end LiftData

theorem wordProd_rel6 (X : ℕ → G) : wordProd X (onRels.getD 6 []) = (X 0 * X 1) ^ 3 := by
  simp [onRels, CFSG.Sporadic.Bridge.ONGPL.Native.rels, wordProd, pow_succ, mul_assoc]

theorem wordProd_rel7 (X : ℕ → G) : wordProd X (onRels.getD 7 []) = (X 1 * X 2) ^ 3 := by
  simp [onRels, CFSG.Sporadic.Bridge.ONGPL.Native.rels, wordProd, pow_succ, mul_assoc]

theorem wordProd_rel8 (X : ℕ → G) : wordProd X (onRels.getD 8 []) = (X 2 * X 3) ^ 8 := by
  simp [onRels, CFSG.Sporadic.Bridge.ONGPL.Native.rels, wordProd, pow_succ, mul_assoc]

theorem wordProd_rel9 (X : ℕ → G) : wordProd X (onRels.getD 9 []) = (X 3 * X 4) ^ 3 := by
  simp [onRels, CFSG.Sporadic.Bridge.ONGPL.Native.rels, wordProd, pow_succ, mul_assoc]

theorem wordProd_rel10 (X : ℕ → G) : wordProd X (onRels.getD 10 []) = (X 4 * X 5) ^ 3 := by
  simp [onRels, CFSG.Sporadic.Bridge.ONGPL.Native.rels, wordProd, pow_succ, mul_assoc]

theorem wordProd_rel11 (X : ℕ → G) : wordProd X (onRels.getD 11 []) = (X 0 * X 2) ^ 2 := by
  simp [onRels, CFSG.Sporadic.Bridge.ONGPL.Native.rels, wordProd, pow_succ, mul_assoc]

theorem wordProd_rel12 (X : ℕ → G) : wordProd X (onRels.getD 12 []) = (X 0 * X 3) ^ 2 := by
  simp [onRels, CFSG.Sporadic.Bridge.ONGPL.Native.rels, wordProd, pow_succ, mul_assoc]

theorem wordProd_rel13 (X : ℕ → G) : wordProd X (onRels.getD 13 []) = (X 0 * X 4) ^ 2 := by
  simp [onRels, CFSG.Sporadic.Bridge.ONGPL.Native.rels, wordProd, pow_succ, mul_assoc]

theorem wordProd_rel14 (X : ℕ → G) : wordProd X (onRels.getD 14 []) = (X 0 * X 5) ^ 2 := by
  simp [onRels, CFSG.Sporadic.Bridge.ONGPL.Native.rels, wordProd, pow_succ, mul_assoc]

theorem wordProd_rel15 (X : ℕ → G) : wordProd X (onRels.getD 15 []) = (X 1 * X 3) ^ 2 := by
  simp [onRels, CFSG.Sporadic.Bridge.ONGPL.Native.rels, wordProd, pow_succ, mul_assoc]

theorem wordProd_rel16 (X : ℕ → G) : wordProd X (onRels.getD 16 []) = (X 1 * X 4) ^ 2 := by
  simp [onRels, CFSG.Sporadic.Bridge.ONGPL.Native.rels, wordProd, pow_succ, mul_assoc]

theorem wordProd_rel17 (X : ℕ → G) : wordProd X (onRels.getD 17 []) = (X 1 * X 5) ^ 2 := by
  simp [onRels, CFSG.Sporadic.Bridge.ONGPL.Native.rels, wordProd, pow_succ, mul_assoc]

theorem wordProd_rel18 (X : ℕ → G) : wordProd X (onRels.getD 18 []) = (X 2 * X 4) ^ 2 := by
  simp [onRels, CFSG.Sporadic.Bridge.ONGPL.Native.rels, wordProd, pow_succ, mul_assoc]

theorem wordProd_rel19 (X : ℕ → G) : wordProd X (onRels.getD 19 []) = (X 2 * X 5) ^ 2 := by
  simp [onRels, CFSG.Sporadic.Bridge.ONGPL.Native.rels, wordProd, pow_succ, mul_assoc]

theorem wordProd_rel20 (X : ℕ → G) : wordProd X (onRels.getD 20 []) = (X 3 * X 5) ^ 2 := by
  simp [onRels, CFSG.Sporadic.Bridge.ONGPL.Native.rels, wordProd, pow_succ, mul_assoc]

namespace LiftData

variable {X : ℕ → G} {K : Subgroup G}

theorem exact6 (hX : LiftData X K) : wordProd X (onRels.getD 6 []) = 1 :=
  hX.cox (hX.inv 0 (by norm_num)) (hX.inv 1 (by norm_num)) (hX.rel_get 6 (by norm_num))
    (wordProd_rel6 X)

theorem exact7 (hX : LiftData X K) : wordProd X (onRels.getD 7 []) = 1 :=
  hX.cox (hX.inv 1 (by norm_num)) (hX.inv 2 (by norm_num)) (hX.rel_get 7 (by norm_num))
    (wordProd_rel7 X)

theorem exact8 (hX : LiftData X K) : wordProd X (onRels.getD 8 []) = 1 :=
  hX.cox (hX.inv 2 (by norm_num)) (hX.inv 3 (by norm_num)) (hX.rel_get 8 (by norm_num))
    (wordProd_rel8 X)

theorem exact9 (hX : LiftData X K) : wordProd X (onRels.getD 9 []) = 1 :=
  hX.cox (hX.inv 3 (by norm_num)) (hX.inv 4 (by norm_num)) (hX.rel_get 9 (by norm_num))
    (wordProd_rel9 X)

theorem exact10 (hX : LiftData X K) : wordProd X (onRels.getD 10 []) = 1 :=
  hX.cox (hX.inv 4 (by norm_num)) (hX.inv 5 (by norm_num)) (hX.rel_get 10 (by norm_num))
    (wordProd_rel10 X)

theorem exact11 (hX : LiftData X K) : wordProd X (onRels.getD 11 []) = 1 :=
  hX.cox (hX.inv 0 (by norm_num)) (hX.inv 2 (by norm_num)) (hX.rel_get 11 (by norm_num))
    (wordProd_rel11 X)

theorem exact12 (hX : LiftData X K) : wordProd X (onRels.getD 12 []) = 1 :=
  hX.cox (hX.inv 0 (by norm_num)) (hX.inv 3 (by norm_num)) (hX.rel_get 12 (by norm_num))
    (wordProd_rel12 X)

theorem exact13 (hX : LiftData X K) : wordProd X (onRels.getD 13 []) = 1 :=
  hX.cox (hX.inv 0 (by norm_num)) (hX.inv 4 (by norm_num)) (hX.rel_get 13 (by norm_num))
    (wordProd_rel13 X)

theorem exact14 (hX : LiftData X K) : wordProd X (onRels.getD 14 []) = 1 :=
  hX.cox (hX.inv 0 (by norm_num)) (hX.inv 5 (by norm_num)) (hX.rel_get 14 (by norm_num))
    (wordProd_rel14 X)

theorem exact15 (hX : LiftData X K) : wordProd X (onRels.getD 15 []) = 1 :=
  hX.cox (hX.inv 1 (by norm_num)) (hX.inv 3 (by norm_num)) (hX.rel_get 15 (by norm_num))
    (wordProd_rel15 X)

theorem exact16 (hX : LiftData X K) : wordProd X (onRels.getD 16 []) = 1 :=
  hX.cox (hX.inv 1 (by norm_num)) (hX.inv 4 (by norm_num)) (hX.rel_get 16 (by norm_num))
    (wordProd_rel16 X)

theorem exact17 (hX : LiftData X K) : wordProd X (onRels.getD 17 []) = 1 :=
  hX.cox (hX.inv 1 (by norm_num)) (hX.inv 5 (by norm_num)) (hX.rel_get 17 (by norm_num))
    (wordProd_rel17 X)

theorem exact18 (hX : LiftData X K) : wordProd X (onRels.getD 18 []) = 1 :=
  hX.cox (hX.inv 2 (by norm_num)) (hX.inv 4 (by norm_num)) (hX.rel_get 18 (by norm_num))
    (wordProd_rel18 X)

theorem exact19 (hX : LiftData X K) : wordProd X (onRels.getD 19 []) = 1 :=
  hX.cox (hX.inv 2 (by norm_num)) (hX.inv 5 (by norm_num)) (hX.rel_get 19 (by norm_num))
    (wordProd_rel19 X)

theorem exact20 (hX : LiftData X K) : wordProd X (onRels.getD 20 []) = 1 :=
  hX.cox (hX.inv 3 (by norm_num)) (hX.inv 5 (by norm_num)) (hX.rel_get 20 (by norm_num))
    (wordProd_rel20 X)

theorem exact_inv (hX : LiftData X K) {i : ℕ} (hi : i < 6) : wordProd X (onRels.getD i []) = 1 := by
  interval_cases i <;>
    simpa [onRels, CFSG.Sporadic.Bridge.ONGPL.Native.rels, wordProd, sq] using hX.inv _ hi

theorem exact21 (hX : LiftData X K) : wordProd X (onRels.getD 21 []) = 1 := by
  have h := hX.g4
  simpa [onRels, CFSG.Sporadic.Bridge.ONGPL.Native.rels, wordProd, pow_succ, mul_assoc] using h

theorem exact22 (hX : LiftData X K) : wordProd X (onRels.getD 22 []) = 1 := by
  have hmem := hX.rel_get 22 (by norm_num)
  set ζ := wordProd X (onRels.getD 22 []) with hζ
  have hval : ζ = X 5 * (X 0 * (X 6 * X 6)) := by
    rw [hζ]
    simp [onRels, CFSG.Sporadic.Bridge.ONGPL.Native.rels, wordProd, hX.inv_eq (i := 5)
      (by norm_num), hX.inv_eq (i := 0) (by norm_num)]
  have h14 := hX.exact14
  rw [wordProd_rel14] at h14
  have hg : X 6 ^ 2 = X 0 * X 5 * ζ := by
    rw [hval, sq]
    have h5 : X 5 * X 5 = 1 := by rw [← sq]; exact hX.inv 5 (by norm_num)
    have h0 : X 0 * X 0 = 1 := by rw [← sq]; exact hX.inv 0 (by norm_num)
    calc X 6 * X 6 = X 0 * (X 5 * X 5) * X 0 * (X 6 * X 6) := by rw [h5, mul_one, ← sq, ← sq,
          hX.inv 0 (by norm_num), one_mul]
      _ = X 0 * X 5 * (X 5 * (X 0 * (X 6 * X 6))) := by group
  have h4 := hX.g4
  rw [show X 6 ^ 4 = (X 6 ^ 2) ^ 2 by group, hg, center_sq_mul (hX.central hmem), h14,
    one_mul] at h4
  exact eq_one_of_sq_of_cube (hX.cube _ hmem) h4

theorem exact23 (hX : LiftData X K) : wordProd X (onRels.getD 23 []) = 1 := by
  have hmem := hX.rel_get 23 (by norm_num)
  set ζ := wordProd X (onRels.getD 23 []) with hζ
  have hval : ζ = X 5 * (X 0 * (X 2 * X 3) ^ 4) := by
    rw [hζ]
    simp [onRels, CFSG.Sporadic.Bridge.ONGPL.Native.rels, wordProd, pow_succ, mul_assoc,
      hX.inv_eq (i := 5) (by norm_num), hX.inv_eq (i := 0) (by norm_num)]
  have h14 := hX.exact14
  rw [wordProd_rel14] at h14
  have h8 := hX.exact8
  rw [wordProd_rel8] at h8
  have hcd : (X 2 * X 3) ^ 4 = X 0 * X 5 * ζ := by
    rw [hval]
    have h5 : X 5 * X 5 = 1 := by rw [← sq]; exact hX.inv 5 (by norm_num)
    have h0 : X 0 * X 0 = 1 := by rw [← sq]; exact hX.inv 0 (by norm_num)
    calc (X 2 * X 3) ^ 4 = X 0 * (X 5 * X 5) * X 0 * (X 2 * X 3) ^ 4 := by
          rw [h5, mul_one, h0, one_mul]
      _ = X 0 * X 5 * (X 5 * (X 0 * (X 2 * X 3) ^ 4)) := by group
  rw [show (X 2 * X 3) ^ 8 = ((X 2 * X 3) ^ 4) ^ 2 by group, hcd,
    center_sq_mul (hX.central hmem), h14, one_mul] at h8
  exact eq_one_of_sq_of_cube (hX.cube _ hmem) h8

theorem conj_exact (hX : LiftData X K) {c u ζ : G} (hc : c ^ 2 = 1) (hmem : ζ ∈ K)
    (h : c * u⁻¹ * c * u = ζ) : ζ = 1 := by
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hc)
  have h1 : u⁻¹ * c * u = c * ζ := by
    rw [← h]
    calc u⁻¹ * c * u = c * c * (u⁻¹ * c * u) := by rw [← sq, hc, one_mul]
      _ = c * (c * u⁻¹ * c * u) := by group
  have h2 : (u⁻¹ * c * u) ^ 2 = 1 := by
    rw [sq, show u⁻¹ * c * u * (u⁻¹ * c * u) = u⁻¹ * (c * c) * u by group, ← sq, hc]
    group
  rw [h1, center_sq_mul (hX.central hmem), hc, one_mul] at h2
  exact eq_one_of_sq_of_cube (hX.cube _ hmem) h2

theorem exact24 (hX : LiftData X K) : wordProd X (onRels.getD 24 []) = 1 := by
  have hmem := hX.rel_get 24 (by norm_num)
  apply hX.conj_exact (c := X 2) (u := X 3 * X 6 * X 3 * X 6) (hX.inv 2 (by norm_num)) hmem
  have h3 := hX.inv_eq (i := 3) (by norm_num)
  simp only [onRels, CFSG.Sporadic.Bridge.ONGPL.Native.rels, List.getD_eq_getElem?_getD,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, wordProd, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, ↓reduceIte, Bool.false_eq_true, mul_inv_rev, h3,
    mul_one, mul_assoc]

theorem exact25 (hX : LiftData X K) : wordProd X (onRels.getD 25 []) = 1 := by
  have hmem := hX.rel_get 25 (by norm_num)
  apply hX.conj_exact (c := X 3) (u := X 2 * X 6 * X 2 * X 6) (hX.inv 3 (by norm_num)) hmem
  have h2 := hX.inv_eq (i := 2) (by norm_num)
  simp only [onRels, CFSG.Sporadic.Bridge.ONGPL.Native.rels, List.getD_eq_getElem?_getD,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, wordProd, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, ↓reduceIte, Bool.false_eq_true, mul_inv_rev, h2,
    mul_one, mul_assoc]

theorem exact (hX : LiftData X K) : ∀ i < 26, wordProd X (onRels.getD i []) = 1 := by
  intro i hi
  rcases Nat.lt_or_ge i 6 with h6 | h6
  · exact hX.exact_inv h6
  interval_cases i
  all_goals first
    | exact hX.exact6 | exact hX.exact7 | exact hX.exact8 | exact hX.exact9 | exact hX.exact10
    | exact hX.exact11 | exact hX.exact12 | exact hX.exact13 | exact hX.exact14
    | exact hX.exact15 | exact hX.exact16 | exact hX.exact17 | exact hX.exact18
    | exact hX.exact19 | exact hX.exact20 | exact hX.exact21 | exact hX.exact22
    | exact hX.exact23 | exact hX.exact24 | exact hX.exact25

end LiftData

theorem lift_mk_fin8 (X : ℕ → G) (w : List (Fin 8 × Bool)) :
    FreeGroup.lift (fun k : Fin 8 => X k.val) (FreeGroup.mk w) =
      wordProd X (w.map fun l => (l.1.val, l.2)) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [show FreeGroup.mk (x :: w) = FreeGroup.mk [x] * FreeGroup.mk w from rfl, map_mul, ih]
    obtain ⟨i, b⟩ := x
    cases b with
    | true =>
      rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
      simp only [wordProd, List.map_cons, List.prod_cons, ↓reduceIte]
    | false =>
      rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
        FreeGroup.lift_apply_of]
      simp only [wordProd, List.map_cons, List.prod_cons, Bool.false_eq_true, ↓reduceIte]

theorem wordProd_append (X : ℕ → G) (v w : List (ℕ × Bool)) :
    wordProd X (v ++ w) = wordProd X v * wordProd X w := by
  simp [wordProd]

theorem wordProd_congr {X Y : ℕ → G} {v : List (ℕ × Bool)} (h : ∀ l ∈ v, X l.1 = Y l.1) :
    wordProd X v = wordProd Y v := by
  induction v with
  | nil => rfl
  | cons l v ih =>
    simp only [wordProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [h l List.mem_cons_self, ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')]

@[expose] def toF8 (v : List (ℕ × Bool)) : List (Fin 8 × Bool) :=
  v.map fun l => (Fin.ofNat 8 l.1, l.2)

theorem coverRels_eq (e₁ e₂ e₃ : ℕ) : coverRels e₁ e₂ e₃ =
    (onRels.take 26).map toF8 ++ ([toF8 (onRels.getD 26 []) ++ zInv e₁,
      toF8 (onRels.getD 27 []) ++ zInv e₂, toF8 (onRels.getD 28 []) ++ zInv e₃,
      [(7, true), (7, true), (7, true)]] ++
      (List.range 7).map fun i => [(7, true), (Fin.ofNat 8 i, true), (7, false),
        (Fin.ofNat 8 i, false)]) := rfl

theorem onRels_lt : ∀ v ∈ onRels, ∀ l ∈ v, l.1 < 7 := by decide

theorem map_toF8 {v : List (ℕ × Bool)} (hv : ∀ l ∈ v, l.1 < 8) :
    (toF8 v).map (fun l => (l.1.val, l.2)) = v := by
  induction v with
  | nil => rfl
  | cons l v ih =>
    simp only [toF8, List.map_cons, List.map_map] at ih ⊢
    rw [ih fun l' hl' => hv l' (List.mem_cons_of_mem _ hl')]
    congr 1
    obtain ⟨a, b⟩ := l
    have ha : a < 8 := hv _ List.mem_cons_self
    simp [Nat.mod_eq_of_lt ha]

theorem wordProd_zInv (X : ℕ → G) (e : ℕ) :
    wordProd X ((zInv e).map fun l => (l.1.val, l.2)) = (X 7)⁻¹ ^ e := by
  induction e with
  | zero => simp [zInv, wordProd]
  | succ e ih =>
    rw [zInv, List.replicate_succ, List.map_cons, pow_succ']
    simp only [wordProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [← ih]
    rfl

theorem lift_relators {X : ℕ → G} {K : Subgroup G} (hX : LiftData X K) (hz : X 7 ∈ K)
    {e₁ e₂ e₃ : ℕ} (h₁ : wordProd X (onRels.getD 26 []) = X 7 ^ e₁)
    (h₂ : wordProd X (onRels.getD 27 []) = X 7 ^ e₂)
    (h₃ : wordProd X (onRels.getD 28 []) = X 7 ^ e₃) :
    ∀ r ∈ {r : FreeGroup (Fin 8) | r ∈ (coverRels e₁ e₂ e₃).map FreeGroup.mk},
      FreeGroup.lift (fun k : Fin 8 => X k.val) r = 1 := by
  intro r hr
  simp only [Set.mem_ofPred_eq, List.mem_map] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  rw [lift_mk_fin8]
  have hlt : ∀ v ∈ onRels, ∀ l ∈ v, l.1 < 8 := fun v hv l hl => by
    have := onRels_lt v hv l hl
    omega
  have hzc := Subgroup.mem_center_iff.1 (hX.central hz)
  rw [coverRels_eq, List.mem_append, List.mem_append] at hw
  rcases hw with hw | hw | hw
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
    rw [map_toF8 (hlt v (List.mem_of_mem_take hv))]
    obtain ⟨i, hi, hvi⟩ := List.getElem_of_mem hv
    have hi26 : i < 26 := by
      have := hi
      simp only [List.length_take, lt_inf_iff] at this
      exact this.1
    have := hX.exact i hi26
    rw [List.getD_eq_getElem _ _ (by rw [onRels_length]; omega), ← List.getElem_take (j := 26)
      (h := hi), hvi] at this
    exact this
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    have hmem : ∀ j < 29, onRels.getD j [] ∈ onRels := fun j hj => onRels_getD_mem hj
    rcases hw with rfl | rfl | rfl | rfl
    · rw [List.map_append, wordProd_append, map_toF8 (hlt _ (hmem 26 (by norm_num))),
        wordProd_zInv, h₁, inv_pow, mul_inv_cancel]
    · rw [List.map_append, wordProd_append, map_toF8 (hlt _ (hmem 27 (by norm_num))),
        wordProd_zInv, h₂, inv_pow, mul_inv_cancel]
    · rw [List.map_append, wordProd_append, map_toF8 (hlt _ (hmem 28 (by norm_num))),
        wordProd_zInv, h₃, inv_pow, mul_inv_cancel]
    · have h3 := hX.cube _ hz
      rw [pow_three] at h3
      simpa [wordProd] using h3
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
    rw [List.mem_range] at hi
    have hval : (Fin.ofNat 8 i).val = i := by simp; omega
    have h7 : ((7 : Fin 8) : ℕ) = 7 := rfl
    simp only [List.map_cons, List.map_nil, hval, h7, wordProd, List.prod_cons, List.prod_nil,
      ↓reduceIte, Bool.false_eq_true, mul_one]
    rw [← mul_assoc, show X 7 * X i = X i * X 7 from (hzc (X i)).symm]
    group

@[expose] def chiImg (n : ℕ) : Multiplicative (ZMod 3) :=
  if n = 7 then Multiplicative.ofAdd 1 else 1

theorem chi_relators : ∀ r ∈ coverRels 0 0 0,
    wordProd chiImg (r.map fun l => (l.1.val, l.2)) = 1 := by
  decide

theorem lift_chi_relator :
    ∀ r ∈ {r : FreeGroup (Fin 8) | r ∈ (coverRels 0 0 0).map FreeGroup.mk},
      FreeGroup.lift (fun k : Fin 8 => chiImg k.val) r = 1 := by
  intro r hr
  simp only [Set.mem_ofPred_eq, List.mem_map] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  rw [lift_mk_fin8]
  exact chi_relators w hw

@[expose] def chiZero : FHat 0 0 0 →* Multiplicative (ZMod 3) :=
  PresentedGroup.toGroup lift_chi_relator

theorem chiZero_surjective : Function.Surjective chiZero := by
  intro a
  refine ⟨PresentedGroup.of 7 ^ (Multiplicative.toAdd a).val, ?_⟩
  rw [map_pow, chiZero, PresentedGroup.toGroup.of]
  show (Multiplicative.ofAdd (1 : ZMod 3)) ^ (Multiplicative.toAdd a).val = a
  rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]

theorem not_surj_zero [Finite G] [Group.IsPerfect G] (hG : Nat.card G = 1382446517760)
    (φ : FHat 0 0 0 →* G) (hφ : Function.Surjective φ) : False := by
  have hfin := card_FHat_zero_le.1
  have hle : (⊤ : Subgroup G) ≤ chiZero.ker.map φ := by
    have hc : commutator (FHat 0 0 0) ≤ chiZero.ker := Abelianization.commutator_subset_ker _
    have hmap := Subgroup.map_mono (f := φ) hc
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 hφ, ← commutator_def, Group.IsPerfect.commutator_eq_top] at hmap
    exact hmap
  have h1 : Nat.card G ≤ Nat.card chiZero.ker := by
    rw [← Subgroup.card_top (G := G)]
    exact (Subgroup.card_le_of_le hle).trans
      (Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd chiZero.ker φ))
  have h2 := Subgroup.card_ker_mul_card_of_surjective (f := chiZero) chiZero_surjective
  rw [Nat.card_eq_fintype_card (α := Multiplicative (ZMod 3)), Fintype.card_multiplicative,
    ZMod.card] at h2
  have h3 := card_FHat_zero_le.2
  omega

theorem eq_one_of_surj [Finite G] [Group.IsPerfect G] (hG : Nat.card G = 1382446517760)
    {e₁ e₂ e₃ : ℕ} (h₁ : e₁ < 2) (h₂ : e₂ < 3) (h₃ : e₃ < 3) (φ : FHat e₁ e₂ e₃ →* G)
    (hφ : Function.Surjective φ) : e₁ = 1 ∧ e₂ = 1 ∧ e₃ = 1 := by
  have collapse : Finite (FHat e₁ e₂ e₃) → Nat.card (FHat e₁ e₂ e₃) ≤ 460815505920 → False :=
    fun hf hc => by
      have := Nat.card_le_card_of_surjective φ hφ
      omega
  interval_cases e₁
  · by_cases h0 : e₂ = 0 ∧ e₃ = 0
    · obtain ⟨rfl, rfl⟩ := h0
      exact (not_surj_zero hG φ hφ).elim
    · obtain ⟨hf, hc⟩ := card_FHat_le_A h₂ h₃ h0
      exact (collapse hf hc).elim
  · by_cases h1 : e₂ = 1 ∧ e₃ = 1
    · exact ⟨rfl, h1⟩
    · obtain ⟨hf, hc⟩ := card_FHat_le_B h₂ h₃ h1
      exact (collapse hf hc).elim

theorem rel_mem (i : ℕ) (hi : i < 29) : onRels.getD i [] ∈ PON.relatorLetters := by
  rw [CFSG.Sporadic.Bridge.ON.relatorLetters_eq]
  exact onRels_getD_mem hi

theorem pGen_sq {i : ℕ} (hi : i < 6) : pGen PON i ^ 2 = 1 := by
  have h := wordProd_pGen_relator PON (rel_mem i (by omega))
  interval_cases i <;>
    simpa [onRels, CFSG.Sporadic.Bridge.ONGPL.Native.rels, wordProd, sq] using h

theorem pGen_six_four : pGen PON 6 ^ 4 = 1 := by
  have h := wordProd_pGen_relator PON (rel_mem 21 (by norm_num))
  simpa [onRels, CFSG.Sporadic.Bridge.ONGPL.Native.rels, wordProd, pow_succ, mul_assoc] using h

theorem nonempty_equiv_FHat [Finite G] [Group.IsPerfect G] (K : Subgroup G) [K.Normal]
    (eK : K ≃* Multiplicative (ZMod 3)) (eQ : G ⧸ K ≃* Blueprint.NativeSporadic.ON) :
    Nonempty (G ≃* FHat 1 1 1) := by
  classical
  have hK3 : Nat.card K = 3 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  have hKc : K ≤ Subgroup.center G :=
    CFSG.Certificates.normal_le_center_of_card_le_four K (by omega)
  have hcube : ∀ k ∈ K, k ^ 3 = 1 := fun k hk => by
    have := pow_card_eq_one' (G := K) (x := ⟨k, hk⟩)
    rw [hK3] at this
    exact congrArg Subtype.val this
  have hG : Nat.card G = 1382446517760 := by
    have h := Subgroup.card_mul_index K
    rw [Subgroup.index, Nat.card_congr eQ.toEquiv, CFSG.Sporadic.ON.card_ON_eq, hK3] at h
    omega
  obtain ⟨eON⟩ := nonempty_equiv_PON
  set eP : PON.Group ≃* G ⧸ K := eON.symm.trans eQ.symm with heP
  have hy : ∀ i : ℕ, ∃ y : G, (y : G ⧸ K) = eP (pGen PON i) := fun i =>
    QuotientGroup.mk_surjective _
  choose y hy using hy
  set X0 : ℕ → G := fun i => if i < 6 then y i ^ 3 else if i = 6 then (y 6)⁻¹ ^ 3 else 1 with hX0
  have hX0lt : ∀ i < 6, X0 i = y i ^ 3 := fun i hi => by simp [hX0, hi]
  have hX06 : X0 6 = (y 6)⁻¹ ^ 3 := by simp [hX0]
  have hq : ∀ i < 7, ((X0 i : G) : G ⧸ K) = eP (pGen PON i) := by
    intro i hi
    by_cases h6 : i < 6
    · rw [hX0lt i h6, QuotientGroup.mk_pow, hy, ← map_pow,
        show pGen PON i ^ 3 = pGen PON i ^ 2 * pGen PON i by group, pGen_sq h6, one_mul]
    · have : i = 6 := by omega
      subst this
      rw [hX06, QuotientGroup.mk_pow, QuotientGroup.mk_inv, hy, ← map_inv, ← map_pow,
        show (pGen PON 6)⁻¹ ^ 3 = (pGen PON 6 ^ 4)⁻¹ * pGen PON 6 by group, pGen_six_four,
        inv_one, one_mul]
  have hmemK : ∀ g : G, ((g : G) : G ⧸ K) = 1 → g ∈ K := fun g hg =>
    (QuotientGroup.eq_one_iff g).1 hg
  have hrel0 : ∀ v ∈ onRels, wordProd X0 v ∈ K := by
    intro v hv
    apply hmemK
    have hmk : ((wordProd X0 v : G) : G ⧸ K) = wordProd (fun i => ((X0 i : G) : G ⧸ K)) v :=
      map_wordProd (QuotientGroup.mk' K) X0 v
    have hmap := map_wordProd eP.toMonoidHom (pGen PON) v
    simp only [MulEquiv.coe_toMonoidHom] at hmap
    rw [hmk, wordProd_congr (Y := fun i => eP (pGen PON i)) (fun l hl => hq _
      (onRels_lt v hv l hl)), ← hmap]
    have := wordProd_pGen_relator PON (by rwa [CFSG.Sporadic.Bridge.ON.relatorLetters_eq])
    rw [this, map_one]
  have hinv0 : ∀ i < 6, X0 i ^ 2 = 1 := by
    intro i hi
    have hk : y i ^ 2 ∈ K := by
      apply hmemK
      rw [QuotientGroup.mk_pow, hy, ← map_pow, pGen_sq hi, map_one]
    rw [hX0lt i hi]
    rw [← pow_mul, show 3 * 2 = 2 * 3 by rfl, pow_mul]
    exact hcube _ hk
  have hg40 : X0 6 ^ 4 = 1 := by
    have hk : y 6 ^ 4 ∈ K := by
      apply hmemK
      rw [QuotientGroup.mk_pow, hy, ← map_pow, pGen_six_four, map_one]
    rw [hX06, ← pow_mul, inv_pow, show 3 * 4 = 4 * 3 by rfl, pow_mul, hcube _ hk, inv_one]
  set ζ0 : G := (eK.symm (Multiplicative.ofAdd 1) : G) with hζ0
  have hζ0K : ζ0 ∈ K := (eK.symm _).2
  have hpowK : ∀ k (hk : k ∈ K), k = ζ0 ^ (Multiplicative.toAdd (eK ⟨k, hk⟩)).val := by
    intro k hk
    have : (⟨k, hk⟩ : K) = eK.symm (Multiplicative.ofAdd 1) ^
        (Multiplicative.toAdd (eK ⟨k, hk⟩)).val := by
      rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, ofAdd_toAdd,
        MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val this
  obtain ⟨ζ, hζK, f₁, f₂, f₃, hf₁, hf₂, hf₃, hv₁, hv₂, hv₃⟩ : ∃ ζ ∈ K, ∃ f₁ f₂ f₃ : ℕ,
      f₁ < 2 ∧ f₂ < 3 ∧ f₃ < 3 ∧ wordProd X0 (onRels.getD 26 []) = ζ ^ f₁ ∧
        wordProd X0 (onRels.getD 27 []) = ζ ^ f₂ ∧ wordProd X0 (onRels.getD 28 []) = ζ ^ f₃ := by
    have hm : ∀ j < 29, wordProd X0 (onRels.getD j []) ∈ K := fun j hj =>
      hrel0 _ (onRels_getD_mem hj)
    have e₁ := hpowK _ (hm 26 (by norm_num))
    have e₂ := hpowK _ (hm 27 (by norm_num))
    have e₃ := hpowK _ (hm 28 (by norm_num))
    set a₁ := (Multiplicative.toAdd (eK ⟨_, hm 26 (by norm_num)⟩)).val with ha₁
    set a₂ := (Multiplicative.toAdd (eK ⟨_, hm 27 (by norm_num)⟩)).val with ha₂
    set a₃ := (Multiplicative.toAdd (eK ⟨_, hm 28 (by norm_num)⟩)).val with ha₃
    have hb₁ : a₁ < 3 := ZMod.val_lt _
    have hb₂ : a₂ < 3 := ZMod.val_lt _
    have hb₃ : a₃ < 3 := ZMod.val_lt _
    have h03 : ζ0 ^ 3 = 1 := hcube _ hζ0K
    have hsq : ∀ a : ℕ, (ζ0 ^ 2) ^ ((2 * a) % 3) = ζ0 ^ a := by
      intro a
      rw [← pow_mul, ← pow_mod_three_of_cube h03, ← pow_mod_three_of_cube h03 a]
      congr 1
      omega
    by_cases h2 : a₁ = 2
    · refine ⟨ζ0 ^ 2, K.pow_mem hζ0K 2, 1, (2 * a₂) % 3, (2 * a₃) % 3, by norm_num,
        Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), ?_, by rw [e₂, hsq],
        by rw [e₃, hsq]⟩
      rw [e₁, h2, pow_one]
    · exact ⟨ζ0, hζ0K, a₁, a₂, a₃, by omega, hb₂, hb₃, e₁, e₂, e₃⟩
  set X : ℕ → G := fun i => if i = 7 then ζ else X0 i with hXdef
  have hXlt : ∀ i < 7, X i = X0 i := fun i hi => by simp [hXdef]; omega
  have hcongr : ∀ v ∈ onRels, wordProd X v = wordProd X0 v := fun v hv =>
    wordProd_congr fun l hl => hXlt _ (onRels_lt v hv l hl)
  have hXD : LiftData X K :=
    { central := hKc
      cube := hcube
      inv := fun i hi => by rw [hXlt i (by omega)]; exact hinv0 i hi
      g4 := by rw [hXlt 6 (by norm_num)]; exact hg40
      rel := fun v hv => by rw [hcongr v hv]; exact hrel0 v hv }
  have hm : ∀ j < 29, onRels.getD j [] ∈ onRels := fun j hj => onRels_getD_mem hj
  have hX7 : X 7 = ζ := by simp [hXdef]
  have hφrel := lift_relators hXD (by rw [hX7]; exact hζK)
    (by rw [hcongr _ (hm 26 (by norm_num)), hX7]; exact hv₁)
    (by rw [hcongr _ (hm 27 (by norm_num)), hX7]; exact hv₂)
    (by rw [hcongr _ (hm 28 (by norm_num)), hX7]; exact hv₃)
  set φ : FHat f₁ f₂ f₃ →* G := PresentedGroup.toGroup hφrel with hφdef
  have hgen : ∀ i < 7, X i ∈ φ.range := fun i hi =>
    ⟨PresentedGroup.of ⟨i, by omega⟩, PresentedGroup.toGroup.of _⟩
  have hmapTop : φ.range.map (QuotientGroup.mk' K) = ⊤ := by
    rw [eq_top_iff]
    have hcl : (⊤ : Subgroup (G ⧸ K)) = (Subgroup.closure (Set.range
        (PresentedGroup.of : Fin PON.generatorCount → PON.Group))).map eP.toMonoidHom := by
      rw [PresentedGroup.closure_range_of, ← MonoidHom.range_eq_map]
      exact (MonoidHom.range_eq_top.2 eP.surjective).symm
    rw [hcl, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have hi : i.val < 7 := by
      have h1 := i.isLt
      have h2 := generatorCount_PON
      omega
    refine ⟨X i.val, hgen _ hi, ?_⟩
    rw [QuotientGroup.mk'_apply, hXlt _ hi, hq _ hi, MulEquiv.coe_toMonoidHom, pGen_of]
  have hqr : ∀ g : G, ∃ r ∈ φ.range, ∃ k ∈ K, g = r * k := by
    intro g
    have : (QuotientGroup.mk' K g) ∈ φ.range.map (QuotientGroup.mk' K) := by
      rw [hmapTop]; trivial
    obtain ⟨r, hr, hrg⟩ := this
    refine ⟨r, hr, r⁻¹ * g, ?_, by group⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hrg
    exact hrg
  have hcomm : ∀ {r₁ r₂ k₁ k₂ : G}, k₁ ∈ K → k₂ ∈ K → ⁅r₁ * k₁, r₂ * k₂⁆ = ⁅r₁, r₂⁆ := by
    intro r₁ r₂ k₁ k₂ h₁ h₂
    have c₁ := Subgroup.mem_center_iff.1 (hKc h₁)
    have c₂ := Subgroup.mem_center_iff.1 (hKc h₂)
    rw [commutatorElement_def, commutatorElement_def]
    calc r₁ * k₁ * (r₂ * k₂) * (r₁ * k₁)⁻¹ * (r₂ * k₂)⁻¹ =
        r₁ * (k₁ * r₂) * k₂ * k₁⁻¹ * r₁⁻¹ * k₂⁻¹ * r₂⁻¹ := by group
      _ = r₁ * (r₂ * k₁) * k₂ * k₁⁻¹ * r₁⁻¹ * k₂⁻¹ * r₂⁻¹ := by rw [c₁ r₂]
      _ = r₁ * r₂ * (k₁ * k₂ * k₁⁻¹) * r₁⁻¹ * k₂⁻¹ * r₂⁻¹ := by group
      _ = r₁ * r₂ * k₂ * r₁⁻¹ * k₂⁻¹ * r₂⁻¹ := by
          rw [show k₁ * k₂ * k₁⁻¹ = k₂ by rw [c₂ k₁, mul_assoc, mul_inv_cancel, mul_one]]
      _ = r₁ * r₂ * (r₁⁻¹ * k₂) * k₂⁻¹ * r₂⁻¹ := by rw [mul_assoc (r₁ * r₂), ← c₂ r₁⁻¹]
      _ = r₁ * r₂ * r₁⁻¹ * r₂⁻¹ := by group
  have hφ : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := G),
      commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    obtain ⟨r₁, hr₁, k₁, hk₁, rfl⟩ := hqr g₁
    obtain ⟨r₂, hr₂, k₂, hk₂, rfl⟩ := hqr g₂
    rw [hcomm hk₁ hk₂]
    exact Subgroup.commutator_mem_commutator hr₁ hr₂ |> fun h => by
      rw [commutatorElement_def]
      exact φ.range.mul_mem (φ.range.mul_mem (φ.range.mul_mem hr₁ hr₂) (φ.range.inv_mem hr₁))
        (φ.range.inv_mem hr₂)
  obtain ⟨rfl, rfl, rfl⟩ := eq_one_of_surj hG hf₁ hf₂ hf₃ φ hφ
  have hinj : Function.Injective φ :=
    (hφ.bijective_of_nat_card_le (by rw [card_FHat_one, hG])).1
  exact ⟨(MulEquiv.ofBijective φ ⟨hinj, hφ⟩).symm⟩

end CFSG.RankThree.Native.ONTriple
