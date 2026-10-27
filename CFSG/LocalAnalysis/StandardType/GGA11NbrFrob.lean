module

public import CFSG.LocalAnalysis.StandardType.GGA11NbrDefs
public import CFSG.LocalAnalysis.StandardType.GGA11J9Gen

public section

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.A8Coord Matrix

namespace CFSG.StandardType.A11

private theorem one_add_one_eq_zero_F2 : (1 : F2) + 1 = 0 := by
  rw [← two_mul, two_eq_zero, zero_mul]

private noncomputable def Fr : Matrix (Fin 3) (Fin 3) F2 := !![1,0,0; 0,0,1; 0,1,1]

private noncomputable def F0 : SL 9 :=
  tvAt 0 (pos 3 1) (pos 3 2) * tvAt 0 (pos 3 2) (pos 3 1)

private noncomputable def F0mat : Matrix (Fin 9) (Fin 9) F2 :=
  Matrix.of fun a b =>
    if blk (Fin.castLE (by omega) a) = (0 : Fin 4) ∧
        blk (Fin.castLE (by omega) b) = (0 : Fin 4)
      then Fr (idxIn (Fin.castLE (by omega) a)) (idxIn (Fin.castLE (by omega) b))
      else if a = b then 1 else 0

private theorem a11nf_swap0_31 : swapBlocks 0 (pos 3 1) = (7 : Fin 12) := by decide
private theorem a11nf_swap0_32 : swapBlocks 0 (pos 3 2) = (8 : Fin 12) := by decide

private theorem a11nf_tvAt0_12 : tvAt 0 (pos 3 1) (pos 3 2) = tv9 (7 : Fin 12) (8 : Fin 12) := by
  rw [tvAt, a11nf_swap0_31, a11nf_swap0_32]

private theorem a11nf_tvAt0_21 : tvAt 0 (pos 3 2) (pos 3 1) = tv9 (8 : Fin 12) (7 : Fin 12) := by
  rw [tvAt, a11nf_swap0_32, a11nf_swap0_31]

private theorem a11nf_tv9_apply_eq (a b : Fin 12) (ha : a.val < 9) (hb : b.val < 9) (hab : a ≠ b) :
    ((tv9 a b : SL 9) : Matrix (Fin 9) (Fin 9) F2) =
      (1 : Matrix (Fin 9) (Fin 9) F2) + Matrix.single ⟨a.val, ha⟩ ⟨b.val, hb⟩ (1 : F2) := by
  rw [tv9, dif_pos (show a.val < 9 ∧ b.val < 9 ∧ a ≠ b from ⟨ha, hb, hab⟩)]
  exact SpecialLinearGroup.transvection_coe _ _

private theorem a11nf_F0_coe : ((F0 : SL 9) : Matrix (Fin 9) (Fin 9) F2) = F0mat := by
  rw [F0, a11nf_tvAt0_12, a11nf_tvAt0_21]
  change ((tv9 (7 : Fin 12) (8 : Fin 12) : SL 9) : Matrix (Fin 9) (Fin 9) F2) *
      ((tv9 (8 : Fin 12) (7 : Fin 12) : SL 9) : Matrix (Fin 9) (Fin 9) F2) = F0mat
  rw [a11nf_tv9_apply_eq 7 8 (by decide) (by decide) (by decide),
    a11nf_tv9_apply_eq 8 7 (by decide) (by decide) (by decide)]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [F0mat, Fr, blk, idxIn, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.single_apply, Matrix.one_apply, one_add_one_eq_zero_F2]

private noncomputable def blkM0 (A : Matrix (Fin 3) (Fin 3) F2) : Matrix (Fin 9) (Fin 9) F2 :=
  Matrix.of fun a b =>
    if blk (Fin.castLE (by omega) a) = (0 : Fin 4) ∧
        blk (Fin.castLE (by omega) b) = (0 : Fin 4)
      then A (idxIn (Fin.castLE (by omega) a)) (idxIn (Fin.castLE (by omega) b))
      else if a = b then 1 else 0

private theorem blkM0_mul (A B : Matrix (Fin 3) (Fin 3) F2) :
    blkM0 A * blkM0 B = blkM0 (A * B) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blkM0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply,
      one_add_one_eq_zero_F2, blk, idxIn]

private theorem a11nf_Fr_Om : Fr * Om = Om * Om * Fr := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fr, Om, Matrix.mul_apply, Fin.sum_univ_three, pow_two, one_add_one_eq_zero_F2]

private theorem a11nf_F0_T9_0_mat : F0mat * T9mat 0 = T9mat 0 ^ 2 * F0mat := by
  rw [show F0mat = blkM0 Fr from rfl, show T9mat 0 = blkM0 Om from rfl,
    pow_two, blkM0_mul, blkM0_mul, blkM0_mul, a11nf_Fr_Om]

private theorem a11nf_F0_T9_1_mat : F0mat * T9mat 1 = T9mat 1 * F0mat := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [F0mat, Fr, T9mat, Om, blk, idxIn, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.single_apply, Matrix.one_apply, one_add_one_eq_zero_F2]

private theorem a11nf_F0_T9_0 : F0 * T9 0 = (T9 0) ^ 2 * F0 := by
  apply Subtype.ext
  change ((F0 : SL 9) : Matrix (Fin 9) (Fin 9) F2) * T9mat 0 = T9mat 0 ^ 2 *
    ((F0 : SL 9) : Matrix (Fin 9) (Fin 9) F2)
  rw [a11nf_F0_coe]
  exact a11nf_F0_T9_0_mat

private theorem a11nf_F0_T9_1 : F0 * T9 1 = T9 1 * F0 := by
  apply Subtype.ext
  change ((F0 : SL 9) : Matrix (Fin 9) (Fin 9) F2) * T9mat 1 = T9mat 1 *
    ((F0 : SL 9) : Matrix (Fin 9) (Fin 9) F2)
  rw [a11nf_F0_coe]
  exact a11nf_F0_T9_1_mat

private theorem a11nf_F0_T9_2 : F0 * T9 2 = T9 2 * F0 := by
  apply Subtype.ext
  change ((F0 : SL 9) : Matrix (Fin 9) (Fin 9) F2) * T9mat 2 = T9mat 2 *
    ((F0 : SL 9) : Matrix (Fin 9) (Fin 9) F2)
  rw [a11nf_F0_coe]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [F0mat, Fr, T9mat, Om, blk, idxIn, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.single_apply, Matrix.one_apply, one_add_one_eq_zero_F2]

private theorem a11nf_h01 (z : F2) : z = 0 ∨ z = 1 := by
  have hcard : Nat.card F2 = 2 := by
    have := GaloisField.card 2 1 (by omega)
    simpa using this
  by_cases hz : z = 0
  · exact Or.inl hz
  · obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (0 : F2)).mp hcard
    exact Or.inr ((huniq z hz).trans (huniq 1 one_ne_zero).symm)

private theorem a11nf_commute_one_add {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [Ring R]
    {A B : Matrix n n R} (hAB : A * B = 0) (hBA : B * A = 0) :
    (1 + A) * (1 + B) = (1 + B) * (1 + A) := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul,
    Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, hAB, hBA]
  abel

private noncomputable def a11nf_coef (i j : Fin 4) (M : Matrix (Fin 3) (Fin 3) F2)
    (p : Fin 9 × Fin 9) : F2 :=
  if blk (Fin.castLE (by omega) p.1) = i ∧ blk (Fin.castLE (by omega) p.2) = j
    then M (idxIn (Fin.castLE (by omega) p.1)) (idxIn (Fin.castLE (by omega) p.2))
    else 0

private noncomputable def a11nf_Am (i j : Fin 4) (M : Matrix (Fin 3) (Fin 3) F2)
    (p : Fin 9 × Fin 9) : Matrix (Fin 9) (Fin 9) F2 :=
  Matrix.single p.1 p.2 (a11nf_coef i j M p)

private theorem a11nf_coef_cond {i j : Fin 4} {M : Matrix (Fin 3) (Fin 3) F2}
    {p : Fin 9 × Fin 9} (hp : a11nf_coef i j M p ≠ 0) :
    blk (Fin.castLE (by omega) p.1) = i ∧ blk (Fin.castLE (by omega) p.2) = j := by
  by_contra h
  exact hp (by simp [a11nf_coef, h])

private theorem a11nf_Am_mul_Am {i j : Fin 4} (hij : i ≠ j) (M : Matrix (Fin 3) (Fin 3) F2)
    (p q : Fin 9 × Fin 9) : a11nf_Am i j M p * a11nf_Am i j M q = 0 := by
  by_cases hp : a11nf_coef i j M p = 0
  · simp [a11nf_Am, hp]
  by_cases hq : a11nf_coef i j M q = 0
  · simp [a11nf_Am, hq]
  obtain ⟨hp1, hp2⟩ := a11nf_coef_cond hp
  obtain ⟨hq1, hq2⟩ := a11nf_coef_cond hq
  have hpq : p.2 ≠ q.1 := by
    intro h
    have : (i : Fin 4) = j := by rw [← hp2, ← hq1, h]
    exact hij this
  rw [a11nf_Am, a11nf_Am]
  ext a b
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro c _
  rw [Matrix.single_apply, Matrix.single_apply]
  by_cases h1 : p.1 = a ∧ p.2 = c
  · rw [if_pos h1]
    by_cases h2 : q.1 = c ∧ q.2 = b
    · rw [if_pos h2]
      exact absurd (h1.2.trans h2.1.symm) hpq
    · rw [if_neg h2, mul_zero]
  · rw [if_neg h1, zero_mul]

private theorem a11nf_sum_Am_apply (i j : Fin 4) (M : Matrix (Fin 3) (Fin 3) F2)
    (a b : Fin 9) : (∑ p : Fin 9 × Fin 9, a11nf_Am i j M p) a b = a11nf_coef i j M (a, b) := by
  rw [Matrix.sum_apply, Finset.sum_eq_single (a, b)]
  · simp [a11nf_Am, Matrix.single_apply]
  · intro p _ hp
    rw [a11nf_Am, Matrix.single_apply, if_neg]
    intro h
    exact hp (Prod.ext h.1 h.2)
  · intro h
    exact absurd (Finset.mem_univ (a, b)) h

private theorem a11nf_coef_eq_zero_of_eq {i j : Fin 4} (hij : i ≠ j)
    {M : Matrix (Fin 3) (Fin 3) F2} {p : Fin 9 × Fin 9} (hp : p.1 = p.2) :
    a11nf_coef i j M p = 0 := by
  have hbij : ¬(blk (Fin.castLE (by omega) p.1) = i ∧
      blk (Fin.castLE (by omega) p.2) = j) := by
    intro hc
    rw [hp] at hc
    exact hij (hc.1.symm.trans hc.2)
  simp [a11nf_coef, hbij]

private noncomputable def a11nf_factor (i j : Fin 4) (M : Matrix (Fin 3) (Fin 3) F2)
    (p : Fin 9 × Fin 9) : SL 9 :=
  if h : p.1 ≠ p.2 then SpecialLinearGroup.transvection h (a11nf_coef i j M p) else 1

private theorem a11nf_factor_coe {i j : Fin 4} (hij : i ≠ j) (M : Matrix (Fin 3) (Fin 3) F2)
    (p : Fin 9 × Fin 9) :
    ((a11nf_factor i j M p : SL 9) : Matrix (Fin 9) (Fin 9) F2) =
      1 + a11nf_Am i j M p := by
  by_cases h : p.1 ≠ p.2
  · rw [a11nf_factor, dif_pos h, SpecialLinearGroup.transvection_coe, a11nf_Am]
  · rw [a11nf_factor, dif_neg h]
    change (1 : Matrix (Fin 9) (Fin 9) F2) = 1 + a11nf_Am i j M p
    rw [a11nf_Am, a11nf_coef_eq_zero_of_eq hij (not_ne_iff.mp h), Matrix.single_zero, add_zero]

private noncomputable def a11nf_toMat : SL 9 →* Matrix (Fin 9) (Fin 9) F2 where
  toFun := Subtype.val
  map_one' := rfl
  map_mul' := fun A B => rfl

private theorem a11nf_toMat_factor {i j : Fin 4} (hij : i ≠ j) (M : Matrix (Fin 3) (Fin 3) F2)
    (p : Fin 9 × Fin 9) :
    a11nf_toMat (a11nf_factor i j M p) = 1 + a11nf_Am i j M p :=
  a11nf_factor_coe hij M p

private def a11nf_L : List (Fin 9 × Fin 9) := (List.finRange 9).product (List.finRange 9)

private theorem a11nf_L_nodup : a11nf_L.Nodup := by
  rw [a11nf_L]
  exact (List.nodup_finRange 9).product (List.nodup_finRange 9)

private theorem a11nf_L_mem (p : Fin 9 × Fin 9) : p ∈ a11nf_L := by
  obtain ⟨a, b⟩ := p
  rw [a11nf_L]
  exact List.mem_product.mpr ⟨List.mem_finRange _, List.mem_finRange _⟩

private theorem a11nf_L_toFinset : a11nf_L.toFinset = (Finset.univ : Finset (Fin 9 × Fin 9)) := by
  ext p
  simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
  exact a11nf_L_mem p

private theorem a11nf_list_mul_sum {R : Type*} [Semiring R] (a : R) (l : List R) :
    a * l.sum = (l.map (a * ·)).sum := by
  induction l with
  | nil => simp
  | cons b l ih => rw [List.map_cons, List.sum_cons, List.sum_cons, mul_add, ih]

private theorem a11nf_list_prod_one_add {R : Type*} [Ring R] {α : Type*} (l : List α)
    (A : α → R) (h : ∀ p ∈ l, ∀ q ∈ l, A p * A q = 0) :
    (l.map (fun p => 1 + A p)).prod = 1 + (l.map A).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons,
      ih (fun p hp q hq => h p (List.mem_cons_of_mem a hp) q (List.mem_cons_of_mem a hq))]
    have h0 : A a * (l.map A).sum = 0 := by
      rw [a11nf_list_mul_sum, List.map_map]
      apply List.sum_eq_zero
      intro b hb
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
      exact h a List.mem_cons_self p (List.mem_cons_of_mem a hp)
    rw [mul_add, mul_one, add_mul, one_mul, h0, add_zero]
    abel

private theorem a11nf_list_prod_congr {M : Type*} [Monoid M] {α : Type*} (l : List α)
    {f g : α → M} (h : ∀ p ∈ l, f p = g p) : (l.map f).prod = (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
      ih (fun p hp => h p (List.mem_cons_of_mem a hp)), h a List.mem_cons_self]

private theorem a11nf_X8_coe {i j : Fin 3} {M : Matrix (Fin 3) (Fin 3) F2} {g : SL 9}
    (hg : ∀ a b, (g : Matrix (Fin 9) (Fin 9) F2) a b = (if a = b then 1 else 0) +
      (if blk (Fin.castLE (by omega) a) = i.castSucc ∧
          blk (Fin.castLE (by omega) b) = j.castSucc
        then M (idxIn (Fin.castLE (by omega) a)) (idxIn (Fin.castLE (by omega) b)) else 0)) :
    (g : Matrix (Fin 9) (Fin 9) F2) = 1 + (a11nf_L.map (fun p =>
      a11nf_Am i.castSucc j.castSucc M p)).sum := by
  rw [← List.sum_toFinset (fun p => a11nf_Am i.castSucc j.castSucc M p) a11nf_L_nodup,
    a11nf_L_toFinset]
  ext a b
  rw [hg a b, Matrix.add_apply, Matrix.one_apply, a11nf_sum_Am_apply]
  rfl

private theorem a11nf_g_eq_prod {i j : Fin 3} (hij : i ≠ j) (M : Matrix (Fin 3) (Fin 3) F2)
    (g : SL 9)
    (hg : ∀ a b, (g : Matrix (Fin 9) (Fin 9) F2) a b = (if a = b then 1 else 0) +
      (if blk (Fin.castLE (by omega) a) = i.castSucc ∧
          blk (Fin.castLE (by omega) b) = j.castSucc
        then M (idxIn (Fin.castLE (by omega) a)) (idxIn (Fin.castLE (by omega) b)) else 0)) :
    g = (a11nf_L.map (fun p => a11nf_factor i.castSucc j.castSucc M p)).prod := by
  apply Subtype.ext
  change a11nf_toMat g = a11nf_toMat ((a11nf_L.map
    (fun p => a11nf_factor i.castSucc j.castSucc M p)).prod)
  rw [map_list_prod, List.map_map]
  rw [a11nf_list_prod_congr a11nf_L
    (f := a11nf_toMat ∘ fun p => a11nf_factor i.castSucc j.castSucc M p)
    (g := fun p => 1 + a11nf_Am i.castSucc j.castSucc M p)
    (fun p _ => a11nf_toMat_factor (by simpa using hij) M p)]
  rw [a11nf_list_prod_one_add _ (fun p => a11nf_Am i.castSucc j.castSucc M p)
    (fun p _ q _ => a11nf_Am_mul_Am (by simpa using hij) M p q)]
  exact a11nf_X8_coe hg

private theorem a11nf_blk_pos (l : Fin 4) (t : Fin 3) : blk (pos l t) = l := by
  fin_cases l <;> fin_cases t <;> decide

private theorem a11nf_swap_apply_of_ne {a b x : Fin 12} (h1 : x ≠ a) (h2 : x ≠ b) :
    Equiv.swap a b x = x := by
  rw [Equiv.swap_apply_def]
  simp [h1, h2]

private theorem a11nf_swapBlocks_apply {l : Fin 4} {a : Fin 12}
    (hla : blk a ≠ l) (h3a : blk a ≠ 3) : swapBlocks l a = a := by
  have h1 : ∀ t : Fin 3, a ≠ pos l t := fun t h =>
    hla (by rw [h]; exact a11nf_blk_pos l t)
  have h2 : ∀ t : Fin 3, a ≠ pos 3 t := fun t h =>
    h3a (by rw [h]; exact a11nf_blk_pos 3 t)
  simp only [swapBlocks, Equiv.Perm.mul_apply,
    a11nf_swap_apply_of_ne (h1 2) (h2 2), a11nf_swap_apply_of_ne (h1 1) (h2 1),
    a11nf_swap_apply_of_ne (h1 0) (h2 0)]

private theorem a11nf_swapBlocks_three (a : Fin 12) : swapBlocks 3 a = a := by
  simp [swapBlocks]

private theorem a11nf_tvAt_eq_tv9 {l : Fin 4} {a b : Fin 12}
    (hla : blk a ≠ l) (h3a : blk a ≠ 3) (hlb : blk b ≠ l) (h3b : blk b ≠ 3) :
    tvAt l a b = tv9 a b := by
  rw [tvAt, a11nf_swapBlocks_apply hla h3a, a11nf_swapBlocks_apply hlb h3b]

private theorem a11nf_tvAt_three (a b : Fin 12) : tvAt 3 a b = tv9 a b := by
  rw [tvAt, a11nf_swapBlocks_three, a11nf_swapBlocks_three]

private theorem a11nf_castLE_inj {p q : Fin 9}
    (h : (Fin.castLE (by omega) p : Fin 12) = (Fin.castLE (by omega) q : Fin 12)) : p = q :=
  Fin.ext (by simpa using congrArg Fin.val h)

private theorem a11nf_tv9_castLE {p q : Fin 9} (hpq : p ≠ q) :
    tv9 (Fin.castLE (by omega) p) (Fin.castLE (by omega) q) =
      SpecialLinearGroup.transvection (i := p) (j := q) hpq (1 : F2) := by
  have hcond : ((Fin.castLE (by omega) p : Fin 12)).val < 9 ∧
      ((Fin.castLE (by omega) q : Fin 12)).val < 9 ∧
      (Fin.castLE (by omega) p : Fin 12) ≠ (Fin.castLE (by omega) q : Fin 12) :=
    ⟨by simp, by simp, fun h => hpq (a11nf_castLE_inj h)⟩
  rw [tv9, dif_pos hcond]

private theorem a11nf_coherent_tv9 {G : Type} [Group G] {Φ : Fin 4 → SL 9 →* G}
    (hC : Coherent Φ) {k i j : Fin 4} (hk3 : k ≠ 3) (hi3 : i ≠ 3) (hj3 : j ≠ 3)
    (hik : i ≠ k) (hjk : j ≠ k) {p q : Fin 9} (hpq : p ≠ q)
    (hp : blk (Fin.castLE (by omega) p) = i) (hq : blk (Fin.castLE (by omega) q) = j) :
    Φ 3 (SpecialLinearGroup.transvection (i := p) (j := q) hpq (1 : F2)) =
      Φ k (SpecialLinearGroup.transvection (i := p) (j := q) hpq (1 : F2)) := by
  have hp' : (Fin.castLE (by omega) p : Fin 12) ≠ (Fin.castLE (by omega) q : Fin 12) := fun h =>
    hpq (a11nf_castLE_inj h)
  have h := hC 3 k (Fin.castLE (by omega) p) (Fin.castLE (by omega) q) hp'
    (by rw [hp]; exact hi3) (by rw [hq]; exact hj3) (by rw [hp]; exact hik) (by rw [hq]; exact hjk)
  rw [a11nf_tvAt_three,
    a11nf_tvAt_eq_tv9 (by rw [hp]; exact hik) (by rw [hp]; exact hi3)
      (by rw [hq]; exact hjk) (by rw [hq]; exact hj3),
    a11nf_tv9_castLE hpq] at h
  exact h

private theorem a11nf_factor_coh {G : Type} [Group G] {Φ : Fin 4 → SL 9 →* G}
    (hC : Coherent Φ) {k i j : Fin 4} (hk3 : k ≠ 3) (hi3 : i ≠ 3) (hj3 : j ≠ 3)
    (hik : i ≠ k) (hjk : j ≠ k) (M : Matrix (Fin 3) (Fin 3) F2) (p : Fin 9 × Fin 9) :
    Φ 3 (a11nf_factor i j M p) = Φ k (a11nf_factor i j M p) := by
  by_cases hp : p.1 ≠ p.2
  · rw [a11nf_factor, dif_pos hp]
    rcases a11nf_h01 (a11nf_coef i j M p) with hc | hc
    · rw [hc, SpecialLinearGroup.transvection_coeff_zero, map_one, map_one]
    · rw [hc]
      obtain ⟨h1, h2⟩ := a11nf_coef_cond (by rw [hc]; exact one_ne_zero)
      exact a11nf_coherent_tv9 hC hk3 hi3 hj3 hik hjk hp h1 h2
  · rw [a11nf_factor, dif_neg hp, map_one, map_one]

private noncomputable def a11nf_Fk3 (k : Fin 3) : SL 9 :=
  tvAt k.castSucc (pos 3 1) (pos 3 2) * tvAt k.castSucc (pos 3 2) (pos 3 1)

private noncomputable def a11nf_Rk (k : Fin 3) : Matrix (Fin 9) (Fin 9) F2 :=
  Matrix.of fun a b =>
    if blk (Fin.castLE (by omega) a) = k.castSucc ∧
        blk (Fin.castLE (by omega) b) = k.castSucc
      then (Fr + 1) (idxIn (Fin.castLE (by omega) a)) (idxIn (Fin.castLE (by omega) b))
      else 0

private theorem a11nf_swapBlocks_pos3 (l : Fin 4) (a : Fin 3) :
    swapBlocks l (pos 3 a) = pos l a := by
  fin_cases l <;> fin_cases a <;> decide

private theorem a11nf_tvAt_pos3 (l : Fin 4) (a b : Fin 3) :
    tvAt l (pos 3 a) (pos 3 b) = tv9 (pos l a) (pos l b) := by
  rw [tvAt, a11nf_swapBlocks_pos3, a11nf_swapBlocks_pos3]

private theorem a11nf_Fk_coe (k : Fin 3) :
    ((a11nf_Fk3 k : SL 9) : Matrix (Fin 9) (Fin 9) F2) = 1 + a11nf_Rk k := by
  rw [a11nf_Fk3, a11nf_tvAt_pos3, a11nf_tvAt_pos3]
  change ((tv9 (pos k.castSucc 1) (pos k.castSucc 2) : SL 9) :
      Matrix (Fin 9) (Fin 9) F2) *
      ((tv9 (pos k.castSucc 2) (pos k.castSucc 1) : SL 9) :
        Matrix (Fin 9) (Fin 9) F2) = 1 + a11nf_Rk k
  rw [a11nf_tv9_apply_eq _ _ (by fin_cases k <;> decide) (by fin_cases k <;> decide)
      (by fin_cases k <;> decide),
    a11nf_tv9_apply_eq _ _ (by fin_cases k <;> decide) (by fin_cases k <;> decide)
      (by fin_cases k <;> decide)]
  ext a b
  fin_cases k <;> fin_cases a <;> fin_cases b <;>
    simp [a11nf_Rk, Fr, blk, idxIn, pos, Fin.castLE, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.single_apply, Matrix.one_apply, one_add_one_eq_zero_F2]

private theorem a11nf_Rk_apply_zero_of_blk_ne {k : Fin 3} {a b : Fin 9}
    (hb : blk (Fin.castLE (by omega) b) ≠ k.castSucc) : a11nf_Rk k a b = 0 := by
  simp [a11nf_Rk, hb]

private theorem a11nf_Rk_mul_coef {k i j : Fin 3} (hki : k ≠ i)
    {M : Matrix (Fin 3) (Fin 3) F2} {p : Fin 9 × Fin 9} (a : Fin 9) :
    a11nf_Rk k a p.1 * a11nf_coef i.castSucc j.castSucc M p = 0 := by
  by_cases hp : a11nf_coef i.castSucc j.castSucc M p = 0
  · rw [hp, mul_zero]
  · obtain ⟨h1, -⟩ := a11nf_coef_cond hp
    have hne : blk (Fin.castLE (by omega) p.1) ≠ k.castSucc := by
      rw [h1]; exact fun h => hki (Fin.castSucc_injective _ h.symm)
    rw [a11nf_Rk_apply_zero_of_blk_ne hne, zero_mul]

private theorem a11nf_Rk_mul_Am {k i j : Fin 3} (hki : k ≠ i)
    (M : Matrix (Fin 3) (Fin 3) F2) (p : Fin 9 × Fin 9) :
    a11nf_Rk k * a11nf_Am i.castSucc j.castSucc M p = 0 := by
  rw [a11nf_Am]
  ext a b
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro c _
  rw [Matrix.single_apply]
  by_cases h1 : p.1 = c ∧ p.2 = b
  · rw [if_pos h1, ← h1.1]
    exact a11nf_Rk_mul_coef hki a
  · rw [if_neg h1, mul_zero]

private theorem a11nf_coef_mul_Rk {k i j : Fin 3} (hkj : k ≠ j)
    {M : Matrix (Fin 3) (Fin 3) F2} {p : Fin 9 × Fin 9} (b : Fin 9) :
    a11nf_coef i.castSucc j.castSucc M p * a11nf_Rk k p.2 b = 0 := by
  by_cases hp : a11nf_coef i.castSucc j.castSucc M p = 0
  · rw [hp, zero_mul]
  · obtain ⟨-, h2⟩ := a11nf_coef_cond hp
    have hne : blk (Fin.castLE (by omega) p.2) ≠ k.castSucc := by
      rw [h2]; exact fun h => hkj (Fin.castSucc_injective _ h.symm)
    have hRk : a11nf_Rk k p.2 b = 0 := by
      rw [a11nf_Rk]; simp only [Matrix.of_apply]
      exact if_neg (fun hc => hne hc.1)
    rw [hRk, mul_zero]

private theorem a11nf_Am_mul_Rk {k i j : Fin 3} (hkj : k ≠ j)
    (M : Matrix (Fin 3) (Fin 3) F2) (p : Fin 9 × Fin 9) :
    a11nf_Am i.castSucc j.castSucc M p * a11nf_Rk k = 0 := by
  rw [a11nf_Am]
  ext a b
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro c _
  rw [Matrix.single_apply]
  by_cases h1 : p.1 = a ∧ p.2 = c
  · rw [if_pos h1, ← h1.2]
    exact a11nf_coef_mul_Rk hkj b
  · rw [if_neg h1, zero_mul]

private theorem a11nf_Fk_comm {i j k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j)
    (M : Matrix (Fin 3) (Fin 3) F2) {g : SL 9}
    (hg : (g : Matrix (Fin 9) (Fin 9) F2) = 1 +
      ∑ p : Fin 9 × Fin 9, a11nf_Am i.castSucc j.castSucc M p) :
    a11nf_Fk3 k * g = g * a11nf_Fk3 k := by
  apply Subtype.ext
  change ((a11nf_Fk3 k : SL 9) : Matrix (Fin 9) (Fin 9) F2) *
      ((g : SL 9) : Matrix (Fin 9) (Fin 9) F2) =
    ((g : SL 9) : Matrix (Fin 9) (Fin 9) F2) *
      ((a11nf_Fk3 k : SL 9) : Matrix (Fin 9) (Fin 9) F2)
  rw [a11nf_Fk_coe, hg]
  have hR : a11nf_Rk k * (∑ p : Fin 9 × Fin 9, a11nf_Am i.castSucc j.castSucc M p) = 0 := by
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun p _ => a11nf_Rk_mul_Am hki M p
  have hR' : (∑ p : Fin 9 × Fin 9, a11nf_Am i.castSucc j.castSucc M p) * a11nf_Rk k = 0 := by
    rw [Finset.sum_mul]
    exact Finset.sum_eq_zero fun p _ => a11nf_Am_mul_Rk hkj M p
  rw [a11nf_commute_one_add hR hR']

private theorem a11nf_coh_F0_Fk {G : Type} [Group G] {Φ : Fin 4 → SL 9 →* G}
    (hC : Coherent Φ) (k : Fin 3) :
    Φ 0 F0 = Φ k.castSucc (a11nf_Fk3 k) := by
  have h1 := hC 0 k.castSucc (pos 3 1) (pos 3 2) (by decide) (by decide) (by decide)
    (by fin_cases k <;> decide) (by fin_cases k <;> decide)
  have h2 := hC 0 k.castSucc (pos 3 2) (pos 3 1) (by decide) (by decide) (by decide)
    (by fin_cases k <;> decide) (by fin_cases k <;> decide)
  rw [F0, a11nf_Fk3]
  simp only [map_mul]
  rw [h1, h2]

private theorem a11nf_X8_coh {G : Type} [Group G] {Φ : Fin 4 → SL 9 →* G}
    (hC : Coherent Φ) {i j k : Fin 3} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (M : Matrix (Fin 3) (Fin 3) F2) {g : SL 9}
    (hg : ∀ a b, (g : Matrix (Fin 9) (Fin 9) F2) a b = (if a = b then 1 else 0) +
      (if blk (Fin.castLE (by omega) a) = i.castSucc ∧
          blk (Fin.castLE (by omega) b) = j.castSucc
        then M (idxIn (Fin.castLE (by omega) a)) (idxIn (Fin.castLE (by omega) b)) else 0)) :
    Φ 3 g = Φ k.castSucc g := by
  rw [a11nf_g_eq_prod hij M g hg]
  rw [map_list_prod, map_list_prod]
  refine a11nf_list_prod_congr (M := G) a11nf_L
    (f := Φ 3 ∘ fun p => a11nf_factor i.castSucc j.castSucc M p)
    (g := Φ k.castSucc ∘ fun p => a11nf_factor i.castSucc j.castSucc M p) (fun p _ => ?_)
  exact a11nf_factor_coh hC (by fin_cases k <;> decide) (by fin_cases i <;> decide)
    (by fin_cases j <;> decide) (fun h => hki (Fin.castSucc_injective _ h).symm)
    (fun h => hkj (Fin.castSucc_injective _ h).symm) M p

private theorem a11nf_centralizer_eq_of_zpowers_eq {G : Type} [Group G] {a b : G}
    (h : Subgroup.zpowers a = Subgroup.zpowers b) :
    Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({b} : Set G) := by
  ext g
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor <;> intro hg
  · have hb : b ∈ Subgroup.zpowers a := by rw [h]; exact Subgroup.mem_zpowers b
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hb
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx, ← hn]
    exact (Commute.zpow_left (hg a rfl) n).eq
  · have ha : a ∈ Subgroup.zpowers b := by rw [← h]; exact Subgroup.mem_zpowers a
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp ha
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx, ← hn]
    exact (Commute.zpow_left (hg b rfl) n).eq

private theorem a11nf_exists_third (i j : Fin 3) (hij : i ≠ j) :
    ∃ e : Fin 3, e ≠ i ∧ e ≠ j := by
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | exact ⟨0, by decide, by decide⟩
      | exact ⟨1, by decide, by decide⟩
      | exact ⟨2, by decide, by decide⟩

private theorem a11nf_T9'_zero : T9' (0 : Fin 4) = T9 0 := rfl
private theorem a11nf_T9'_one : T9' (1 : Fin 4) = T9 1 := rfl
private theorem a11nf_T9'_two : T9' (2 : Fin 4) = T9 2 := rfl

theorem a11NbrFrobInput_holds : A11NbrFrobInput := by
  intro hLB G instG instFin B Bs x L D J y K φ₃ f n Φ ρ hctx y' K' hnb c hc hz
  obtain ⟨hRest, hConfig, hFrame, hExtra, hCoh, hRho⟩ := hctx
  have hI : GGThmIHyp 7 B x L := hRest.1.1
  have hDJ : LargeEvenStdSub 7 B x L D J := hRest.1.2.2
  have hSStar : LargeEvenSStar 7 B x L := hI.2.2.2.2.2.2.1
  have hStd : LargeEvenStandardType 7 B x L := hI.2.2.2.2.2.2.2
  have hLcomp : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    hSStar.2.2.2.1
  have hJcomp : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hDJ.1.2.2.2.2.2.1
  have hGlue : A11GlueHyp φ₃ f n := hFrame.1
  have hφT9 : ∀ i : Fin 3, f i.castSucc = φ₃ (T9 i) := hGlue.2.1
  have hKcomp : CFSG.Assembly.IsComponentOf φ₃.range (Subgroup.centralizer ({f 3} : Set G)) :=
    hGlue.2.2.2.2.2.2.2
  have hnswap : ∀ l i, n l * f i * (n l)⁻¹ = f (Equiv.swap l 3 i) := hGlue.2.2.2.2.2.2.1
  have hφK : φ₃.range = K := hFrame.2.1
  have hxdef : x = f 0 * f 1 * f 2 * f 3 := hFrame.2.2.2.2.1
  have hJK : J ≤ K := hFrame.2.2.2.2.2.2.2.2.1
  have hJJ9 : J ≤ J9.map φ₃ := hFrame.2.2.2.2.2.2.2.2.2.1
  have hLgen : L ≤ Subgroup.closure ((J : Set G) ∪
      (J.map (MulAut.conj (n 2)).toMonoidHom : Set G)) := hFrame.2.2.2.2.2.2.2.2.2.2
  have h7J : 7 ∣ Nat.card J := hExtra.1
  have hΦ3 : Φ 3 = φ₃ := hCoh.1
  have hΦrange : ∀ l, (Φ l).range = φ₃.range.map (MulAut.conj (n l)).toMonoidHom := hCoh.2.2.1
  have hΦT9 : ∀ l k, k ≠ l → Φ l (T9' (Equiv.swap l 3 k)) = f k := hCoh.2.2.2.1
  have hCoherent : Coherent Φ := hCoh.2.2.2.2
  have hRhoClos : ∀ l, (Φ l).range ≤ Clos φ₃ ρ := by
    intro l
    have h := hRho.2.1 l
    simpa [hΦ3] using h
  have hf0 : f 0 = Φ 3 (T9 0) := by
    have h0 : f 0 = φ₃ (T9 0) := by simpa using hφT9 (0 : Fin 3)
    rw [h0, ← hΦ3]
  have hf1 : f 1 = Φ 0 (T9 1) := by
    have h := hΦT9 0 1 (show (1 : Fin 4) ≠ 0 from by decide)
    rw [show Equiv.swap (0 : Fin 4) 3 1 = 1 from by decide, a11nf_T9'_one] at h
    exact h.symm
  have hf2 : f 2 = Φ 0 (T9 2) := by
    have h := hΦT9 0 2 (show (2 : Fin 4) ≠ 0 from by decide)
    rw [show Equiv.swap (0 : Fin 4) 3 2 = 2 from by decide, a11nf_T9'_two] at h
    exact h.symm
  have hf3 : f 3 = Φ 0 (T9 0) := by
    have h := hΦT9 0 3 (show (3 : Fin 4) ≠ 0 from by decide)
    rw [show Equiv.swap (0 : Fin 4) 3 3 = 0 from by decide, a11nf_T9'_zero] at h
    exact h.symm
  let d : G := Φ 0 F0
  have hd3_eq : d * f 3 = f 3 ^ 2 * d := by
    have h := congrArg (Φ 0) a11nf_F0_T9_0
    simp only [map_mul, map_pow] at h
    rw [← hf3] at h
    simpa using h
  have hd1_eq : d * f 1 = f 1 * d := by
    have h := congrArg (Φ 0) a11nf_F0_T9_1
    simp only [map_mul] at h
    rw [← hf1] at h
    simpa using h
  have hd2_eq : d * f 2 = f 2 * d := by
    have h := congrArg (Φ 0) a11nf_F0_T9_2
    simp only [map_mul] at h
    rw [← hf2] at h
    simpa using h
  have hd3 : d * f 3 * d⁻¹ = f 3 ^ 2 := by
    calc d * f 3 * d⁻¹ = f 3 ^ 2 * d * d⁻¹ := by rw [hd3_eq]
      _ = f 3 ^ 2 := by group
  have hd1 : d * f 1 * d⁻¹ = f 1 := by
    calc d * f 1 * d⁻¹ = f 1 * d * d⁻¹ := by rw [hd1_eq]
      _ = f 1 := by group
  have hd2 : d * f 2 * d⁻¹ = f 2 := by
    calc d * f 2 * d⁻¹ = f 2 * d * d⁻¹ := by rw [hd2_eq]
      _ = f 2 := by group
  have hrange_0 : (Φ 0).range ≤ Subgroup.centralizer ({f 0} : Set G) := by
    calc (Φ 0).range = φ₃.range.map (MulAut.conj (n 0)).toMonoidHom := hΦrange 0
      _ ≤ (Subgroup.centralizer ({f 3} : Set G)).map (MulAut.conj (n 0)).toMonoidHom :=
          Subgroup.map_mono hKcomp.1
      _ = Subgroup.centralizer ({n 0 * f 3 * (n 0)⁻¹} : Set G) :=
          CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton (n 0) (f 3)
      _ = Subgroup.centralizer ({f 0} : Set G) := by
          rw [hnswap 0 3, show Equiv.swap (0 : Fin 4) 3 3 = 0 from by decide]
  have hd0 : d * f 0 * d⁻¹ = f 0 := by
    have hdmem : d ∈ Subgroup.centralizer ({f 0} : Set G) :=
      hrange_0 (show d ∈ (Φ 0).range from ⟨F0, rfl⟩)
    have hcomm : f 0 * d = d * f 0 := (Subgroup.mem_centralizer_iff.mp hdmem) (f 0) rfl
    calc d * f 0 * d⁻¹ = f 0 * d * d⁻¹ := by rw [← hcomm]
      _ = f 0 := by group
  have hconj3 : MulAut.conj d (f 3) = f 3 ^ 2 := by
    rw [MulAut.conj_apply]; exact hd3
  have hd_f3sq : d * f 3 ^ 2 * d⁻¹ = f 3 ^ 4 := by
    have h1 : d * f 3 ^ 2 * d⁻¹ = MulAut.conj d (f 3 ^ 2) := by rw [MulAut.conj_apply]
    rw [h1, map_pow, hconj3, ← pow_mul]
  have hd_x : d * x * d⁻¹ = ell f 2 := by
    rw [hxdef]
    calc d * (f 0 * f 1 * f 2 * f 3) * d⁻¹
        = (d * f 0 * d⁻¹) * (d * f 1 * d⁻¹) * (d * f 2 * d⁻¹) * (d * f 3 * d⁻¹) := by
          group
      _ = f 0 * f 1 * f 2 * f 3 ^ 2 := by rw [hd0, hd1, hd2, hd3]
      _ = ell f 2 := by
          rw [ell, show (2 : ZMod 7).val = 2 from by decide]
  have hd_ell2 : d * ell f 2 * d⁻¹ = ell f 4 := by
    have hLrhs : ell f 2 = f 0 * f 1 * f 2 * f 3 ^ 2 := by
      rw [ell, show (2 : ZMod 7).val = 2 from by decide]
    have hRrhs : ell f 4 = f 0 * f 1 * f 2 * f 3 ^ 4 := by
      rw [ell, show (4 : ZMod 7).val = 4 from by decide]
    rw [hLrhs, hRrhs]
    calc d * (f 0 * f 1 * f 2 * f 3 ^ 2) * d⁻¹
        = (d * f 0 * d⁻¹) * (d * f 1 * d⁻¹) * (d * f 2 * d⁻¹) * (d * f 3 ^ 2 * d⁻¹) := by
          group
      _ = f 0 * f 1 * f 2 * f 3 ^ 4 := by rw [hd0, hd1, hd2, hd_f3sq]
  have hxconj2 : MulAut.conj d x = ell f 2 := by
    rw [MulAut.conj_apply]; exact hd_x
  have hell2conj : MulAut.conj d (ell f 2) = ell f 4 := by
    rw [MulAut.conj_apply]; exact hd_ell2
  have hd2_x : d ^ 2 * x * (d ^ 2)⁻¹ = ell f 4 := by
    have h1 : d ^ 2 * x * (d ^ 2)⁻¹ = MulAut.conj (d ^ 2) x := by rw [MulAut.conj_apply]
    rw [h1, map_pow, pow_two, MulAut.mul_apply, hxconj2, hell2conj]
  have hdC : d ∈ Clos φ₃ ρ := by
    have h : d ∈ Clos (Φ 3) ρ := hRho.2.1 0 ⟨F0, rfl⟩
    simpa [hΦ3] using h
  have hJ2le : J ≤ φ₃.range := by rw [hφK]; exact hJK
  have hφ3Clos : φ₃.range ≤ Clos φ₃ ρ := by
    have h := hRhoClos 3
    simpa [← hΦ3] using h
  have hJClos : J ≤ Clos φ₃ ρ := hJ2le.trans hφ3Clos
  have hJn2Clos : J.map (MulAut.conj (n 2)).toMonoidHom ≤ Clos φ₃ ρ := by
    calc J.map (MulAut.conj (n 2)).toMonoidHom
        ≤ φ₃.range.map (MulAut.conj (n 2)).toMonoidHom := Subgroup.map_mono hJ2le
      _ = (Φ 2).range := (hΦrange 2).symm
      _ ≤ Clos φ₃ ρ := hRhoClos 2
  have hLClos : L ≤ Clos φ₃ ρ := by
    have hclosure_le : Subgroup.closure ((J : Set G) ∪
        (J.map (MulAut.conj (n 2)).toMonoidHom : Set G)) ≤ Clos φ₃ ρ := by
      rw [Subgroup.closure_le]
      intro z hzmem
      rw [Set.mem_union] at hzmem
      rcases hzmem with hzm | hzm
      · exact hJClos hzm
      · exact hJn2Clos hzm
    exact hLgen.trans hclosure_le
  have hGJ_cent : GJ.map φ₃ ≤ Subgroup.centralizer ({d} : Set G) := by
    rw [GJ, MonoidHom.map_closure, Subgroup.closure_le]
    intro z hzmem
    obtain ⟨g, hgs, rfl⟩ := hzmem
    obtain ⟨i, j, hij, hgX8⟩ := hgs
    change φ₃ g ∈ Subgroup.centralizer ({d} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    obtain ⟨M, hM, hg⟩ := hgX8
    obtain ⟨e, hei, hej⟩ := a11nf_exists_third i j hij
    have hXcoh : Φ 3 g = Φ e.castSucc g := a11nf_X8_coh hCoherent hij hei hej M hg
    have hdFk : d = Φ e.castSucc (a11nf_Fk3 e) := a11nf_coh_F0_Fk hCoherent e
    have hcomm : a11nf_Fk3 e * g = g * a11nf_Fk3 e :=
      a11nf_Fk_comm hei hej M (a11nf_X8_coe hg)
    have hcomm_d : d * Φ 3 g = Φ 3 g * d := by
      calc d * Φ 3 g
          = Φ e.castSucc (a11nf_Fk3 e) * Φ e.castSucc g := by rw [hdFk, hXcoh]
        _ = Φ e.castSucc (a11nf_Fk3 e * g) := by rw [map_mul]
        _ = Φ e.castSucc (g * a11nf_Fk3 e) := by rw [hcomm]
        _ = Φ e.castSucc g * Φ e.castSucc (a11nf_Fk3 e) := by rw [map_mul]
        _ = Φ 3 g * d := by rw [← hXcoh, ← hdFk]
    simpa only [hΦ3] using hcomm_d
  have hJGJ : J ≤ GJ.map φ₃ := hJJ9.trans (Subgroup.map_mono a11J9GenInput_holds)
  have hdJ : J ≤ Subgroup.centralizer ({d} : Set G) := hJGJ.trans hGJ_cent
  have hpowC_all : ∀ e : ℕ, d ^ e ∈ Clos φ₃ ρ := by
    intro e
    induction e with
    | zero => simpa using Subgroup.one_mem (Clos φ₃ ρ)
    | succ n ih => rw [pow_succ]; exact Subgroup.mul_mem _ ih hdC
  have hbase : ∀ (e : ℕ) (c : ZMod 7), d ^ e * x * (d ^ e)⁻¹ = ell f c →
      Subgroup.zpowers y' = Subgroup.zpowers (ell f c) → K' ≤ Clos φ₃ ρ := by
    intro e c hxconj hzc
    have hpowC : d ^ e ∈ Clos φ₃ ρ := hpowC_all e
    have hJe : J ≤ Subgroup.centralizer ({d ^ e} : Set G) := by
      intro j hj
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      have hdj : d * j = j * d := (Subgroup.mem_centralizer_iff.mp (hdJ hj)) d rfl
      exact (Commute.pow_left hdj e).eq
    have hLpow : L.map (MulAut.conj (d ^ e)).toMonoidHom ≤ Clos φ₃ ρ := by
      intro z hzmem
      obtain ⟨l, hl, rfl⟩ := hzmem
      change MulAut.conj (d ^ e) l ∈ Clos φ₃ ρ
      rw [MulAut.conj_apply]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hpowC (hLClos hl))
        (Subgroup.inv_mem _ hpowC)
    have hLcomp' : CFSG.Assembly.IsComponentOf (L.map (MulAut.conj (d ^ e)).toMonoidHom)
        (Subgroup.centralizer ({y'} : Set G)) := by
      have hmap := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hLcomp (d ^ e)
      have hcent : (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj (d ^ e)).toMonoidHom =
          Subgroup.centralizer ({y'} : Set G) := by
        rw [CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton (d ^ e) x, hxconj,
          a11nf_centralizer_eq_of_zpowers_eq hzc.symm]
      rwa [hcent] at hmap
    have hK'comp : CFSG.Assembly.IsComponentOf K' (Subgroup.centralizer ({y'} : Set G)) :=
      (isComponentOf_of_isNeighborOf hStd (isNeighborOf_of_ggNbr hDJ hnb)).1
    have hJleL : J ≤ L := hJcomp.1.trans inf_le_left
    have hJleLpow : J ≤ L.map (MulAut.conj (d ^ e)).toMonoidHom := by
      intro j hj
      refine ⟨j, hJleL hj, ?_⟩
      change MulAut.conj (d ^ e) j = j
      rw [MulAut.conj_apply]
      have hdj : d ^ e * j = j * d ^ e :=
        (Subgroup.mem_centralizer_iff.mp (hJe hj)) (d ^ e) rfl
      rw [hdj, mul_assoc, mul_inv_cancel, mul_one]
    have hJleK' : J ≤ K' := le_of_ggNbr hLB hI hDJ h7J hnb
    have hJq := hJcomp.2.2
    have hEq : L.map (MulAut.conj (d ^ e)).toMonoidHom = K' :=
      CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_of_le hJq hLcomp' hK'comp
        hJleLpow hJleK'
    rw [← hEq]
    exact hLpow
  rcases hc with hc2 | hc4
  · rw [hc2] at hz
    exact hbase 1 2 (by simpa using hd_x) hz
  · rw [hc4] at hz
    exact hbase 2 4 hd2_x hz

end CFSG.StandardType.A11

end
