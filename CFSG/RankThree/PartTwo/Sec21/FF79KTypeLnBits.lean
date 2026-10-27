module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.TLn

open Matrix

@[expose] def bz (x j : ℕ) : ZMod 2 := if x.testBit j then 1 else 0

@[expose] def rowmul : ℕ → List ℕ → ℕ
  | _, [] => 0
  | x, y :: Y => (y * (x % 2)) ^^^ rowmul (x / 2) Y

@[expose] def mulB (X Y : List ℕ) : List ℕ := X.map (rowmul · Y)

@[expose] def idB (n : ℕ) : List ℕ := (List.range n).map (2 ^ ·)

@[expose] def toM (n : ℕ) (X : List ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j => bz (X.getD i 0) j

@[expose] def Bd (n : ℕ) (X : List ℕ) : Prop := X.length = n ∧ ∀ x ∈ X, x < 2 ^ n

@[expose] def sqmulAux (X : List ℕ) : List ℕ → List Bool → List ℕ
  | acc, [] => acc
  | acc, b :: bs => sqmulAux X (if b then mulB (mulB acc acc) X else mulB acc acc) bs

@[expose] def bsVal : ℕ → List Bool → ℕ
  | v, [] => v
  | v, b :: bs => bsVal (2 * v + (if b then 1 else 0)) bs

@[expose] def sqmul (X : List ℕ) (bs : List Bool) : List ℕ := sqmulAux X X bs

@[expose] def chk (n : ℕ) (bs : List Bool) (W : List (List ℕ × List ℕ)) (X : List ℕ) : Bool :=
  sqmul X bs != idB n || X == idB n || W.any fun p =>
    sqmul (mulB X (mulB (mulB p.1 X) p.2)) bs != idB n

theorem bz_xor (a b j : ℕ) : bz (a ^^^ b) j = bz a j + bz b j := by
  unfold bz
  rw [Nat.testBit_xor]
  cases a.testBit j <;> cases b.testBit j <;> decide

theorem bz_zero (j : ℕ) : bz 0 j = 0 := by simp [bz]

theorem bz_mul_mod (y x j : ℕ) : bz (y * (x % 2)) j = bz x 0 * bz y j := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h
  · have : x.testBit 0 = false := by rw [Nat.testBit_zero]; simp [h]
    simp [h, bz, this]
  · have : x.testBit 0 = true := by rw [Nat.testBit_zero]; simp [h]
    simp [h, bz, this]

theorem bz_div_two (x k : ℕ) : bz (x / 2) k = bz x (k + 1) := by
  simp [bz, Nat.testBit_succ]

theorem rowmul_bz : ∀ (Y : List ℕ) (x j : ℕ),
    bz (rowmul x Y) j = ∑ k : Fin Y.length, bz x k * bz (Y.get k) j
  | [], x, j => by simp [rowmul, bz_zero]
  | y :: Y, x, j => by
    rw [rowmul, bz_xor, rowmul_bz Y, bz_mul_mod]
    refine Eq.trans ?_ (Fin.sum_univ_succ (n := Y.length)
      (fun k : Fin (Y.length + 1) => bz x k * bz ((y :: Y).get k) j)).symm
    simp [bz_div_two]

theorem rowmul_zero (Y : List ℕ) : rowmul 0 Y = 0 := by
  induction Y with
  | nil => rfl
  | cons y Y ih => simp [rowmul, ih]

theorem length_mulB (X Y : List ℕ) : (mulB X Y).length = X.length := by simp [mulB]

theorem getD_mulB (X Y : List ℕ) (i : ℕ) : (mulB X Y).getD i 0 = rowmul (X.getD i 0) Y := by
  unfold mulB
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases X[i]? <;> simp [rowmul_zero]

theorem mulB_toM {n : ℕ} {X Y : List ℕ} (hY : Y.length = n) :
    toM n (mulB X Y) = toM n X * toM n Y := by
  subst hY
  ext i j
  simp only [toM, of_apply, Matrix.mul_apply, getD_mulB, rowmul_bz]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [List.getD_eq_getElem _ _ k.2]
  rfl

theorem Bd_mulB {n : ℕ} {X Y : List ℕ} (hX : Bd n X) (hY : Bd n Y) : Bd n (mulB X Y) := by
  have key : ∀ (Y : List ℕ) (x : ℕ), (∀ y ∈ Y, y < 2 ^ n) → rowmul x Y < 2 ^ n := by
    intro Y
    induction Y with
    | nil => intro x _; simp [rowmul]
    | cons y Y ih =>
      intro x h
      simp only [rowmul]
      refine Nat.xor_lt_two_pow ?_ (ih _ fun z hz => h z (List.mem_cons_of_mem _ hz))
      rcases Nat.mod_two_eq_zero_or_one x with hx | hx
      · simp [hx]
      · simpa [hx] using h y (List.mem_cons_self ..)
  refine ⟨by rw [length_mulB]; exact hX.1, ?_⟩
  intro z hz
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp hz
  exact key Y x hY.2

theorem Bd_idB (n : ℕ) : Bd n (idB n) := by
  refine ⟨by simp [idB], ?_⟩
  intro z hz
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
  exact Nat.pow_lt_pow_right (by norm_num) (List.mem_range.mp hi)

theorem toM_idB (n : ℕ) : toM n (idB n) = 1 := by
  ext i j
  simp only [toM, of_apply, Matrix.one_apply, bz]
  have : (idB n).getD i 0 = 2 ^ (i : ℕ) := by
    simp [idB, List.getD_eq_getElem _ _ (show (i : ℕ) < (idB n).length by simp [idB])]
  rw [this, Nat.testBit_two_pow]
  by_cases h : i = j
  · subst h; simp
  · have : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
    simp [h, this]

theorem toM_inj {n : ℕ} {X Y : List ℕ} (hX : Bd n X) (hY : Bd n Y)
    (h : toM n X = toM n Y) : X = Y := by
  refine List.ext_getElem (hX.1.trans hY.1.symm) fun i hi hi' => ?_
  refine Nat.eq_of_testBit_eq fun j => ?_
  by_cases hj : j < n
  · have := congrFun (congrFun h ⟨i, hX.1 ▸ hi⟩) ⟨j, hj⟩
    simp only [toM, of_apply, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at this
    unfold bz at this
    cases h1 : X[i].testBit j <;> cases h2 : Y[i].testBit j <;> simp_all
  · have h1 : X[i] < 2 ^ n := hX.2 _ (List.getElem_mem hi)
    have h2 : Y[i] < 2 ^ n := hY.2 _ (List.getElem_mem hi')
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num)
      (not_lt.mp hj))), Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h2
      (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hj)))]

theorem sqmulAux_spec {n : ℕ} {X : List ℕ} (hX : Bd n X) :
    ∀ (bs : List Bool) (acc : List ℕ) (k : ℕ), Bd n acc → toM n acc = toM n X ^ k →
      Bd n (sqmulAux X acc bs) ∧ toM n (sqmulAux X acc bs) = toM n X ^ bsVal k bs
  | [], acc, k, h1, h2 => ⟨h1, h2⟩
  | b :: bs, acc, k, h1, h2 => by
    simp only [sqmulAux, bsVal]
    cases b
    · simp only [Bool.false_eq_true, if_false]
      refine sqmulAux_spec hX bs _ (2 * k + 0) (Bd_mulB h1 h1) ?_
      rw [mulB_toM h1.1, h2, ← pow_add]; ring_nf
    · simp only [if_true]
      refine sqmulAux_spec hX bs _ (2 * k + 1) (Bd_mulB (Bd_mulB h1 h1) hX) ?_
      rw [mulB_toM hX.1, mulB_toM h1.1, h2, ← pow_add, ← pow_succ]; ring_nf

theorem sqmul_spec {n : ℕ} {X : List ℕ} (hX : Bd n X) (bs : List Bool) :
    Bd n (sqmul X bs) ∧ toM n (sqmul X bs) = toM n X ^ bsVal 1 bs :=
  sqmulAux_spec hX bs X 1 hX (by rw [pow_one])

theorem chk_sound {n : ℕ} {bs : List Bool} {W : List (List ℕ × List ℕ)} {X : List ℕ}
    (hW : ∀ p ∈ W, Bd n p.1 ∧ Bd n p.2) (hX : Bd n X)
    (hpow : toM n X ^ bsVal 1 bs = 1) (h : chk n bs W X = true) :
    toM n X = 1 ∨ ∃ p ∈ W, Bd n p.1 ∧ Bd n p.2 ∧
      (toM n X * (toM n p.1 * toM n X * toM n p.2)) ^ bsVal 1 bs ≠ 1 := by
  obtain ⟨hb, hm⟩ := sqmul_spec hX bs
  have hid : sqmul X bs = idB n :=
    toM_inj hb (Bd_idB n) (by rw [hm, hpow, toM_idB])
  simp only [chk, hid, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, beq_iff_eq,
    List.any_eq_true] at h
  rcases h with h | ⟨p, hp, hp'⟩
  · left; rw [h, toM_idB]
  · right
    refine ⟨p, hp, (hW p hp).1, (hW p hp).2, fun hone => ?_⟩
    have h1 : Bd n (mulB X (mulB (mulB p.1 X) p.2)) :=
      Bd_mulB hX (Bd_mulB (Bd_mulB (hW p hp).1 hX) (hW p hp).2)
    obtain ⟨hb2, hm2⟩ := sqmul_spec h1 bs
    have hl1 : (mulB p.1 X).length = n := by rw [length_mulB]; exact (hW p hp).1.1
    have hl2 : (mulB (mulB p.1 X) p.2).length = n := by rw [length_mulB]; exact hl1
    have hmP : toM n (mulB X (mulB (mulB p.1 X) p.2)) =
        toM n X * (toM n p.1 * toM n X * toM n p.2) := by
      rw [mulB_toM hl2, mulB_toM (hW p hp).2.1, mulB_toM hX.1]
    rw [hmP] at hm2
    simp only [bne_iff_ne, ne_eq] at hp'
    exact hp' (toM_inj hb2 (Bd_idB n) (by rw [hm2, hone, toM_idB]))

end CFSG.RankThree.PartTwo.Sec21.FF79.TLn
