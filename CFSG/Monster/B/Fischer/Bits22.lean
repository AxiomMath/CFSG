module

public import CFSG.Monster.B.Classical.Derived22Coordinates
public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.Code CFSG.Monster.B.Classical.Mog22 CFSG.Monster.B.Classical.Plane

theorem two_le_of_mem_X₀ (i : X₀) : 2 ≤ ((i : Fin 24) : ℕ) := by
  have := i.2
  simp only [X₀, Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact this

@[expose] def pos (i : X₀) : Fin 22 :=
  ⟨((i : Fin 24) : ℕ) - 2, by have := ((i : Fin 24)).2; omega⟩

@[expose] def coordAt (t : Fin 22) : X₀ :=
  ⟨⟨(t : ℕ) + 2, by omega⟩, by simp [X₀]⟩

theorem coordAt_pos (i : X₀) : coordAt (pos i) = i := by
  have := two_le_of_mem_X₀ i
  apply Subtype.ext; apply Fin.ext
  simp only [coordAt, pos]
  omega

theorem pos_coordAt (t : Fin 22) : pos (coordAt t) = t := by
  apply Fin.ext
  simp [pos, coordAt]

@[expose] def posEquiv : X₀ ≃ Fin 22 where
  toFun := pos
  invFun := coordAt
  left_inv := coordAt_pos
  right_inv := pos_coordAt

theorem card_V₀ : Nat.card V₀ = 2 ^ 22 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_coe, card_X₀]

@[expose] def vecOf (m : ℕ) : V₀ := fun i => if m.testBit (pos i) then 1 else 0

theorem vecOf_apply (m : ℕ) (i : X₀) : vecOf m i = if m.testBit (pos i) then 1 else 0 := rfl

theorem vecOf_zero : vecOf 0 = 0 := by
  funext i; simp [vecOf]

theorem vecOf_xor (a b : ℕ) : vecOf (a ^^^ b) = vecOf a + vecOf b := by
  funext i
  simp only [vecOf, Nat.testBit_xor, Pi.add_apply]
  cases a.testBit (pos i) <;> cases b.testBit (pos i) <;> decide

theorem vecOf_two_pow (t : Fin 22) : vecOf (2 ^ (t : ℕ)) = e (coordAt t) := by
  funext i
  have key : ((t : ℕ) = (pos i : ℕ)) ↔ i = coordAt t := by
    constructor
    · intro h
      rw [← coordAt_pos i]
      exact congrArg coordAt (Fin.ext h.symm)
    · rintro rfl
      rw [pos_coordAt]
  simp only [vecOf, Nat.testBit_two_pow, e, Pi.single_apply, decide_eq_true_eq]
  by_cases h : i = coordAt t <;> simp [h, key, pos_coordAt]

theorem vecOf_coordAt (m : ℕ) (t : Fin 22) :
    vecOf m (coordAt t) = if m.testBit t then 1 else 0 := by
  rw [vecOf_apply, pos_coordAt]

theorem vecOf_inj {a b : ℕ} (ha : a < 2 ^ 22) (hb : b < 2 ^ 22) (h : vecOf a = vecOf b) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < 22
  · have := congrFun h (coordAt ⟨t, ht⟩)
    rw [vecOf_coordAt, vecOf_coordAt] at this
    cases ha' : a.testBit t <;> cases hb' : b.testBit t <;> simp_all
  · rw [Nat.testBit_eq_false_of_lt (ha.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_eq_false_of_lt (hb.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem vecOf_surj (v : V₀) : ∃ m < 2 ^ 22, vecOf m = v := by
  have hinj : Function.Injective fun m : Fin (2 ^ 22) => vecOf m := fun a b h =>
    Fin.ext (vecOf_inj a.2 b.2 h)
  have hbij := hinj.bijective_of_nat_card_le (by rw [card_V₀, Nat.card_eq_fintype_card,
    Fintype.card_fin])
  obtain ⟨m, hm⟩ := hbij.2 v
  exact ⟨m, m.2, hm⟩

theorem blockVec_ofMask (b : ℕ) : blockVec (ofMask b) = vecOf (b >>> 2) := by
  funext i
  rw [blockVec_apply, vecOf_apply, Nat.testBit_shiftRight]
  have := two_le_of_mem_X₀ i
  have e : 2 + ((pos i : Fin 22) : ℕ) = ((i : Fin 24) : ℕ) := by simp only [pos]; omega
  rw [e]
  simp [ofMask]

@[expose] def xorSel (sel : ℕ → Bool) (cols : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => xorSel sel cols n ^^^ (if sel n then cols n else 0)

theorem vecOf_xorSel (sel : ℕ → Bool) (cols : ℕ → ℕ) (n : ℕ) :
    vecOf (xorSel sel cols n) = ∑ t : Fin n, if sel t then vecOf (cols t) else 0 := by
  induction n with
  | zero => simp [xorSel, vecOf_zero]
  | succ n ih =>
    rw [xorSel, vecOf_xor, ih, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    congr 1
    split_ifs <;> simp [vecOf_zero]

theorem xorSel_lt (sel : ℕ → Bool) {cols : ℕ → ℕ} {k : ℕ} (h : ∀ t, cols t < 2 ^ k) (n : ℕ) :
    xorSel sel cols n < 2 ^ k := by
  induction n with
  | zero => exact Nat.two_pow_pos k
  | succ n ih =>
    rw [xorSel]
    refine Nat.xor_lt_two_pow ih ?_
    split_ifs
    · exact h n
    · exact Nat.two_pow_pos k

theorem xorSel_xor (sel sel' : ℕ → Bool) (cols : ℕ → ℕ) (n : ℕ) :
    xorSel (fun t => sel t ^^ sel' t) cols n = xorSel sel cols n ^^^ xorSel sel' cols n := by
  induction n with
  | zero => simp [xorSel]
  | succ n ih =>
    rw [xorSel, xorSel, xorSel, ih]
    cases sel n <;> cases sel' n <;> simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]

theorem vecOf_eq_sum (m : ℕ) :
    vecOf m = ∑ t : Fin 22, if m.testBit t then vecOf (2 ^ (t : ℕ)) else 0 := by
  funext i
  rw [Finset.sum_apply]
  simp only [apply_ite (fun v : V₀ => v i), Pi.zero_apply, vecOf_apply, Nat.testBit_two_pow]
  rw [Finset.sum_eq_single (pos i)]
  · simp
  · intro t _ ht
    have : ¬((t : ℕ) = (pos i : ℕ)) := fun h => ht (Fin.ext h)
    simp [this]
  · simp

theorem map_vecOf {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (L : V₀ →ₗ[ZMod 2] M)
    (F : ℕ → M) (hF : ∀ a b, F (a ^^^ b) = F a + F b) (hF0 : F 0 = 0) {cols : ℕ → ℕ}
    (h : ∀ t : Fin 22, L (vecOf (2 ^ (t : ℕ))) = F (cols t)) (m : ℕ) :
    L (vecOf m) = F (xorSel m.testBit cols 22) := by
  have key : ∀ n, F (xorSel m.testBit cols n) = ∑ t : Fin n, if m.testBit t then F (cols t)
      else 0 := by
    intro n
    induction n with
    | zero => simp [xorSel, hF0]
    | succ n ih =>
      rw [xorSel, hF, ih, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      congr 1
      split_ifs <;> simp [hF0]
  rw [key, vecOf_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs
  · exact h t
  · exact map_zero L

@[expose] def IsEchelon (k : ℕ) (piv row : ℕ → ℕ) : Prop :=
  (∀ l < k, row l < 2 ^ 22) ∧ (∀ l < k, piv l < 22) ∧
    ∀ l < k, ∀ l' < k, (row l).testBit (piv l') = decide (l = l')

@[expose] def red (k : ℕ) (piv row : ℕ → ℕ) (m : ℕ) : ℕ :=
  m ^^^ xorSel (fun l => m.testBit (piv l)) row k

@[expose] noncomputable def spanRows (k : ℕ) (row : ℕ → ℕ) : Submodule (ZMod 2) V₀ :=
  Submodule.span (ZMod 2) (Set.range fun l : Fin k => vecOf (row l))

variable {k : ℕ} {piv row : ℕ → ℕ}

theorem red_lt (hE : IsEchelon k piv row) {m : ℕ} (hm : m < 2 ^ 22) : red k piv row m < 2 ^ 22 :=
  Nat.xor_lt_two_pow hm (by
    have : ∀ n ≤ k, xorSel (fun l => m.testBit (piv l)) row n < 2 ^ 22 := by
      intro n hn
      induction n with
      | zero => exact Nat.two_pow_pos 22
      | succ n ih =>
        rw [xorSel]
        refine Nat.xor_lt_two_pow (ih (by omega)) ?_
        split_ifs
        · exact hE.1 n (by omega)
        · exact Nat.two_pow_pos 22
    exact this k le_rfl)

theorem vecOf_row_mem (l : Fin k) : vecOf (row l) ∈ spanRows k row :=
  Submodule.subset_span ⟨l, rfl⟩

theorem vecOf_xorSel_mem (sel : ℕ → Bool) (n : ℕ) (hn : n ≤ k) :
    vecOf (xorSel sel row n) ∈ spanRows k row := by
  rw [vecOf_xorSel]
  refine Submodule.sum_mem _ fun t _ => ?_
  split_ifs
  · exact vecOf_row_mem ⟨t, by omega⟩
  · exact Submodule.zero_mem _

theorem vecOf_red_add_mem (m : ℕ) :
    vecOf (red k piv row m) + vecOf m ∈ spanRows k row := by
  rw [red, vecOf_xor, add_comm, ← add_assoc, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl,
    zero_smul, zero_add]
  exact vecOf_xorSel_mem _ k le_rfl

theorem coord_piv (hE : IsEchelon k piv row) (c : Fin k → ZMod 2) (l' : Fin k) :
    (∑ l, c l • vecOf (row l)) (coordAt ⟨piv l', hE.2.1 l' l'.2⟩) = c l' := by
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, vecOf_coordAt, smul_eq_mul]
  rw [Finset.sum_eq_single l']
  · rw [hE.2.2 l' l'.2 l' l'.2]; simp
  · intro l _ hl
    rw [hE.2.2 l l.2 l' l'.2]
    have : (l : ℕ) ≠ l' := fun h => hl (Fin.ext h)
    simp [this]
  · simp

theorem linearIndependent_rows (hE : IsEchelon k piv row) :
    LinearIndependent (ZMod 2) fun l : Fin k => vecOf (row l) := by
  refine (Fintype.linearIndependent_iff (R := ZMod 2) (M := V₀)
    (v := fun l : Fin k => vecOf (row l))).2 fun c hc l' => ?_
  have h1 := coord_piv hE c l'
  have h2 := congrFun hc (coordAt ⟨piv l', hE.2.1 l' l'.2⟩)
  exact h1.symm.trans h2

theorem finrank_spanRows (hE : IsEchelon k piv row) :
    Module.finrank (ZMod 2) (spanRows k row) = k := by
  rw [spanRows, finrank_span_eq_card (linearIndependent_rows hE), Fintype.card_fin]

theorem vecOf_mem_span_iff (hE : IsEchelon k piv row) {m : ℕ} (hm : m < 2 ^ 22) :
    vecOf m ∈ spanRows k row ↔ red k piv row m = 0 := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 h
    have hsel : ∀ l : Fin k, (if m.testBit (piv l) then (1 : ZMod 2) else 0) = c l := by
      intro l
      have := coord_piv hE c l
      rw [hc, vecOf_coordAt] at this
      exact this
    apply vecOf_inj (red_lt hE hm) (Nat.two_pow_pos 22)
    rw [vecOf_zero, red, vecOf_xor, vecOf_xorSel, ← hc]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← hsel l]
    split_ifs <;> simp [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl]
  · intro h
    have := vecOf_red_add_mem (k := k) (piv := piv) (row := row) m
    rwa [h, vecOf_zero, zero_add] at this

end CFSG.Monster.B.Fischer
