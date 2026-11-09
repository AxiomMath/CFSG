module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop
public import CFSG.Permutation.FinPackWalk

public section

namespace CFSG.Quasithin

namespace LRed4L

open Equiv

abbrev V8 : Type := Fin 8 → ZMod 2

@[expose] def pv (σ : Perm (Fin 8)) (x : V8) : V8 := fun i => x (σ⁻¹ i)

@[expose] def nrm (x : V8) : V8 := fun i => x i + x 0

@[expose] def wt8 (x : V8) : ℕ := ∑ i, (x i).val

@[expose] def qP8 (x : V8) : ZMod 2 := ((wt8 x / 2 : ℕ) : ZMod 2)

@[expose] def isNE (x : V8) : Prop := x 0 = 0 ∧ ∑ i, x i = 0

instance : DecidablePred isNE := fun x => by unfold isNE; infer_instance

@[expose] def act (σ : Perm (Fin 8)) (x : V8) : V8 := nrm (pv σ x)

theorem two_add_self (c : ZMod 2) : c + c = 0 := by revert c; decide

theorem pv_one (x : V8) : pv 1 x = x := by
  funext i; simp [pv]

theorem pv_mul (σ τ : Perm (Fin 8)) (x : V8) : pv (σ * τ) x = pv σ (pv τ x) := by
  funext i; simp [pv, mul_inv_rev, Perm.mul_apply]

theorem pv_add (σ : Perm (Fin 8)) (x y : V8) : pv σ (x + y) = pv σ x + pv σ y := by
  funext i; simp [pv]

theorem nrm_add (x y : V8) : nrm (x + y) = nrm x + nrm y := by
  funext i; simp only [nrm, Pi.add_apply]; ring

theorem nrm_of_zero (x : V8) (h : x 0 = 0) : nrm x = x := by
  funext i; simp [nrm, h]

theorem nrm_pv_nrm (σ : Perm (Fin 8)) (x : V8) : nrm (pv σ (nrm x)) = nrm (pv σ x) := by
  funext i
  simp only [nrm, pv]
  have := two_add_self (x 0)
  calc x (σ⁻¹ i) + x 0 + (x (σ⁻¹ 0) + x 0) = x (σ⁻¹ i) + x (σ⁻¹ 0) + (x 0 + x 0) := by ring
    _ = x (σ⁻¹ i) + x (σ⁻¹ 0) := by rw [this, add_zero]

theorem act_one (x : V8) (h : x 0 = 0) : act 1 x = x := by
  unfold act; rw [pv_one, nrm_of_zero x h]

theorem act_mul (σ τ : Perm (Fin 8)) (x : V8) : act (σ * τ) x = act σ (act τ x) := by
  unfold act; rw [nrm_pv_nrm, pv_mul]

theorem act_add (σ : Perm (Fin 8)) (x y : V8) : act σ (x + y) = act σ x + act σ y := by
  unfold act; rw [pv_add, nrm_add]

theorem act_zero_apply (σ : Perm (Fin 8)) (x : V8) : act σ x 0 = 0 := by
  simp [act, nrm, two_add_self]

theorem act_zero (σ : Perm (Fin 8)) : act σ 0 = 0 := by
  funext i; simp [act, nrm, pv]

theorem act_inv_act (σ : Perm (Fin 8)) (x : V8) (h : x 0 = 0) : act σ⁻¹ (act σ x) = x := by
  rw [← act_mul, inv_mul_cancel, act_one x h]

theorem act_act_inv (σ : Perm (Fin 8)) (x : V8) (h : x 0 = 0) : act σ (act σ⁻¹ x) = x := by
  rw [← act_mul, mul_inv_cancel, act_one x h]

abbrev Wd : Type := List (Fin 8 × Fin 8)

@[expose] def pvSwap (a b : Fin 8) (x : V8) : V8 := fun i => x (if i = a then b else if i = b then a else i)

@[expose] def pvW : Wd → V8 → V8
  | [], x => x
  | p :: w, x => pvSwap p.1 p.2 (pvW w x)

@[expose] def permW : Wd → Perm (Fin 8)
  | [] => 1
  | p :: w => Equiv.swap p.1 p.2 * permW w

theorem pv_swap (a b : Fin 8) (x : V8) : pv (Equiv.swap a b) x = pvSwap a b x := by
  funext i; simp [pv, pvSwap, Equiv.swap_apply_def]

theorem pv_permW (w : Wd) (x : V8) : pv (permW w) x = pvW w x := by
  induction w with
  | nil => simp [permW, pvW, pv_one]
  | cons p w ih => rw [permW, pvW, pv_mul, ih, pv_swap]

@[expose, irreducible] def stepL (gs : List Wd) (K : Finset V8) : Finset V8 :=
  K ∪ (gs.map fun g => K.image fun x => nrm (pvW g x)).foldr (· ∪ ·) ∅

@[expose] def bfsL (gs : List Wd) (x0 : V8) : ℕ → Finset V8
  | 0 => {x0}
  | k+1 => stepL gs (bfsL gs x0 k)

theorem mem_foldr_union (l : List (Finset V8)) (p : V8) :
    p ∈ l.foldr (· ∪ ·) ∅ ↔ ∃ s ∈ l, p ∈ s := by
  induction l with
  | nil => simp
  | cons s l ih => simp [ih]

theorem mem_stepL {gs : List Wd} {K : Finset V8} {p : V8} :
    p ∈ stepL gs K ↔ p ∈ K ∨ ∃ g ∈ gs, ∃ x ∈ K, p = nrm (pvW g x) := by
  unfold stepL
  rw [Finset.mem_union, mem_foldr_union]
  constructor
  · rintro (h | ⟨s, hs, hp⟩)
    · exact Or.inl h
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hs
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
      exact Or.inr ⟨g, hg, x, hx, rfl⟩
  · rintro (h | ⟨g, hg, x, hx, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨_, List.mem_map.2 ⟨g, hg, rfl⟩, Finset.mem_image.2 ⟨x, hx, rfl⟩⟩

theorem bfsL_sound (gs : List Wd) (Q : Perm (Fin 8) → Prop) (hQ1 : Q 1)
    (hQ : ∀ g ∈ gs, ∀ σ, Q σ → Q (permW g * σ)) (x0 : V8) (h0 : x0 0 = 0) :
    ∀ k, ∀ p ∈ bfsL gs x0 k, ∃ σ, Q σ ∧ act σ x0 = p := by
  intro k
  induction k with
  | zero =>
    intro p hp
    have hp' : p = x0 := by simpa [bfsL] using hp
    exact ⟨1, hQ1, by rw [hp']; exact act_one x0 h0⟩
  | succ k ih =>
    intro p hp
    rw [bfsL, mem_stepL] at hp
    rcases hp with hp | ⟨g, hg, x, hx, rfl⟩
    · exact ih p hp
    · obtain ⟨σ, hσ, rfl⟩ := ih x hx
      refine ⟨permW g * σ, hQ g hg σ hσ, ?_⟩
      rw [act_mul]
      show nrm (pv (permW g) (act σ x0)) = _
      rw [pv_permW]

@[expose, irreducible] def Sing : Finset V8 := Finset.univ.filter fun x => isNE x ∧ x ≠ 0 ∧ qP8 x = 0

@[expose, irreducible] def NS : Finset V8 := Finset.univ.filter fun x => isNE x ∧ qP8 x = 1

theorem mem_Sing {x : V8} : x ∈ Sing ↔ isNE x ∧ x ≠ 0 ∧ qP8 x = 0 := by simp [Sing]

theorem mem_NS {x : V8} : x ∈ NS ↔ isNE x ∧ qP8 x = 1 := by simp [NS]

@[expose] def gensAll : List Wd := [[(0,1)], [(1,2)], [(2,3)], [(3,4)], [(4,5)], [(5,6)], [(6,7)]]

@[expose] def gensStab : List Wd :=
  [[(0,1)], [(1,2)], [(2,3)], [(4,5)], [(5,6)], [(6,7)], [(0,4),(1,5),(2,6),(3,7)]]

@[expose] def a0 : V8 := ![0,0,0,0,1,1,1,1]
@[expose] def b0 : V8 := ![0,0,1,1,0,0,1,1]
@[expose] def nsRoot : V8 := ![0,0,0,0,0,0,1,1]

@[expose] def basis6 : Fin 6 → V8 := ![![0, 0, 1, 1, 1, 0, 1, 0], ![0, 0, 1, 1, 1, 1, 0, 0], ![0, 1, 1, 0, 1, 0, 0, 1],
  ![0, 1, 0, 1, 1, 0, 1, 0], ![0, 1, 1, 1, 0, 0, 0, 1], ![0, 0, 0, 1, 1, 1, 0, 1]]

@[expose, irreducible] def stepK (K : Finset V8) : Finset V8 :=
  K ∪ (((K ×ˢ K).filter fun pq => pq.1 ≠ pq.2 ∧ pq.1 + pq.2 ∈ Sing).image fun pq => pq.1 + pq.2)

theorem mem_stepK {K : Finset V8} {p : V8} :
    p ∈ stepK K ↔ p ∈ K ∨ ∃ p₁ ∈ K, ∃ p₂ ∈ K, p₁ ≠ p₂ ∧ p₁ + p₂ ∈ Sing ∧ p = p₁ + p₂ := by
  unfold stepK
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Prod.exists]
  constructor
  · rintro (h | ⟨p₁, p₂, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨p₁, h1, p₂, h2, h3, h4, rfl⟩
  · rintro (h | ⟨p₁, h1, p₂, h2, h3, h4, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨p₁, p₂, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩

section Masks

open CFSG.Permutation.FinPack

@[expose] def bitsOf (f : ℕ → Bool) (m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => acc ||| (bif f i then 1 <<< i else 0)) m

theorem testBit_bitsOf (f : ℕ → Bool) : ∀ (m j : ℕ),
    (bitsOf f m).testBit j = (decide (j < m) && f j)
  | 0, j => by simp [bitsOf]
  | m + 1, j => by
    change (bitsOf f m ||| (bif f m then 1 <<< m else 0)).testBit j = _
    rw [Nat.testBit_or, testBit_bitsOf f m j]
    by_cases hj : j = m
    · subst hj
      cases f j <;> simp [Nat.one_shiftLeft, Nat.testBit_two_pow]
    · have e : (bif f m then 1 <<< m else 0).testBit j = false := by
        cases f m <;> simp [Nat.one_shiftLeft, Nat.testBit_two_pow, Ne.symm hj]
      rw [e, Bool.or_false]
      by_cases h : j < m
      · simp [h, show j < m + 1 by omega]
      · simp [h, show ¬ j < m + 1 by omega]

@[expose] def encV (x : V8) : ℕ := bitsOf (fun i => if h : i < 8 then decide (x ⟨i, h⟩ = 1) else false) 8

@[expose] def decV (c : ℕ) : V8 := fun i => if c.testBit i then 1 else 0

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

theorem testBit_encV (x : V8) (j : ℕ) :
    (encV x).testBit j = if h : j < 8 then decide (x ⟨j, h⟩ = 1) else false := by
  rw [encV, testBit_bitsOf]
  by_cases h : j < 8 <;> simp [h]

theorem decV_encV (x : V8) : decV (encV x) = x := by
  funext i
  rw [decV, testBit_encV, dif_pos i.isLt]
  rcases zmod2_cases (x i) with h | h <;> simp [h]

theorem encV_decV {c : ℕ} (hc : c < 256) : encV (decV c) = c := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_encV]
  by_cases h : j < 8
  · rw [dif_pos h, decV]
    cases c.testBit j <;> simp
  · rw [dif_neg h, Nat.testBit_lt_two_pow]
    exact lt_of_lt_of_le hc (by
      calc (256 : ℕ) = 2 ^ 8 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega))

theorem encV_lt (x : V8) : encV x < 256 := by
  rw [← decV_encV x] at *
  have : encV x < 2 ^ 8 := by
    refine Nat.lt_pow_two_of_testBit _ fun j hj => ?_
    rw [testBit_encV, dif_neg (by omega)]
  rw [decV_encV]
  simpa using this

theorem encV_injective : Function.Injective encV := fun x y h => by
  rw [← decV_encV x, ← decV_encV y, h]

theorem encV_add (x y : V8) : encV (x + y) = encV x ^^^ encV y := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, testBit_encV, testBit_encV, testBit_encV]
  by_cases h : j < 8
  · simp only [dif_pos h, Pi.add_apply]
    rcases zmod2_cases (x ⟨j, h⟩) with hx | hx <;> rcases zmod2_cases (y ⟨j, h⟩) with hy | hy <;>
      simp [hx, hy] <;> decide
  · simp [dif_neg h]

@[expose] def nrmK (c : ℕ) : ℕ := bif c.testBit 0 then c ^^^ 255 else c

theorem encV_nrm (x : V8) : encV (nrm x) = nrmK (encV x) := by
  apply Nat.eq_of_testBit_eq
  intro j
  have h0 : (encV x).testBit 0 = decide (x 0 = 1) := by rw [testBit_encV, dif_pos (by norm_num)]; rfl
  rw [nrmK, h0, testBit_encV]
  by_cases h : j < 8
  · rw [dif_pos h]
    have h255 : (255 : ℕ).testBit j = true := by
      have : (255 : ℕ) = 2 ^ 8 - 1 := by norm_num
      rw [this, Nat.testBit_two_pow_sub_one]; simpa using h
    simp only [nrm]
    rcases zmod2_cases (x 0) with hx0 | hx0 <;> rcases zmod2_cases (x ⟨j, h⟩) with hx | hx <;>
      simp [hx0, hx, Nat.testBit_xor, h255, testBit_encV, h] <;> decide
  · rw [dif_neg h]
    rcases zmod2_cases (x 0) with hx0 | hx0 <;>
      simp [hx0, Nat.testBit_xor, testBit_encV, h, Nat.testBit_lt_two_pow
        (show (255 : ℕ) < 2 ^ j from lt_of_lt_of_le (by norm_num : (255 : ℕ) < 2 ^ 8)
          (Nat.pow_le_pow_right (by norm_num) (by omega)))]

@[expose] def swapK (a b c : ℕ) : ℕ :=
  bitsOf (fun i => c.testBit (if i = a then b else if i = b then a else i)) 8

theorem encV_pvSwap (a b : Fin 8) (x : V8) : encV (pvSwap a b x) = swapK a b (encV x) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [swapK, testBit_bitsOf, testBit_encV]
  by_cases h : j < 8
  · rw [dif_pos h, decide_eq_true h, Bool.true_and, testBit_encV]
    simp only [pvSwap]
    by_cases ha : j = a
    · have : (⟨j, h⟩ : Fin 8) = a := Fin.ext ha
      simp [ha, this, b.isLt]
    · by_cases hb : j = b
      · have e1 : (⟨j, h⟩ : Fin 8) = b := Fin.ext hb
        have e2 : (⟨j, h⟩ : Fin 8) ≠ a := fun e => ha (congrArg Fin.val e)
        have hba : b ≠ a := e1 ▸ e2
        have hba' : (b : ℕ) ≠ a := fun e => hba (Fin.ext e)
        simp [ha, hb, e1, e2, hba, hba', a.isLt]
      · have h1 : (⟨j, h⟩ : Fin 8) ≠ a := fun e => ha (congrArg Fin.val e)
        have h2 : (⟨j, h⟩ : Fin 8) ≠ b := fun e => hb (congrArg Fin.val e)
        simp [ha, hb, h1, h2, h]
  · rw [dif_neg h, decide_eq_false h, Bool.false_and]

@[expose] def pvWK : Wd → ℕ → ℕ
  | [], c => c
  | p :: w, c => swapK p.1 p.2 (pvWK w c)

theorem encV_pvW (w : Wd) (x : V8) : encV (pvW w x) = pvWK w (encV x) := by
  induction w with
  | nil => rfl
  | cons p w ih => rw [pvW, pvWK, encV_pvSwap, ih]

@[expose] def imgK (f : ℕ → ℕ) (M : ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun c acc => bif M.testBit c then acc ||| (1 <<< f c) else acc) n

theorem testBit_imgK (f : ℕ → ℕ) (M : ℕ) : ∀ (n j : ℕ),
    (imgK f M n).testBit j = true → ∃ c < n, M.testBit c = true ∧ f c = j
  | 0, j, h => by simp [imgK] at h
  | n + 1, j, h => by
    change (bif M.testBit n then imgK f M n ||| (1 <<< f n) else imgK f M n).testBit j = true at h
    cases hm : M.testBit n <;> rw [hm] at h
    · obtain ⟨c, hc, h1, h2⟩ := testBit_imgK f M n j h
      exact ⟨c, by omega, h1, h2⟩
    · simp only [cond_true, Nat.testBit_or, Bool.or_eq_true, Nat.one_shiftLeft,
        Nat.testBit_two_pow, decide_eq_true_iff] at h
      rcases h with h | h
      · obtain ⟨c, hc, h1, h2⟩ := testBit_imgK f M n j h
        exact ⟨c, by omega, h1, h2⟩
      · exact ⟨n, by omega, hm, h⟩

@[expose] def stepLK (gs : List Wd) (M : ℕ) : ℕ :=
  gs.foldr (fun g acc => acc ||| imgK (fun c => nrmK (pvWK g c)) M 256) M

theorem testBit_stepLK (gs : List Wd) (M j : ℕ) (h : (stepLK gs M).testBit j = true) :
    M.testBit j = true ∨ ∃ g ∈ gs, ∃ c < 256, M.testBit c = true ∧ nrmK (pvWK g c) = j := by
  induction gs with
  | nil => exact Or.inl h
  | cons g gs ih =>
    change (stepLK gs M ||| imgK (fun c => nrmK (pvWK g c)) M 256).testBit j = true at h
    rw [Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · rcases ih h with h | ⟨g', hg', c, hc, h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨g', List.mem_cons_of_mem _ hg', c, hc, h1, h2⟩
    · obtain ⟨c, hc, h1, h2⟩ := testBit_imgK _ M 256 j h
      exact Or.inr ⟨g, List.mem_cons_self, c, hc, h1, h2⟩

@[expose] def bfsLK (gs : List Wd) (c0 : ℕ) : ℕ → ℕ
  | 0 => 1 <<< c0
  | k + 1 => stepLK gs (bfsLK gs c0 k)

theorem bfsLK_sound (gs : List Wd) (x0 : V8) : ∀ (k : ℕ) (p : V8),
    (bfsLK gs (encV x0) k).testBit (encV p) = true → p ∈ bfsL gs x0 k
  | 0, p, h => by
    rw [bfsLK, Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_iff] at h
    rw [bfsL, Finset.mem_singleton]
    exact encV_injective h.symm
  | k + 1, p, h => by
    rw [bfsL, mem_stepL]
    rcases testBit_stepLK gs _ _ h with h | ⟨g, hg, c, hc, h1, h2⟩
    · exact Or.inl (bfsLK_sound gs x0 k p h)
    · have hx := encV_decV hc
      rw [← hx] at h1
      refine Or.inr ⟨g, hg, decV c, bfsLK_sound gs x0 k _ h1, encV_injective ?_⟩
      rw [encV_nrm, encV_pvW, hx, h2]

@[expose] def pairsIn (S M c : ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun d acc2 =>
    bif M.testBit d && !(Nat.beq c d) && S.testBit (c ^^^ d) then acc2 ||| (1 <<< (c ^^^ d))
    else acc2) n

@[expose] def pairsOut (S M : ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun c acc => bif M.testBit c then acc ||| pairsIn S M c 256
    else acc) n

theorem testBit_pairsIn (S M c : ℕ) : ∀ (n j : ℕ), (pairsIn S M c n).testBit j = true →
    ∃ d < n, M.testBit d = true ∧ c ≠ d ∧ S.testBit (c ^^^ d) = true ∧ c ^^^ d = j
  | 0, j, h => by simp [pairsIn] at h
  | n + 1, j, h => by
    change (bif M.testBit n && !(Nat.beq c n) && S.testBit (c ^^^ n) then
      pairsIn S M c n ||| (1 <<< (c ^^^ n)) else pairsIn S M c n).testBit j = true at h
    cases hb : (M.testBit n && !(Nat.beq c n) && S.testBit (c ^^^ n)) <;> rw [hb] at h
    · obtain ⟨d, hd, h1⟩ := testBit_pairsIn S M c n j h
      exact ⟨d, by omega, h1⟩
    · simp only [cond_true, Nat.testBit_or, Bool.or_eq_true, Nat.one_shiftLeft,
        Nat.testBit_two_pow, decide_eq_true_iff] at h
      rcases h with h | h
      · obtain ⟨d, hd, h1⟩ := testBit_pairsIn S M c n j h
        exact ⟨d, by omega, h1⟩
      · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hb
        refine ⟨n, by omega, hb.1.1, fun e => ?_, hb.2, h⟩
        rw [e, Nat.beq_refl] at hb
        exact Bool.false_ne_true hb.1.2.symm

theorem testBit_pairsOut (S M : ℕ) : ∀ (n j : ℕ), (pairsOut S M n).testBit j = true →
    ∃ c < n, M.testBit c = true ∧ ∃ d < 256, M.testBit d = true ∧ c ≠ d ∧
      S.testBit (c ^^^ d) = true ∧ c ^^^ d = j
  | 0, j, h => by simp [pairsOut] at h
  | n + 1, j, h => by
    change (bif M.testBit n then pairsOut S M n ||| pairsIn S M n 256 else pairsOut S M n).testBit j
      = true at h
    cases hm : M.testBit n <;> rw [hm] at h
    · obtain ⟨c, hc, h1⟩ := testBit_pairsOut S M n j h
      exact ⟨c, by omega, h1⟩
    · simp only [cond_true, Nat.testBit_or, Bool.or_eq_true] at h
      rcases h with h | h
      · obtain ⟨c, hc, h1⟩ := testBit_pairsOut S M n j h
        exact ⟨c, by omega, h1⟩
      · exact ⟨n, by omega, hm, testBit_pairsIn S M n 256 j h⟩

@[expose] def stepKK (S M : ℕ) : ℕ := M ||| pairsOut S M 256

theorem stepKK_sound {S M : ℕ} {K : Finset V8} (hM : ∀ q, M.testBit (encV q) = true → q ∈ K)
    (hS : ∀ q, S.testBit (encV q) = true → q ∈ Sing) :
    ∀ p, (stepKK S M).testBit (encV p) = true → p ∈ stepK K := by
  intro p h
  rw [mem_stepK]
  rw [stepKK, Nat.testBit_or, Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl (hM p h)
  · obtain ⟨c, hc, h1, d, hd, h2, hne, h3, h4⟩ := testBit_pairsOut S M 256 _ h
    have ec := encV_decV hc
    have ed := encV_decV hd
    refine Or.inr ⟨decV c, hM _ (by rwa [ec]), decV d, hM _ (by rwa [ed]), fun e => hne ?_,
      hS _ (by rwa [encV_add, ec, ed]), encV_injective (by rw [encV_add, ec, ed, h4])⟩
    rw [← ec, ← ed, e]

@[expose] def maskL (L : List ℕ) : ℕ := L.foldr (fun c acc => acc ||| (1 <<< c)) 0

theorem testBit_maskL : ∀ (L : List ℕ) (j : ℕ), (maskL L).testBit j = true → j ∈ L
  | [], j, h => by simp [maskL] at h
  | c :: L, j, h => by
    change (maskL L ||| (1 <<< c)).testBit j = true at h
    simp only [Nat.testBit_or, Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow,
      decide_eq_true_iff] at h
    rcases h with h | h
    · exact List.mem_cons_of_mem _ (testBit_maskL L j h)
    · rw [h]; exact List.mem_cons_self

@[expose] def singK (c : ℕ) : Bool := decide (isNE (decV c) ∧ decV c ≠ 0 ∧ qP8 (decV c) = 0)

@[expose] def nsK (c : ℕ) : Bool := decide (isNE (decV c) ∧ qP8 (decV c) = 1)

theorem singMask_sound (q : V8) (h : (bitsOf singK 256).testBit (encV q) = true) : q ∈ Sing := by
  rw [testBit_bitsOf, Bool.and_eq_true] at h
  have h2 := h.2
  rw [singK, decV_encV, decide_eq_true_iff] at h2
  exact mem_Sing.2 h2

theorem basisMask_sound (q : V8)
    (h : (maskL ((List.finRange 6).map fun i => encV (basis6 i))).testBit (encV q) = true) :
    q ∈ Finset.univ.image basis6 := by
  obtain ⟨i, -, hi⟩ := List.mem_map.1 (testBit_maskL _ _ h)
  exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, encV_injective hi⟩

end Masks

theorem card_NS : NS.card = 28 := by decide +kernel

theorem sing_bfs : ∀ p ∈ Sing, p ∈ bfsL gensAll a0 9 := by decide +kernel

theorem stab_fix : ∀ g ∈ gensStab, nrm (pvW g a0) = a0 := by decide +kernel

theorem nbr_bfs : ∀ q ∈ Sing, q ≠ a0 → a0 + q ∈ Sing → q ∈ bfsL gensStab b0 6 := by decide +kernel

open CFSG.Permutation.FinPack in
theorem known_all : ∀ p ∈ Sing, p ∈ stepK (stepK (stepK (Finset.univ.image basis6))) := by
  have hw : allLtK (fun c => !singK c || (stepKK (bitsOf singK 256) (stepKK (bitsOf singK 256)
      (stepKK (bitsOf singK 256) (maskL ((List.finRange 6).map fun i => encV (basis6 i)))))).testBit c)
      256 = true := by
    decide +kernel
  intro p hp
  have h := allLtK_iff.1 hw (encV p) (encV_lt p)
  have hs : singK (encV p) = true := by
    rw [singK, decV_encV]
    exact decide_eq_true (mem_Sing.1 hp)
  rw [hs, Bool.not_true, Bool.false_or] at h
  exact stepKK_sound (stepKK_sound (stepKK_sound (basisMask_sound) singMask_sound) singMask_sound)
    singMask_sound p h

theorem basis_span : ∀ x : V8, isNE x → ∃ ε : Fin 6 → ZMod 2, x = ∑ i, ε i • basis6 i := by decide +kernel

open CFSG.Permutation.FinPack in
theorem ns_bfs : ∀ x ∈ NS, x ∈ bfsL gensAll nsRoot 13 := by
  have hw : allLtK (fun c => !nsK c || (bfsLK gensAll (encV nsRoot) 13).testBit c) 256 = true := by
    decide +kernel
  intro x hx
  have h := allLtK_iff.1 hw (encV x) (encV_lt x)
  have hs : nsK (encV x) = true := by
    rw [nsK, decV_encV]
    exact decide_eq_true (mem_NS.1 hx)
  rw [hs, Bool.not_true, Bool.false_or] at h
  exact bfsLK_sound gensAll nsRoot 13 x h

theorem basis_mem_Sing : ∀ i, basis6 i ∈ Sing := by decide +kernel

theorem sum_pv (σ : Perm (Fin 8)) (x : V8) : ∑ i, pv σ x i = ∑ i, x i :=
  Equiv.sum_comp σ⁻¹ (fun i => x i)

theorem sum_nrm (y : V8) (h : ∑ i, y i = 0) : ∑ i, nrm y i = 0 := by
  unfold nrm
  rw [Finset.sum_add_distrib, h, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have : ∀ c : ZMod 2, (8 : ℕ) • c = 0 := by decide
  rw [this, add_zero]

theorem isNE_act (σ : Perm (Fin 8)) {x : V8} (hx : ∑ i, x i = 0) : isNE (act σ x) := by
  refine ⟨act_zero_apply σ x, ?_⟩
  unfold act
  apply sum_nrm
  rw [sum_pv, hx]

theorem wt8_pv (σ : Perm (Fin 8)) (x : V8) : wt8 (pv σ x) = wt8 x :=
  Equiv.sum_comp σ⁻¹ (fun i => (x i).val)

theorem qP8_nrm_even : ∀ y : V8, ∑ i, y i = 0 → qP8 (nrm y) = qP8 y := by decide +kernel

theorem qP8_act (σ : Perm (Fin 8)) {x : V8} (hx : ∑ i, x i = 0) : qP8 (act σ x) = qP8 x := by
  unfold act
  rw [qP8_nrm_even _ (by rw [sum_pv, hx])]
  unfold qP8
  rw [wt8_pv]

theorem act_ne_zero (σ : Perm (Fin 8)) {x : V8} (hx0 : x 0 = 0) (hx : x ≠ 0) : act σ x ≠ 0 := by
  intro h
  apply hx
  have := act_inv_act σ x hx0
  rw [h, act_zero] at this
  exact this.symm

theorem act_mem_Sing (σ : Perm (Fin 8)) {x : V8} (hx : x ∈ Sing) : act σ x ∈ Sing := by
  obtain ⟨⟨h0, hs⟩, hne, hq⟩ := mem_Sing.1 hx
  refine mem_Sing.2 ⟨isNE_act σ hs, act_ne_zero σ h0 hne, ?_⟩
  rw [qP8_act σ hs, hq]

theorem trans_pts {p : V8} (hp : p ∈ Sing) : ∃ σ : Perm (Fin 8), act σ a0 = p := by
  have h := sing_bfs p hp
  obtain ⟨σ, -, hσ⟩ := bfsL_sound gensAll (fun _ => True) trivial (fun _ _ _ _ => trivial) a0
    (by decide) 9 p h
  exact ⟨σ, hσ⟩

theorem trans_nbr {q : V8} (hq : q ∈ Sing) (hne : q ≠ a0) (hs : a0 + q ∈ Sing) :
    ∃ ρ : Perm (Fin 8), act ρ a0 = a0 ∧ act ρ b0 = q := by
  have h := nbr_bfs q hq hne hs
  obtain ⟨σ, hσ, hσ'⟩ := bfsL_sound gensStab (fun σ => act σ a0 = a0) (act_one a0 (by decide))
    (fun g hg σ hσ => by
      rw [act_mul, hσ]
      show nrm (pv (permW g) a0) = a0
      rw [pv_permW]
      exact stab_fix g hg) b0 (by decide) 6 q h
  exact ⟨σ, hσ, hσ'⟩

theorem trans_pairs {p q : V8} (hp : p ∈ Sing) (hq : q ∈ Sing) (hne : p ≠ q)
    (hpq : p + q ∈ Sing) : ∃ σ : Perm (Fin 8), act σ a0 = p ∧ act σ b0 = q := by
  obtain ⟨σ₁, h₁⟩ := trans_pts hp
  have hq0 : q 0 = 0 := (mem_Sing.1 hq).1.1
  have hp0 : p 0 = 0 := (mem_Sing.1 hp).1.1
  set q' := act σ₁⁻¹ q with hq'
  have hq'S : q' ∈ Sing := act_mem_Sing _ hq
  have hq'ne : q' ≠ a0 := by
    intro h
    apply hne
    rw [← h₁, ← h, hq', act_act_inv σ₁ q hq0]
  have hsum : a0 + q' = act σ₁⁻¹ (p + q) := by
    rw [act_add, ← h₁, act_inv_act σ₁ a0 (by decide)]
  have hs : a0 + q' ∈ Sing := by rw [hsum]; exact act_mem_Sing _ hpq
  obtain ⟨ρ₂, hρ₂, hρ₂'⟩ := trans_nbr hq'S hq'ne hs
  refine ⟨σ₁ * ρ₂, ?_, ?_⟩
  · rw [act_mul, hρ₂, h₁]
  · rw [act_mul, hρ₂', hq', act_act_inv σ₁ q hq0]

section Core

variable {V : Type} [CommGroup V]

theorem pow_mod_two (hV : ∀ v : V, v ^ 2 = 1) (v : V) (n : ℕ) : v ^ n = v ^ (n % 2) := by
  conv_lhs => rw [← Nat.div_add_mod n 2, pow_add, pow_mul, hV v, one_pow, one_mul]

theorem inv_eq_self_of_sq (hV : ∀ v : V, v ^ 2 = 1) (v : V) : v⁻¹ = v :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV v)

theorem card_closure_range_le [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (b : Fin 6 → V) :
    Nat.card (Subgroup.closure (Set.range b)) ≤ 2 ^ 6 := by
  classical
  have key : ∀ x ∈ Subgroup.closure (Set.range b),
      ∃ ε : Fin 6 → ZMod 2, x = ∏ i, b i ^ (ε i).val := by
    intro x hx
    refine Subgroup.closure_induction
      (p := fun x _ => ∃ ε : Fin 6 → ZMod 2, x = ∏ i, b i ^ (ε i).val) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨j, rfl⟩
      refine ⟨Pi.single j 1, ?_⟩
      rw [Finset.prod_eq_single j]
      · have : (1 : ZMod 2).val = 1 := by decide
        simp [this]
      · intro i _ hij
        simp [hij]
      · simp
    · exact ⟨0, by simp⟩
    · rintro x y - - ⟨ε, rfl⟩ ⟨δ, rfl⟩
      refine ⟨ε + δ, ?_⟩
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← pow_add, pow_mod_two hV (b i) ((ε i).val + (δ i).val), Pi.add_apply, ZMod.val_add]
    · rintro x - ⟨ε, rfl⟩
      exact ⟨ε, inv_eq_self_of_sq hV _⟩
  have hmem : ∀ ε : Fin 6 → ZMod 2, (∏ i, b i ^ (ε i).val) ∈ Subgroup.closure (Set.range b) := by
    intro ε
    exact Subgroup.prod_mem _ fun i _ => Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self i)) _
  let f : (Fin 6 → ZMod 2) → ↥(Subgroup.closure (Set.range b)) := fun ε => ⟨_, hmem ε⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨ε, rfl⟩ := key x hx
    exact ⟨ε, rfl⟩
  calc Nat.card ↥(Subgroup.closure (Set.range b)) ≤ Nat.card (Fin 6 → ZMod 2) :=
        Nat.card_le_card_of_surjective f hf
    _ = 2 ^ 6 := by simp [Nat.card_eq_fintype_card]

theorem core [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (ρ : Perm (Fin 8) →* MulAut V)
    (φ : V →* Multiplicative V8)
    (hφ : ∀ σ u, φ (ρ σ u) = Multiplicative.ofAdd (act σ (Multiplicative.toAdd (φ u))))
    (v : V) (hv0 : Multiplicative.toAdd (φ v) = a0)
    (hvR : ∀ τ : Perm (Fin 8), act τ a0 = a0 → ρ τ v = v)
    (g : Perm (Fin 8)) (hg : act g a0 = b0) (hrel : v * ρ g v * ρ (g * g) v = 1) :
    ∃ W : Subgroup V, (∀ τ, ∀ x ∈ W, ρ τ x ∈ W) ∧
      (∀ y : V8, isNE y → ∃ x ∈ W, Multiplicative.toAdd (φ x) = y) ∧ Nat.card W ≤ 2 ^ 6 := by
  classical
  let w : V8 → V := fun p => if h : ∃ σ, act σ a0 = p then ρ h.choose v else 1
  have a0z : a0 0 = 0 := by decide
  have w_eq : ∀ σ, w (act σ a0) = ρ σ v := by
    intro σ
    have h : ∃ σ', act σ' a0 = act σ a0 := ⟨σ, rfl⟩
    have hw : w (act σ a0) = ρ h.choose v := by simp [w, h]
    rw [hw]
    have h1 : act h.choose a0 = act σ a0 := h.choose_spec
    have h2 : act (σ⁻¹ * h.choose) a0 = a0 := by
      rw [act_mul, h1, ← act_mul, inv_mul_cancel, act_one a0 a0z]
    have h3 := hvR _ h2
    calc ρ h.choose v = ρ (σ * (σ⁻¹ * h.choose)) v := by rw [mul_inv_cancel_left]
      _ = ρ σ (ρ (σ⁻¹ * h.choose) v) := by rw [map_mul]; rfl
      _ = ρ σ v := by rw [h3]
  have w_act : ∀ τ σ, w (act τ (act σ a0)) = ρ τ (ρ σ v) := by
    intro τ σ
    rw [← act_mul, w_eq, map_mul]
    rfl
  have hv_w : w a0 = v := by
    have := w_eq 1
    rwa [act_one a0 a0z, map_one] at this
  have hb : w b0 = ρ g v := by rw [← hg, w_eq]
  have hc : act (g * g) a0 = a0 + b0 := by
    have h1 := congrArg φ hrel
    rw [map_mul, map_mul, map_one, hφ g v, hφ (g * g) v, hv0, hg] at h1
    have h2 := congrArg Multiplicative.toAdd h1
    simp only [toAdd_mul, toAdd_ofAdd, toAdd_one] at h2
    rw [hv0] at h2
    funext i
    have h3 := congrFun h2 i
    simp only [Pi.add_apply, Pi.zero_apply] at h3
    have key : ∀ a b c : ZMod 2, a + b + c = 0 → c = a + b := by decide
    exact key _ _ _ h3
  have hc' : w (a0 + b0) = ρ (g * g) v := by rw [← hc, w_eq]
  have hbase : w a0 * w b0 * w (a0 + b0) = 1 := by rw [hv_w, hb, hc']; exact hrel
  have w_add : ∀ p q : V8, p ∈ Sing → q ∈ Sing → p ≠ q → p + q ∈ Sing →
      w (p + q) = w p * w q := by
    intro p q hp hq hne hpq
    obtain ⟨σ, h1, h2⟩ := trans_pairs hp hq hne hpq
    have h3 : act σ (a0 + b0) = p + q := by rw [act_add, h1, h2]
    have h4 := congrArg (ρ σ) hbase
    rw [map_mul, map_mul, map_one] at h4
    have e1 : ρ σ (w a0) = w p := by rw [hv_w, ← w_eq σ, h1]
    have e2 : ρ σ (w b0) = w q := by
      rw [hb, ← w_act σ g, hg, h2]
    have e3 : ρ σ (w (a0 + b0)) = w (p + q) := by
      rw [hc', ← w_act σ (g * g), hc, h3]
    rw [e1, e2, e3] at h4
    have h5 : w (p + q) = (w p * w q)⁻¹ := eq_inv_of_mul_eq_one_right h4
    rw [h5, inv_eq_self_of_sq hV]
  set W₀ : Subgroup V := Subgroup.closure (Set.range fun i => w (basis6 i)) with hW₀
  have stepGood : ∀ K : Finset V8, (∀ p ∈ K, p ∈ Sing ∧ w p ∈ W₀) →
      ∀ p ∈ stepK K, p ∈ Sing ∧ w p ∈ W₀ := by
    intro K ih p hp
    rcases mem_stepK.1 hp with h | ⟨p₁, hk1, p₂, hk2, hne, hS, rfl⟩
    · exact ih p h
    · obtain ⟨hS1, hw1⟩ := ih _ hk1
      obtain ⟨hS2, hw2⟩ := ih _ hk2
      refine ⟨hS, ?_⟩
      show w (p₁ + p₂) ∈ W₀
      rw [w_add p₁ p₂ hS1 hS2 hne hS]
      exact W₀.mul_mem hw1 hw2
  have base : ∀ p ∈ Finset.univ.image basis6, p ∈ Sing ∧ w p ∈ W₀ := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨basis_mem_Sing i, Subgroup.subset_closure (Set.mem_range_self i)⟩
  have hsub : ∀ p ∈ Sing, w p ∈ W₀ := fun p hp =>
    (stepGood _ (stepGood _ (stepGood _ base)) p (known_all p hp)).2
  let W : Subgroup V := Subgroup.closure (w '' (Sing : Set V8))
  have hWle : W ≤ W₀ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨p, hp, rfl⟩
    exact hsub p hp
  have w_act' : ∀ τ p, p ∈ Sing → ρ τ (w p) = w (act τ p) := by
    intro τ p hp
    obtain ⟨σ, rfl⟩ := trans_pts hp
    rw [w_eq, w_act]
  have hinv : ∀ τ, ∀ x ∈ W, ρ τ x ∈ W := by
    intro τ x hx
    refine Subgroup.closure_induction (p := fun x _ => ρ τ x ∈ W) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨p, hp, rfl⟩
      rw [w_act' τ p hp]
      exact Subgroup.subset_closure (Set.mem_image_of_mem w (Finset.mem_coe.2 (act_mem_Sing τ hp)))
    · rw [map_one]; exact W.one_mem
    · intro x y _ _ hx hy
      rw [map_mul]; exact W.mul_mem hx hy
    · intro x _ hx
      rw [map_inv]; exact W.inv_mem hx
  have hφw : ∀ p ∈ Sing, Multiplicative.toAdd (φ (w p)) = p := by
    intro p hp
    obtain ⟨σ, rfl⟩ := trans_pts hp
    rw [w_eq, hφ, hv0, toAdd_ofAdd]
  refine ⟨W, hinv, ?_, ?_⟩
  · intro y hy
    obtain ⟨ε, hε⟩ := basis_span y hy
    refine ⟨∏ i, w (basis6 i) ^ (ε i).val, ?_, ?_⟩
    · exact Subgroup.prod_mem _ fun i _ => Subgroup.pow_mem _
        (Subgroup.subset_closure (Set.mem_image_of_mem w (Finset.mem_coe.2 (basis_mem_Sing i)))) _
    · rw [map_prod, toAdd_prod, hε]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_pow, toAdd_pow, hφw _ (basis_mem_Sing i), ← Nat.cast_smul_eq_nsmul (ZMod 2),
        ZMod.natCast_zmod_val]
  · exact (Subgroup.card_le_of_le hWle).trans (card_closure_range_le hV _)

end Core

end LRed4L

end CFSG.Quasithin
