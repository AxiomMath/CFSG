module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.H13.HatC

abbrev W6 : Type := Multiplicative (Fin 6 → ZMod 2)

@[expose] def dec (c : ℕ) : Fin 6 → ZMod 2 := fun i => if c.testBit i then 1 else 0

@[expose] def enc (v : Fin 6 → ZMod 2) : ℕ :=
  (v 0).val + 2 * (v 1).val + 4 * (v 2).val + 8 * (v 3).val + 16 * (v 4).val + 32 * (v 5).val

theorem enc_dec : ∀ c < 64, enc (dec c) = c := by
  decide +kernel

theorem dec_enc_lt : ∀ v : Fin 6 → ZMod 2, dec (enc v) = v ∧ enc v < 64 := by
  decide +kernel

theorem dec_enc (v : Fin 6 → ZMod 2) : dec (enc v) = v := (dec_enc_lt v).1

theorem enc_lt (v : Fin 6 → ZMod 2) : enc v < 64 := (dec_enc_lt v).2

theorem dec_injective {a b : ℕ} (ha : a < 64) (hb : b < 64) (h : dec a = dec b) : a = b := by
  rw [← enc_dec a ha, ← enc_dec b hb, h]

theorem dec_xor (a b : ℕ) : dec (a ^^^ b) = dec a + dec b := by
  funext i
  simp only [dec, Nat.testBit_xor, Pi.add_apply]
  cases a.testBit i <;> cases b.testBit i <;> decide

theorem dec_zero : dec 0 = 0 := by
  funext i
  simp [dec]

@[expose] def mactN (m : List ℕ) (c : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => mactN m c n ^^^ (if c.testBit n then m.getD n 0 else 0)

@[expose] def mact (m : List ℕ) (c : ℕ) : ℕ := mactN m c 6

@[expose] def mmul (m n : List ℕ) : List ℕ := n.map (mact m)

@[expose] def idc : List ℕ := [1, 2, 4, 8, 16, 32]

@[expose] def mcode (g : W6 → W6) : List ℕ :=
  (List.range 6).map fun k => enc (Multiplicative.toAdd (g (Multiplicative.ofAdd (dec (2 ^ k)))))

theorem dec_eq_sum : ∀ c < 64, dec c =
    ∑ k ∈ Finset.range 6, (if c.testBit k then dec (2 ^ k) else 0) := by
  decide +kernel

theorem dec_mactN (m : List ℕ) (c n : ℕ) :
    dec (mactN m c n) = ∑ k ∈ Finset.range n, (if c.testBit k then dec (m.getD k 0) else 0) := by
  induction n with
  | zero => simp [mactN, dec_zero]
  | succ n ih =>
    rw [mactN, dec_xor, ih, Finset.sum_range_succ]
    congr 1
    split_ifs <;> simp [dec_zero]

theorem mcode_getD (g : W6 → W6) {k : ℕ} (hk : k < 6) :
    (mcode g).getD k 0 = enc (Multiplicative.toAdd (g (Multiplicative.ofAdd (dec (2 ^ k))))) := by
  simp [mcode, hk]

theorem dec_mact (g : MulAut W6) {c : ℕ} (hc : c < 64) :
    dec (mact (mcode g) c) = Multiplicative.toAdd (g (Multiplicative.ofAdd (dec c))) := by
  rw [mact, dec_mactN, dec_eq_sum c hc]
  have hadd : ∀ (s : Finset ℕ) (f : ℕ → Fin 6 → ZMod 2),
      Multiplicative.toAdd (g (Multiplicative.ofAdd (∑ k ∈ s, f k))) =
        ∑ k ∈ s, Multiplicative.toAdd (g (Multiplicative.ofAdd (f k))) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ofAdd_add, map_mul, toAdd_mul, ih]
  rw [hadd]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [mcode_getD g (Finset.mem_range.1 hk), dec_enc]
  split_ifs
  · rfl
  · simp

theorem mact_lt {m : List ℕ} (hm : ∀ k < 6, m.getD k 0 < 64) (c : ℕ) : mact m c < 64 := by
  have key : ∀ n ≤ 6, mactN m c n < 2 ^ 6 := by
    intro n hn
    induction n with
    | zero => simp [mactN]
    | succ n ih =>
      rw [mactN]
      refine Nat.xor_lt_two_pow (ih (by omega)) ?_
      split_ifs
      · exact hm n (by omega)
      · positivity
  exact key 6 le_rfl

theorem mcode_getD_lt (g : W6 → W6) {k : ℕ} (hk : k < 6) : (mcode g).getD k 0 < 64 := by
  rw [mcode_getD g hk]
  exact enc_lt _

theorem mcode_mul (g h : MulAut W6) : mcode ⇑(g * h) = mmul (mcode ⇑g) (mcode ⇑h) := by
  simp only [mcode, mmul, List.map_map]
  refine List.map_congr_left fun k _ => ?_
  refine dec_injective (enc_lt _) (mact_lt (fun _ hj => mcode_getD_lt g hj) _) ?_
  rw [dec_enc, Function.comp_apply, show (List.range 6).map (fun k =>
      enc (Multiplicative.toAdd (g (Multiplicative.ofAdd (dec (2 ^ k)))))) = mcode g from rfl,
    dec_mact g (enc_lt _), dec_enc]
  rfl

theorem mcode_injective {g h : MulAut W6} (hgh : mcode ⇑g = mcode ⇑h) : g = h := by
  refine MulEquiv.ext fun x => ?_
  apply Multiplicative.toAdd.injective
  obtain ⟨c, hc, hcx⟩ := (⟨enc (Multiplicative.toAdd x), enc_lt _, dec_enc _⟩ :
    ∃ c < 64, dec c = Multiplicative.toAdd x)
  have hx : x = Multiplicative.ofAdd (dec c) := by rw [hcx]; rfl
  rw [hx, ← dec_mact g hc, ← dec_mact h hc, hgh]

theorem mcode_one : mcode ⇑(1 : MulAut W6) = idc := by
  decide +kernel

@[expose] def linc (m : List ℕ) : (Fin 6 → ZMod 2) →+ (Fin 6 → ZMod 2) where
  toFun v := ∑ k : Fin 6, v k • dec (m.getD k 0)
  map_zero' := by simp
  map_add' v w := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.add_apply, add_smul]

theorem linc_dec : ∀ (m : List ℕ), ∀ c < 64, linc m (dec c) = dec (mact m c) := by
  intro m c hc
  rw [mact, dec_mactN]
  show ∑ k : Fin 6, dec c k • dec (m.getD k 0) = _
  rw [Finset.sum_range (fun k => if c.testBit k then dec (m.getD k 0) else 0)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [dec]
  split_ifs <;> simp

@[expose] def caut (m m' : List ℕ) (h : ∀ c < 64, mact m (mact m' c) = c ∧ mact m' (mact m c) = c)
    (hm : ∀ k < 6, m.getD k 0 < 64) (hm' : ∀ k < 6, m'.getD k 0 < 64) : MulAut W6 where
  toFun x := Multiplicative.ofAdd (linc m (Multiplicative.toAdd x))
  invFun x := Multiplicative.ofAdd (linc m' (Multiplicative.toAdd x))
  left_inv x := by
    obtain ⟨c, hc, hcx⟩ : ∃ c < 64, dec c = Multiplicative.toAdd x :=
      ⟨enc (Multiplicative.toAdd x), enc_lt _, dec_enc _⟩
    show Multiplicative.ofAdd (linc m' (linc m (Multiplicative.toAdd x))) = x
    rw [← hcx, linc_dec m c hc, linc_dec m' _ (mact_lt hm c), (h c hc).2, hcx]
    rfl
  right_inv x := by
    obtain ⟨c, hc, hcx⟩ : ∃ c < 64, dec c = Multiplicative.toAdd x :=
      ⟨enc (Multiplicative.toAdd x), enc_lt _, dec_enc _⟩
    show Multiplicative.ofAdd (linc m (linc m' (Multiplicative.toAdd x))) = x
    rw [← hcx, linc_dec m' c hc, linc_dec m _ (mact_lt hm' c), (h c hc).1, hcx]
    rfl
  map_mul' x y := by
    show Multiplicative.ofAdd (linc m (Multiplicative.toAdd x + Multiplicative.toAdd y)) = _
    rw [map_add]
    rfl

theorem caut_apply (m m' : List ℕ) (h) (hm) (hm') (c : ℕ) (hc : c < 64) :
    caut m m' h hm hm' (Multiplicative.ofAdd (dec c)) = Multiplicative.ofAdd (dec (mact m c)) := by
  show Multiplicative.ofAdd (linc m (dec c)) = _
  rw [linc_dec m c hc]

theorem mcode_caut (m m' : List ℕ) (h) (hm) (hm') (hlen : m.length = 6) :
    mcode ⇑(caut m m' h hm hm') = m := by
  have key : ∀ k < 6, (mcode ⇑(caut m m' h hm hm')).getD k 0 = m.getD k 0 := by
    intro k hk
    rw [mcode_getD _ hk, caut_apply m m' h hm hm' _ (by interval_cases k <;> decide),
      toAdd_ofAdd, enc_dec _ (mact_lt hm _)]
    interval_cases k <;> simp (config := { decide := true }) [mact, mactN]
  apply List.ext_getElem
  · simp [mcode, hlen]
  · intro k hk1 hk2
    have hk : k < 6 := by simpa [mcode] using hk1
    have := key k hk
    rwa [List.getD_eq_getElem _ _ hk1, List.getD_eq_getElem _ _ hk2] at this

theorem enc_apply (g : MulAut W6) (c : ℕ) (hc : c < 64) :
    enc (Multiplicative.toAdd (g (Multiplicative.ofAdd (dec c)))) = mact (mcode g) c := by
  rw [← dec_mact g hc, enc_dec _ (mact_lt (fun _ hk => mcode_getD_lt _ hk) _)]

end CFSG.Quasithin.H13.HatC
