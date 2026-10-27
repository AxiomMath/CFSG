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

public section

namespace CFSG.Quasithin.H158T

@[expose] def genLs : List (List ℕ) :=
  [[22, 7, 4, 21, 1, 16, 19, 2, 14, 10, 12, 11, 15, 13, 8, 9, 3, 18, 17, 0, 20, 5, 6, 23],
    [7, 5, 10, 0, 1, 9, 19, 16, 17, 4, 12, 23, 22, 14, 18, 6, 3, 11, 20, 21, 13, 15, 2, 8],
    [1, 21, 16, 19, 4, 22, 2, 7, 13, 6, 10, 17, 0, 14, 23, 15, 9, 20, 11, 3, 18, 12, 5, 8],
    [12, 0, 6, 22, 7, 19, 9, 4, 11, 16, 15, 14, 21, 17, 20, 10, 2, 23, 13, 5, 8, 1, 3, 18]]

@[expose] def gimg (j x : ℕ) : ℕ := (genLs.getD j []).getD x 0

@[expose] def pt16 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 12, 15, 16, 19, 21, 22]

@[expose] def o0L : List ℕ := [0, 1, 2, 6, 9, 12, 16, 21]

@[expose] def allCs : List (List Bool) :=
  [[false, false, false, false], [false, false, false, true], [false, false, true, false],
    [false, false, true, true], [false, true, false, false], [false, true, false, true],
    [false, true, true, false], [false, true, true, true], [true, false, false, false],
    [true, false, false, true], [true, false, true, false], [true, false, true, true],
    [true, true, false, false], [true, true, false, true], [true, true, true, false],
    [true, true, true, true]]

@[expose] def lab0 (s : ℕ) (b : Bool) : List (Option Bool) :=
  (List.replicate 24 none).set s (some b)

@[expose] def propStep (cs : List Bool) (b : Bool) (x : ℕ) (L : List (Option Bool)) (j : ℕ) :
    List (Option Bool) :=
  match L.getD (gimg j x) none with
  | none => L.set (gimg j x) (some (Bool.xor b (cs.getD j false)))
  | some _ => L

@[expose] def propPt (cs : List Bool) (L : List (Option Bool)) (x : ℕ) : List (Option Bool) :=
  match L.getD x none with
  | none => L
  | some b => [0, 1, 2, 3].foldl (propStep cs b x) L

@[expose] def propRound (cs : List Bool) (L : List (Option Bool)) : List (Option Bool) :=
  pt16.foldl (fun L' x => propPt cs L' x) L

@[expose] def propIter (cs : List Bool) : ℕ → List (Option Bool) → List (Option Bool)
  | 0, L => L
  | n + 1, L => propIter cs n (propRound cs L)

theorem gen_closed_dec : ∀ j ∈ [0, 1, 2, 3], ∀ x ∈ pt16, gimg j x ∈ pt16 := by
  decide +kernel

theorem pt16_lt_dec : ∀ x ∈ pt16, x < 24 := by decide +kernel

theorem cover_dec : ∀ cs ∈ allCs, ∀ y ∈ pt16,
    (propIter cs 16 (lab0 0 true)).getD y none ≠ none := by
  decide +kernel

theorem orbit_dec : ∀ x0 ∈ pt16, ∀ y ∈ pt16,
    (propIter [false, false, false, false] 16 (lab0 x0 true)).getD y none = some true := by
  decide +kernel

theorem part_dec : ∀ cs ∈ allCs,
    (∀ x ∈ pt16, ∀ b : Bool, (propIter cs 16 (lab0 0 true)).getD x none = some b →
      ∀ j ∈ [0, 1, 2, 3], (propIter cs 16 (lab0 0 true)).getD (gimg j x) none =
        some (Bool.xor b (cs.getD j false))) →
    (∃ y ∈ pt16, (propIter cs 16 (lab0 0 true)).getD y none = some false) →
    ∀ y ∈ pt16, (propIter cs 16 (lab0 0 true)).getD y none = some (decide (y ∈ o0L)) := by
  decide +kernel

@[expose] def LabInv (P : ℕ → Bool) (L : List (Option Bool)) : Prop :=
  ∀ y b, L.getD y none = some b → y ∈ pt16 ∧ P y = b

theorem getD_set_ne' (L : List (Option Bool)) {y z : ℕ} (v : Option Bool) (h : y ≠ z) :
    (L.set y v).getD z none = L.getD z none := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set, h]

theorem getD_set_eq' (L : List (Option Bool)) {y : ℕ} (v : Option Bool) (hy : y < L.length) :
    (L.set y v).getD y none = v := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set, hy]

theorem propStep_inv (P : ℕ → Bool) (cs : List Bool) (x : ℕ) (b : Bool) (hb : P x = b)
    (hD : ∀ j ∈ [0, 1, 2, 3], gimg j x ∈ pt16)
    (hP : ∀ j ∈ [0, 1, 2, 3], P (gimg j x) = Bool.xor (P x) (cs.getD j false))
    (j : ℕ) (hj : j ∈ [0, 1, 2, 3]) (L : List (Option Bool)) (hL : LabInv P L)
    (hlen : L.length = 24) :
    LabInv P (propStep cs b x L j) ∧ (propStep cs b x L j).length = 24 := by
  unfold propStep
  split
  · rename_i hnone
    have hlt : gimg j x < L.length := by
      rw [hlen]
      exact pt16_lt_dec _ (hD j hj)
    refine ⟨?_, by simp [hlen]⟩
    intro z c hz
    by_cases hzy : gimg j x = z
    · subst hzy
      rw [getD_set_eq' L _ hlt] at hz
      have hc := Option.some.inj hz
      refine ⟨hD j hj, ?_⟩
      rw [← hc, hP j hj, hb]
    · rw [getD_set_ne' L _ hzy] at hz
      exact hL z c hz
  · exact ⟨hL, hlen⟩

theorem fold_inv (P : ℕ → Bool) (cs : List Bool) (x : ℕ) (b : Bool) (hb : P x = b)
    (hD : ∀ j ∈ [0, 1, 2, 3], gimg j x ∈ pt16)
    (hP : ∀ j ∈ [0, 1, 2, 3], P (gimg j x) = Bool.xor (P x) (cs.getD j false)) :
    ∀ (js : List ℕ), (∀ j ∈ js, j ∈ [0, 1, 2, 3]) → ∀ (L : List (Option Bool)),
      LabInv P L → L.length = 24 →
        LabInv P (js.foldl (propStep cs b x) L) ∧ (js.foldl (propStep cs b x) L).length = 24 := by
  intro js
  induction js with
  | nil => intro _ L hL hlen; exact ⟨hL, hlen⟩
  | cons j js ih =>
    intro hjs L hL hlen
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := propStep_inv P cs x b hb hD hP j (hjs j (by simp)) L hL hlen
    exact ih (fun k hk => hjs k (by simp [hk])) _ h1 h2

theorem propPt_inv (P : ℕ → Bool) (cs : List Bool)
    (hD : ∀ x ∈ pt16, ∀ j ∈ [0, 1, 2, 3], gimg j x ∈ pt16)
    (hP : ∀ x ∈ pt16, ∀ j ∈ [0, 1, 2, 3], P (gimg j x) = Bool.xor (P x) (cs.getD j false))
    (x : ℕ) (hx : x ∈ pt16) (L : List (Option Bool)) (hL : LabInv P L) (hlen : L.length = 24) :
    LabInv P (propPt cs L x) ∧ (propPt cs L x).length = 24 := by
  unfold propPt
  split
  · exact ⟨hL, hlen⟩
  · rename_i b hb0
    have hPx : P x = b := (hL x b hb0).2
    exact fold_inv P cs x b hPx (hD x hx) (hP x hx) [0, 1, 2, 3] (by simp) L hL hlen

theorem list_fold_inv (P : ℕ → Bool) (cs : List Bool)
    (hD : ∀ x ∈ pt16, ∀ j ∈ [0, 1, 2, 3], gimg j x ∈ pt16)
    (hP : ∀ x ∈ pt16, ∀ j ∈ [0, 1, 2, 3], P (gimg j x) = Bool.xor (P x) (cs.getD j false)) :
    ∀ (l : List ℕ), (∀ x ∈ l, x ∈ pt16) → ∀ (L : List (Option Bool)), LabInv P L →
      L.length = 24 → LabInv P (l.foldl (fun L' x => propPt cs L' x) L) ∧
        (l.foldl (fun L' x => propPt cs L' x) L).length = 24 := by
  intro l
  induction l with
  | nil => intro _ L hL hlen; exact ⟨hL, hlen⟩
  | cons x l ih =>
    intro hl L hL hlen
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := propPt_inv P cs hD hP x (hl x (by simp)) L hL hlen
    exact ih (fun k hk => hl k (by simp [hk])) _ h1 h2

theorem propIter_inv (P : ℕ → Bool) (cs : List Bool)
    (hD : ∀ x ∈ pt16, ∀ j ∈ [0, 1, 2, 3], gimg j x ∈ pt16)
    (hP : ∀ x ∈ pt16, ∀ j ∈ [0, 1, 2, 3], P (gimg j x) = Bool.xor (P x) (cs.getD j false))
    (n : ℕ) : ∀ (L : List (Option Bool)), LabInv P L → L.length = 24 →
      LabInv P (propIter cs n L) ∧ (propIter cs n L).length = 24 := by
  induction n with
  | zero => intro L hL hlen; exact ⟨hL, hlen⟩
  | succ n ih =>
    intro L hL hlen
    obtain ⟨h1, h2⟩ := list_fold_inv P cs hD hP pt16 (fun x hx => hx) L hL hlen
    exact ih _ h1 h2

theorem lab0_inv (P : ℕ → Bool) (s : ℕ) (hs : s ∈ pt16) (hPs : P s = true) :
    LabInv P (lab0 s true) := by
  intro y b hy
  unfold lab0 at hy
  by_cases hys : y = s
  · subst hys
    rw [getD_set_eq' _ _ (by rw [List.length_replicate]; exact pt16_lt_dec _ hs)] at hy
    have hb := Option.some.inj hy
    subst hb
    exact ⟨hs, hPs⟩
  · rw [getD_set_ne' _ _ (Ne.symm hys)] at hy
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate] at hy
    split_ifs at hy <;> simp at hy

theorem lab0_len (s : ℕ) (b : Bool) : (lab0 s b).length = 24 := by
  simp [lab0]

theorem part_lab (P : ℕ → Bool) (cs : List Bool) (hcs : cs ∈ allCs) (h0 : P 0 = true)
    (hP : ∀ x ∈ pt16, ∀ j ∈ [0, 1, 2, 3], P (gimg j x) = Bool.xor (P x) (cs.getD j false))
    (hB : ∃ y ∈ pt16, P y = false) :
    ∀ y ∈ pt16, P y = decide (y ∈ o0L) := by
  have hD := gen_closed_dec
  have hD' : ∀ x ∈ pt16, ∀ j ∈ [0, 1, 2, 3], gimg j x ∈ pt16 := fun x hx j hj =>
    gen_closed_dec j hj x hx
  have hinv := propIter_inv P cs hD' hP 16 (lab0 0 true)
    (lab0_inv P 0 (by simp [pt16]) h0) (lab0_len 0 true)
  have hval : ∀ y ∈ pt16, (propIter cs 16 (lab0 0 true)).getD y none = some (P y) := by
    intro y hy
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 (cover_dec cs hcs y hy)
    rw [hb, (hinv.1 y b hb).2]
  have hclosed : ∀ x ∈ pt16, ∀ b : Bool, (propIter cs 16 (lab0 0 true)).getD x none = some b →
      ∀ j ∈ [0, 1, 2, 3], (propIter cs 16 (lab0 0 true)).getD (gimg j x) none =
        some (Bool.xor b (cs.getD j false)) := by
    intro x hx b hb j hj
    have hbx : b = P x := by
      rw [hval x hx] at hb
      exact (Option.some.inj hb).symm
    rw [hval _ (hD' x hx j hj), hP x hx j hj, hbx]
  obtain ⟨y0, hy0, hy0f⟩ := hB
  have hB' : ∃ y ∈ pt16, (propIter cs 16 (lab0 0 true)).getD y none = some false :=
    ⟨y0, hy0, by rw [hval y0 hy0, hy0f]⟩
  intro y hy
  have h1 := part_dec cs hcs hclosed hB' y hy
  rw [hval y hy] at h1
  exact Option.some.inj h1

theorem orbit_lab (P : ℕ → Bool) (x0 : ℕ) (hx0 : x0 ∈ pt16) (hPx0 : P x0 = true)
    (hP : ∀ x ∈ pt16, ∀ j ∈ [0, 1, 2, 3], P (gimg j x) = P x) :
    ∀ y ∈ pt16, P y = true := by
  have hD' : ∀ x ∈ pt16, ∀ j ∈ [0, 1, 2, 3], gimg j x ∈ pt16 := fun x hx j hj =>
    gen_closed_dec j hj x hx
  have hP' : ∀ x ∈ pt16, ∀ j ∈ [0, 1, 2, 3],
      P (gimg j x) = Bool.xor (P x) ([false, false, false, false].getD j false) := by
    intro x hx j hj
    have h0 : ([false, false, false, false] : List Bool).getD j false = false := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl <;> rfl
    rw [h0, Bool.xor_false]
    exact hP x hx j hj
  have hinv := propIter_inv P [false, false, false, false] hD' hP' 16 (lab0 x0 true)
    (lab0_inv P x0 hx0 hPx0) (lab0_len x0 true)
  intro y hy
  exact (hinv.1 y true (orbit_dec x0 hx0 y hy)).2

end CFSG.Quasithin.H158T
