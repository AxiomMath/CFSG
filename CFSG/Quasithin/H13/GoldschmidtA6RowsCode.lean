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
public import Mathlib.GroupTheory.Nilpotent
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Matrix

namespace CFSG.Quasithin.H13.A6.GR

@[expose] def bit (n i : ℕ) : ZMod 2 := if n.testBit i then 1 else 0

@[expose] def vecN (d n : ℕ) : Fin d → ZMod 2 := fun i => bit n i

@[expose] def codeN (d : ℕ) (v : Fin d → ZMod 2) : ℕ := ∑ i : Fin d, (v i).val * 2 ^ (i : ℕ)

theorem bit_xor (a b i : ℕ) : bit (a ^^^ b) i = bit a i + bit b i := by
  unfold bit
  rw [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> decide

theorem bit_zero (i : ℕ) : bit 0 i = 0 := by simp [bit]

theorem vecN_xor (d a b : ℕ) : vecN d (a ^^^ b) = vecN d a + vecN d b := by
  funext i
  exact bit_xor a b i

theorem vecN_zero (d : ℕ) : vecN d 0 = 0 := by
  funext i
  exact bit_zero i

@[expose] def dotC (d c y : ℕ) : ℕ :=
  ((List.range d).filter fun i => c.testBit i && y.testBit i).length % 2

structure Laws (d : ℕ) : Prop where
  vec_code : ∀ v : Fin d → ZMod 2, vecN d (codeN d v) = v
  code_lt : ∀ v : Fin d → ZMod 2, codeN d v < 2 ^ d
  code_vec : ∀ n, n < 2 ^ d → codeN d (vecN d n) = n
  dot_vec : ∀ c, c < 2 ^ d → ∀ y, y < 2 ^ d → vecN d c ⬝ᵥ vecN d y = (dotC d c y : ZMod 2)

theorem laws4 : Laws 4 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem laws6 : Laws 6 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩


@[expose] def matOfCols (d : ℕ) (cs : List ℕ) : Matrix (Fin d) (Fin d) (ZMod 2) :=
  Matrix.of fun r j => vecN d (cs.getD j 0) r

@[expose] def colsOf (d : ℕ) (K : Matrix (Fin d) (Fin d) (ZMod 2)) : List ℕ :=
  (List.finRange d).map fun j => codeN d (fun i => K i j)

@[expose] def appAux (cs : List ℕ) (x : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (if x.testBit n then cs.getD n 0 else 0) ^^^ appAux cs x n

@[expose] def appC (d : ℕ) (cs : List ℕ) (x : ℕ) : ℕ := appAux cs x d

theorem vecN_appAux (d : ℕ) (cs : List ℕ) (x n : ℕ) :
    vecN d (appAux cs x n) =
      ∑ i ∈ Finset.range n, vecN d (if x.testBit i then cs.getD i 0 else 0) := by
  induction n with
  | zero => simpa [appAux] using vecN_zero d
  | succ n ih => rw [appAux, vecN_xor, ih, Finset.sum_range_succ, add_comm]

theorem vecN_appC (d : ℕ) (cs : List ℕ) (x : ℕ) :
    vecN d (appC d cs x) = matOfCols d cs *ᵥ vecN d x := by
  unfold appC
  rw [vecN_appAux, Finset.sum_range]
  funext r
  simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, matOfCols, Matrix.of_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : x.testBit j
  · simp [hj, vecN, bit]
  · simp [hj, vecN, bit]

theorem appC_zero (d : ℕ) (cs : List ℕ) : appC d cs 0 = 0 := by
  have h : ∀ n : ℕ, appAux cs 0 n = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [appAux, ih]
  exact h d

@[expose] def mulC (d : ℕ) (a b : List ℕ) : List ℕ := b.map (appC d a)

theorem getD_map_zero {f : ℕ → ℕ} (hf : f 0 = 0) (b : List ℕ) (j : ℕ) :
    (b.map f).getD j 0 = f (b.getD j 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases b[j]? <;> simp [hf]

theorem matOfCols_mulC (d : ℕ) (a b : List ℕ) :
    matOfCols d (mulC d a b) = matOfCols d a * matOfCols d b := by
  ext r j
  rw [Matrix.mul_apply]
  have h1 : matOfCols d (mulC d a b) r j = vecN d (appC d a (b.getD j 0)) r := by
    simp only [matOfCols, Matrix.of_apply, mulC]
    rw [getD_map_zero (appC_zero d a)]
  rw [h1, vecN_appC]
  simp [Matrix.mulVec, dotProduct, matOfCols]

@[expose] def oneC (d : ℕ) : List ℕ := (List.range d).map fun i => 2 ^ i

theorem matOfCols_oneC (d : ℕ) : matOfCols d (oneC d) = 1 := by
  ext r j
  rw [Matrix.one_apply]
  simp only [matOfCols, Matrix.of_apply, oneC]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp only [List.getElem_map, List.getElem_range]
  simp [vecN, bit, Nat.testBit_two_pow, Fin.ext_iff, eq_comm]

@[expose] def sqIter (d : ℕ) (cs : List ℕ) : ℕ → List ℕ
  | 0 => cs
  | a + 1 => mulC d (sqIter d cs a) (sqIter d cs a)

theorem matOfCols_sqIter (d : ℕ) (cs : List ℕ) (a : ℕ) :
    matOfCols d (sqIter d cs a) = matOfCols d cs ^ (2 ^ a) := by
  induction a with
  | zero => simp [sqIter]
  | succ a ih =>
    rw [sqIter, matOfCols_mulC, ih, ← pow_add, pow_succ 2 a, mul_two]

@[expose] def cubeC (d : ℕ) (cs : List ℕ) : List ℕ := mulC d cs (mulC d cs cs)

theorem matOfCols_cubeC (d : ℕ) (cs : List ℕ) :
    matOfCols d (cubeC d cs) = matOfCols d cs ^ 3 := by
  rw [cubeC, matOfCols_mulC, matOfCols_mulC]
  simp [pow_succ, Matrix.mul_assoc]

theorem matOfCols_colsOf {d : ℕ} (hL : Laws d) (K : Matrix (Fin d) (Fin d) (ZMod 2)) :
    matOfCols d (colsOf d K) = K := by
  ext r j
  simp only [matOfCols, Matrix.of_apply, colsOf]
  rw [List.getD_eq_getElem _ _ (by simp)]
  have key := congrFun (hL.vec_code (fun i => K i j)) r
  simpa using key


@[expose] def spanC (d : ℕ) (L : List (List ℕ)) : Bool :=
  (List.range (2 ^ d)).all fun c => c == 0 || L.any fun q => (List.range (2 ^ d)).any fun y =>
    dotC d c (appC d q y % 2 ^ d) != dotC d c y

@[expose] def conjC (d : ℕ) (gp : List (List ℕ × List ℕ)) (cs : List ℕ) : List (List ℕ) :=
  cs :: gp.flatMap fun p => [mulC d (mulC d p.1 cs) p.2, mulC d (mulC d p.2 cs) p.1]

@[expose] def wordC (d : ℕ) (gm : List (List ℕ)) : List ℕ → List ℕ
  | [] => oneC d
  | i :: w => mulC d (gm.getD i (oneC d)) (wordC d gm w)

@[expose] def ccolsC (d : ℕ) (gm : List (List ℕ)) (words : List (List ℕ)) (w : ℕ) : List ℕ :=
  words.map fun wd => appC d (wordC d gm wd) w

@[expose] def pcolsC (d : ℕ) (gm : List (List ℕ)) (words : List (List ℕ)) (Binv : List ℕ) (w : ℕ) :
    List ℕ := mulC d (ccolsC d gm words w) Binv

@[expose] def fixC (d : ℕ) (Pc : List ℕ) : ℕ :=
  ((Finset.range (2 ^ d)).filter fun y => appC d Pc y % 2 ^ d = y).card

@[expose] def commOk (d : ℕ) (Pc pre : List ℕ) : Bool :=
  (List.range pre.length).all fun i =>
    decide (2 ^ pre.length ≤ Pc.getD i 0) ||
      appC d pre (Pc.getD i 0) % 2 ^ d == appC d Pc (pre.getD i 0) % 2 ^ d

@[expose] def bt (d : ℕ) (ok : List ℕ → ℕ → Bool) : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (bt d ok n).flatMap fun pre =>
      ((List.range (2 ^ d)).filter (ok pre)).map fun c => pre ++ [c]


theorem vecN_mod (d n : ℕ) : vecN d (n % 2 ^ d) = vecN d n := by
  funext i
  simp [vecN, bit, Nat.testBit_mod_two_pow, i.2]

theorem vecN_eq_iff_mod {d : ℕ} (hL : Laws d) (a b : ℕ) :
    vecN d a = vecN d b ↔ a % 2 ^ d = b % 2 ^ d := by
  constructor
  · intro h
    have ha := hL.code_vec (a % 2 ^ d) (Nat.mod_lt _ (by positivity))
    have hb := hL.code_vec (b % 2 ^ d) (Nat.mod_lt _ (by positivity))
    rw [← ha, ← hb, vecN_mod, vecN_mod, h]
  · intro h
    rw [← vecN_mod d a, ← vecN_mod d b, h]

@[expose] def normC (d : ℕ) (cs : List ℕ) : List ℕ :=
  (List.range d).map fun j => cs.getD j 0 % 2 ^ d

theorem normC_getD (d : ℕ) (cs : List ℕ) {j : ℕ} (hj : j < d) :
    (normC d cs).getD j 0 = cs.getD j 0 % 2 ^ d := by
  rw [normC, List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

theorem matOfCols_eq_iff {d : ℕ} (hL : Laws d) (a b : List ℕ) :
    matOfCols d a = matOfCols d b ↔ normC d a = normC d b := by
  constructor
  · intro h
    refine List.map_congr_left fun j hj => ?_
    have hj' : j < d := List.mem_range.mp hj
    have h1 : vecN d (a.getD j 0) = vecN d (b.getD j 0) := by
      funext r
      exact congrFun (congrFun h r) ⟨j, hj'⟩
    exact (vecN_eq_iff_mod hL _ _).mp h1
  · intro h
    ext r j
    have h1 : a.getD j 0 % 2 ^ d = b.getD j 0 % 2 ^ d := by
      have h3 : (normC d a).getD (j : ℕ) 0 = (normC d b).getD (j : ℕ) 0 :=
        congrArg (fun l => List.getD l (j : ℕ) 0) h
      rw [normC_getD d a j.2, normC_getD d b j.2] at h3
      exact h3
    have h2 := (vecN_eq_iff_mod hL _ _).mpr h1
    exact congrFun h2 r

@[expose] def isOne (d : ℕ) (cs : List ℕ) : Bool := normC d cs == normC d (oneC d)

theorem isOne_iff {d : ℕ} (hL : Laws d) (cs : List ℕ) : isOne d cs = true ↔ matOfCols d cs = 1 := by
  rw [isOne, beq_iff_eq, ← matOfCols_eq_iff hL, matOfCols_oneC]


@[expose] def Span {d : ℕ} (T : List (Matrix (Fin d) (Fin d) (ZMod 2))) : Prop :=
  ∀ c : Fin d → ZMod 2, c ≠ 0 → ∃ q ∈ T, ∃ y : Fin d → ZMod 2, c ⬝ᵥ (q *ᵥ y) ≠ c ⬝ᵥ y

@[expose] def conjM {d : ℕ}
    (gp : List (Matrix (Fin d) (Fin d) (ZMod 2) × Matrix (Fin d) (Fin d) (ZMod 2)))
    (K : Matrix (Fin d) (Fin d) (ZMod 2)) : List (Matrix (Fin d) (Fin d) (ZMod 2)) :=
  K :: gp.flatMap fun p => [p.1 * K * p.2, p.2 * K * p.1]

@[expose] def fixCard {d : ℕ} (P : Matrix (Fin d) (Fin d) (ZMod 2)) : ℕ :=
  (Finset.univ.filter fun y : Fin d → ZMod 2 => P *ᵥ y = y).card

theorem spanC_sound {d : ℕ} (hL : Laws d) (L : List (List ℕ)) (h : spanC d L = true) :
    Span (L.map (matOfCols d)) := by
  intro c hc
  set cn := codeN d c with hcn
  have hcn_lt : cn < 2 ^ d := hL.code_lt c
  have hcn0 : cn ≠ 0 := by
    intro h0
    apply hc
    have := hL.vec_code c
    rw [← hcn, h0, vecN_zero] at this
    exact this.symm
  unfold spanC at h
  rw [List.all_eq_true] at h
  have h1 := h cn (List.mem_range.mpr hcn_lt)
  simp only [Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 hcn0
  · rw [List.any_eq_true] at h1
    obtain ⟨q, hq, h2⟩ := h1
    rw [List.any_eq_true] at h2
    obtain ⟨y, hy, h3⟩ := h2
    have hy' : y < 2 ^ d := List.mem_range.mp hy
    refine ⟨matOfCols d q, List.mem_map_of_mem hq, vecN d y, ?_⟩
    have hv : vecN d cn = c := hL.vec_code c
    rw [← vecN_appC, ← vecN_mod, ← hv]
    rw [hL.dot_vec cn hcn_lt _ (Nat.mod_lt _ (by positivity)), hL.dot_vec cn hcn_lt y hy']
    intro heq
    have h4 := (ZMod.natCast_eq_natCast_iff' _ _ 2).mp heq
    simp only [bne_iff_ne, ne_eq] at h3
    apply h3
    unfold dotC at h4 ⊢
    omega

theorem fixCard_matOfCols {d : ℕ} (hL : Laws d) (Pc : List ℕ) :
    fixCard (matOfCols d Pc) = fixC d Pc := by
  unfold fixCard fixC
  refine Finset.card_nbij' (codeN d) (vecN d) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
    refine ⟨hL.code_lt y, ?_⟩
    have h1 : vecN d (appC d Pc (codeN d y)) = vecN d (codeN d y) := by
      rw [vecN_appC, hL.vec_code, hy]
    have h2 := (vecN_eq_iff_mod hL _ _).mp h1
    rwa [Nat.mod_eq_of_lt (hL.code_lt y)] at h2
  · intro n hn
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hn
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    rw [← vecN_appC, ← vecN_mod, hn.2]
  · intro y _
    exact hL.vec_code y
  · intro n hn
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hn
    exact hL.code_vec n hn.1


@[expose] def wordMat {d : ℕ} (gm : List (Matrix (Fin d) (Fin d) (ZMod 2))) :
    List ℕ → Matrix (Fin d) (Fin d) (ZMod 2)
  | [] => 1
  | i :: w => gm.getD i 1 * wordMat gm w

theorem comm_wordMat {d : ℕ} {P : Matrix (Fin d) (Fin d) (ZMod 2)}
    {gm : List (Matrix (Fin d) (Fin d) (ZMod 2))} (h : ∀ M ∈ gm, P * M = M * P) (w : List ℕ) :
    P * wordMat gm w = wordMat gm w * P := by
  induction w with
  | nil => simp [wordMat]
  | cons i w ih =>
    have hi : P * gm.getD i 1 = gm.getD i 1 * P := by
      by_cases hlt : i < gm.length
      · rw [List.getD_eq_getElem _ _ hlt]
        exact h _ (List.getElem_mem hlt)
      · rw [List.getD_eq_default _ _ (not_lt.mp hlt)]
        simp
    simp only [wordMat]
    rw [← Matrix.mul_assoc, hi, Matrix.mul_assoc, ih, Matrix.mul_assoc]

structure CycData (d : ℕ) where
  gm : List (Matrix (Fin d) (Fin d) (ZMod 2))
  u : Fin d → ZMod 2
  words : Fin d → List ℕ
  Binv : Matrix (Fin d) (Fin d) (ZMod 2)

namespace CycData

variable {d : ℕ} (c : CycData d)

@[expose] def Bmat : Matrix (Fin d) (Fin d) (ZMod 2) :=
  Matrix.of fun r k => (wordMat c.gm (c.words k) *ᵥ c.u) r

@[expose] def Cmat (w : Fin d → ZMod 2) : Matrix (Fin d) (Fin d) (ZMod 2) :=
  Matrix.of fun r k => (wordMat c.gm (c.words k) *ᵥ w) r

@[expose] def Pmat (w : Fin d → ZMod 2) : Matrix (Fin d) (Fin d) (ZMod 2) := c.Cmat w * c.Binv

theorem Bmat_eq : c.Bmat = c.Cmat c.u := rfl

theorem eq_Pmat (hB : c.Bmat * c.Binv = 1) {P : Matrix (Fin d) (Fin d) (ZMod 2)}
    (h : ∀ M ∈ c.gm, P * M = M * P) : P = c.Pmat (P *ᵥ c.u) := by
  have key : P * c.Bmat = c.Cmat (P *ᵥ c.u) := by
    ext r k
    have h1 : (P * c.Bmat) r k = (P *ᵥ (wordMat c.gm (c.words k) *ᵥ c.u)) r := by
      simp [Bmat, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [h1, Matrix.mulVec_mulVec, comm_wordMat h, ← Matrix.mulVec_mulVec]
    rfl
  calc P = P * (c.Bmat * c.Binv) := by rw [hB, Matrix.mul_one]
    _ = c.Pmat (P *ᵥ c.u) := by rw [← Matrix.mul_assoc, key]; rfl

end CycData


theorem mem_bt (d : ℕ) (ok : List ℕ → ℕ → Bool) : ∀ (n : ℕ) (cs : List ℕ), cs.length = n →
    (∀ j < n, cs.getD j 0 < 2 ^ d ∧ ok (cs.take j) (cs.getD j 0) = true) → cs ∈ bt d ok n := by
  intro n
  induction n with
  | zero =>
    intro cs hcs _
    rw [List.length_eq_zero_iff] at hcs
    simp [hcs, bt]
  | succ n ih =>
    intro cs hcs hok
    rcases List.eq_nil_or_concat cs with h0 | ⟨pre, c, hpc⟩
    · rw [h0] at hcs
      simp at hcs
    · rw [List.concat_eq_append] at hpc
      subst hpc
      have hlen : pre.length = n := by simpa using hcs
      have hpre : pre ∈ bt d ok n := by
        refine ih pre hlen fun j hj => ?_
        have := hok j (by omega)
        rwa [List.getD_append _ _ _ _ (by omega), List.take_append_of_le_length (by omega)] at this
      have hlast := hok n (by omega)
      rw [List.take_append_of_le_length (by omega),
        List.getD_append_right _ _ _ _ (by omega)] at hlast
      have htake : pre.take n = pre := by rw [← hlen, List.take_length]
      simp only [hlen, htake, Nat.sub_self, List.getD_cons_zero] at hlast
      rw [bt, List.mem_flatMap]
      refine ⟨pre, hpre, ?_⟩
      rw [List.mem_map]
      refine ⟨c, ?_, rfl⟩
      rw [List.mem_filter, List.mem_range]
      exact ⟨hlast.1, hlast.2⟩


theorem colsOf_length (d : ℕ) (K : Matrix (Fin d) (Fin d) (ZMod 2)) : (colsOf d K).length = d := by
  simp [colsOf]

theorem colsOf_getD {d : ℕ} (hL : Laws d) (K : Matrix (Fin d) (Fin d) (ZMod 2)) (i : Fin d) :
    vecN d ((colsOf d K).getD i 0) = fun r => K r i := by
  have h := matOfCols_colsOf hL K
  funext r
  have := congrFun (congrFun h r) i
  simpa [matOfCols] using this

theorem colsOf_getD_lt {d : ℕ} (hL : Laws d) (K : Matrix (Fin d) (Fin d) (ZMod 2)) {j : ℕ}
    (hj : j < d) : (colsOf d K).getD j 0 < 2 ^ d := by
  rw [List.getD_eq_getElem _ _ (by simpa [colsOf_length] using hj)]
  simp only [colsOf, List.getElem_map]
  exact hL.code_lt _

theorem appAux_take (cols : List ℕ) (n x : ℕ) (hx : x < 2 ^ n) :
    ∀ m, appAux (cols.take n) x m = appAux cols x m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [appAux, appAux, ih]
    congr 1
    by_cases hb : x.testBit m
    · have hmn : m < n := by
        by_contra hge
        push Not at hge
        have : x < 2 ^ m := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hge)
        rw [Nat.testBit_lt_two_pow this] at hb
        exact absurd hb (by simp)
      simp only [hb, ite_true]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hmn]
    · simp [hb]

theorem commOk_sound {d : ℕ} (hL : Laws d) (Pc : List ℕ) (K : Matrix (Fin d) (Fin d) (ZMod 2))
    (hKP : matOfCols d Pc * K = K * matOfCols d Pc) (n : ℕ) (hn : n ≤ d) :
    commOk d Pc ((colsOf d K).take n) = true := by
  unfold commOk
  rw [List.all_eq_true]
  intro i hi
  have hlen : ((colsOf d K).take n).length = n := by
    simp [colsOf_length, hn]
  rw [List.mem_range, hlen] at hi
  rw [hlen]
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  by_cases hx : 2 ^ n ≤ Pc.getD i 0
  · exact Or.inl hx
  · right
    push Not at hx
    have hid : i < d := lt_of_lt_of_le hi hn
    have h1 : appC d ((colsOf d K).take n) (Pc.getD i 0) = appC d (colsOf d K) (Pc.getD i 0) :=
      appAux_take _ n _ hx d
    have h2 : ((colsOf d K).take n).getD i 0 = (colsOf d K).getD i 0 := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
    rw [h1, h2]
    apply (vecN_eq_iff_mod hL _ _).mp
    rw [vecN_appC, vecN_appC]
    rw [matOfCols_colsOf hL K, colsOf_getD hL K ⟨i, hid⟩]
    have hv : vecN d (Pc.getD i 0) = fun r => matOfCols d Pc r ⟨i, hid⟩ := by
      funext r
      simp [matOfCols]
    rw [hv]
    funext r
    have hrow := congrFun (congrFun hKP r) ⟨i, hid⟩
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using hrow.symm


@[expose] def cycOf (d : ℕ) (gm : List (List ℕ)) (u : ℕ) (words : List (List ℕ)) (binv : List ℕ) :
    CycData d where
  gm := gm.map (matOfCols d)
  u := vecN d u
  words := fun k => words.getD k []
  Binv := matOfCols d binv

theorem getD_map_matOfCols (d : ℕ) (gm : List (List ℕ)) (i : ℕ) :
    (gm.map (matOfCols d)).getD i 1 = matOfCols d (gm.getD i (oneC d)) := by
  by_cases h : i < gm.length
  · rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [List.getD_eq_default _ _ (by simpa using h), List.getD_eq_default _ _ (not_lt.mp h),
      matOfCols_oneC]

theorem matOfCols_wordC (d : ℕ) (gm : List (List ℕ)) (w : List ℕ) :
    matOfCols d (wordC d gm w) = wordMat (gm.map (matOfCols d)) w := by
  induction w with
  | nil => simp [wordC, wordMat, matOfCols_oneC]
  | cons i w ih => rw [wordC, matOfCols_mulC, ih, wordMat, getD_map_matOfCols]

theorem matOfCols_ccolsC (d : ℕ) (gm : List (List ℕ)) (u : ℕ) (words : List (List ℕ))
    (binv : List ℕ) (hw : words.length = d) (w : ℕ) :
    matOfCols d (ccolsC d gm words w) = (cycOf d gm u words binv).Cmat (vecN d w) := by
  ext r k
  have hk : (k : ℕ) < words.length := by rw [hw]; exact k.2
  have h1 : (ccolsC d gm words w).getD k 0 = appC d (wordC d gm (words.getD k [])) w := by
    rw [ccolsC, List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ hk]
    simp
  simp only [matOfCols, Matrix.of_apply, CycData.Cmat, cycOf]
  rw [h1, vecN_appC, matOfCols_wordC]

theorem Pmat_eq (d : ℕ) (gm : List (List ℕ)) (u : ℕ) (words : List (List ℕ)) (binv : List ℕ)
    (hw : words.length = d) (w : ℕ) :
    (cycOf d gm u words binv).Pmat (vecN d w) = matOfCols d (pcolsC d gm words binv w) := by
  rw [pcolsC, matOfCols_mulC, matOfCols_ccolsC d gm u words binv hw]
  rfl

theorem hB_of {d : ℕ} (hL : Laws d) (gm : List (List ℕ)) (u : ℕ) (words : List (List ℕ))
    (binv : List ℕ) (hw : words.length = d)
    (h : isOne d (mulC d (ccolsC d gm words u) binv) = true) :
    (cycOf d gm u words binv).Bmat * (cycOf d gm u words binv).Binv = 1 := by
  rw [CycData.Bmat_eq]
  have h1 := (isOne_iff hL _).mp h
  rw [matOfCols_mulC, matOfCols_ccolsC d gm u words binv hw] at h1
  exact h1


@[expose] def condC (d : ℕ) (gm : List (List ℕ)) (words : List (List ℕ)) (binv : List ℕ)
    (w : ℕ) : Bool :=
  let P := pcolsC d gm words binv w
  isOne d (mulC d P P) && gm.all (fun A => normC d (mulC d P A) == normC d (mulC d A P)) &&
    (fixC d P == 2 ^ (d - 2))

@[expose] def leafC (d : ℕ) (gp : List (List ℕ × List ℕ)) (fullM : List ℕ → Bool) (a : ℕ)
    (cs : List ℕ) : Bool :=
  !(fullM cs) || (isOne d (sqIter d (cubeC d cs) a) &&
    (!(isOne d (cubeC d cs)) || isOne d cs || spanC d (conjC d gp cs)))

theorem leaf_of_search {d : ℕ} (hL : Laws d) (gm : List (List ℕ))
    (gp : List (List ℕ × List ℕ)) (u : ℕ) (words : List (List ℕ)) (binv : List ℕ)
    (hw : words.length = d) (okM : List ℕ → ℕ → Bool) (fullM : List ℕ → Bool) (a : ℕ)
    (Mem : Matrix (Fin d) (Fin d) (ZMod 2) → Prop)
    (hok : ∀ K, Mem K → ∀ j < d, okM ((colsOf d K).take j) ((colsOf d K).getD j 0) = true)
    (hfull : ∀ K, Mem K → fullM (colsOf d K) = true)
    (hsearch : ∀ w < 2 ^ d, condC d gm words binv w = true →
      ∀ cs ∈ bt d (fun pre c => okM pre c &&
        commOk d (pcolsC d gm words binv w) (pre ++ [c])) d, leafC d gp fullM a cs = true) :
    ∀ w : Fin d → ZMod 2,
      (cycOf d gm u words binv).Pmat w * (cycOf d gm u words binv).Pmat w = 1 →
      (∀ A ∈ (cycOf d gm u words binv).gm,
        (cycOf d gm u words binv).Pmat w * A = A * (cycOf d gm u words binv).Pmat w) →
      fixCard ((cycOf d gm u words binv).Pmat w) = 2 ^ (d - 2) →
      ∀ K, Mem K → K * (cycOf d gm u words binv).Pmat w = (cycOf d gm u words binv).Pmat w * K →
        K ^ (3 * 2 ^ a) = 1 ∧ (K ^ 3 = 1 → K ≠ 1 →
          Span (conjM (gp.map fun p => (matOfCols d p.1, matOfCols d p.2)) K)) := by
  intro w hPP hPA hfix K hMem hK
  set wn := codeN d w with hwn
  have hw' : vecN d wn = w := hL.vec_code w
  set Pc := pcolsC d gm words binv wn with hPc
  have hP : (cycOf d gm u words binv).Pmat w = matOfCols d Pc := by
    rw [← hw', Pmat_eq d gm u words binv hw]
  rw [hP] at hPP hPA hfix hK
  have hcond : condC d gm words binv wn = true := by
    unfold condC
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [isOne_iff hL, matOfCols_mulC]
      exact hPP
    · rw [List.all_eq_true]
      intro A hA
      rw [beq_iff_eq, ← matOfCols_eq_iff hL, matOfCols_mulC, matOfCols_mulC]
      exact hPA (matOfCols d A) (by simp [cycOf]; exact ⟨A, hA, rfl⟩)
    · rw [← fixCard_matOfCols hL]
      exact hfix
  have hmem : colsOf d K ∈ bt d (fun pre c => okM pre c && commOk d Pc (pre ++ [c])) d := by
    refine mem_bt d _ d _ (colsOf_length d K) fun j hj => ?_
    have hcols : (colsOf d K).getD j 0 = codeN d (fun i => K i ⟨j, hj⟩) := by
      rw [List.getD_eq_getElem _ _ (by simpa [colsOf_length] using hj)]
      simp [colsOf]
    refine ⟨?_, ?_⟩
    · rw [hcols]; exact hL.code_lt _
    · rw [Bool.and_eq_true]
      refine ⟨hok K hMem j hj, ?_⟩
      have hts : (colsOf d K).take j ++ [(colsOf d K).getD j 0] = (colsOf d K).take (j + 1) := by
        rw [List.take_add_one, List.getD_eq_getElem?_getD]
        have hj' : j < (colsOf d K).length := by simpa [colsOf_length] using hj
        simp [List.getElem?_eq_getElem hj']
      rw [hts]
      exact commOk_sound hL Pc K hK.symm (j + 1) (by omega)
  have hleaf := hsearch wn (hL.code_lt w) hcond _ hmem
  unfold leafC at hleaf
  have hfK := hfull K hMem
  simp only [hfK, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at hleaf
  obtain ⟨hsq, hrest⟩ := hleaf
  have hKm : matOfCols d (colsOf d K) = K := matOfCols_colsOf hL K
  constructor
  · rw [isOne_iff hL, matOfCols_sqIter, matOfCols_cubeC, hKm] at hsq
    rw [pow_mul]
    exact hsq
  · intro hK3 hK1
    have h3 : isOne d (cubeC d (colsOf d K)) = true := by
      rw [isOne_iff hL, matOfCols_cubeC, hKm]
      exact hK3
    have h1 : isOne d (colsOf d K) = false := by
      by_contra hne
      have : isOne d (colsOf d K) = true := by simpa using hne
      rw [isOne_iff hL, hKm] at this
      exact hK1 this
    rcases hrest with (h | h) | h
    · rw [h3] at h
      exact absurd h (by simp)
    · rw [h1] at h
      exact absurd h (by simp)
    · have hsp := spanC_sound hL _ h
      have heq : (conjC d gp (colsOf d K)).map (matOfCols d) =
          conjM (gp.map fun p => (matOfCols d p.1, matOfCols d p.2)) K := by
        simp [conjC, conjM, List.map_flatMap, List.flatMap_map, matOfCols_mulC, hKm]
      rwa [heq] at hsp


theorem normC_eq_of_matOfCols {d : ℕ} (hL : Laws d) {a b : List ℕ}
    (h : normC d a = normC d b) : matOfCols d a = matOfCols d b :=
  (matOfCols_eq_iff hL a b).mpr h

theorem isPGroup_closure {Γ : Type} [Group Γ] {d : ℕ} (hL : Laws d)
    (mat : Γ → Matrix (Fin d) (Fin d) (ZMod 2))
    (hmul : ∀ γ δ, mat (γ * δ) = mat γ * mat δ) (hone : mat 1 = 1)
    (hinj : ∀ γ, mat γ = 1 → γ = 1)
    (gcs : List (Γ × List ℕ)) (hgc : ∀ p ∈ gcs, mat p.1 = matOfCols d p.2)
    (hinv : ∀ p ∈ gcs, ∃ q ∈ gcs, q.1 = p.1⁻¹)
    (slist : List (List ℕ)) (a : ℕ)
    (h1 : ∃ c ∈ slist, normC d c = normC d (oneC d))
    (hcl : ∀ c ∈ slist, ∀ p ∈ gcs, ∃ c' ∈ slist, normC d c' = normC d (mulC d p.2 c))
    (hpow : ∀ c ∈ slist, isOne d (sqIter d c a) = true) :
    IsPGroup 2 (Subgroup.closure {x : Γ | x ∈ gcs.map Prod.fst}) := by
  have hmatpow : ∀ (γ : Γ) (n : ℕ), mat (γ ^ n) = mat γ ^ n := by
    intro γ n
    induction n with
    | zero => rw [pow_zero, pow_zero, hone]
    | succ n ih => rw [pow_succ, pow_succ, hmul, ih]
  have key : ∀ x ∈ Subgroup.closure {x : Γ | x ∈ gcs.map Prod.fst},
      ∃ c ∈ slist, matOfCols d c = mat x := by
    intro x hx
    refine Subgroup.closure_induction_left (p := fun x _ => ∃ c ∈ slist, matOfCols d c = mat x)
      ?_ ?_ ?_ hx
    · obtain ⟨c, hc, hn⟩ := h1
      exact ⟨c, hc, by rw [normC_eq_of_matOfCols hL hn, matOfCols_oneC, hone]⟩
    · intro g hg y _ ⟨c, hc, hcy⟩
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
      obtain ⟨c', hc', hn⟩ := hcl c hc p hp
      refine ⟨c', hc', ?_⟩
      rw [normC_eq_of_matOfCols hL hn, matOfCols_mulC, hcy, ← hgc p hp, hmul]
    · intro g hg y _ ⟨c, hc, hcy⟩
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
      obtain ⟨q, hq, hqp⟩ := hinv p hp
      obtain ⟨c', hc', hn⟩ := hcl c hc q hq
      refine ⟨c', hc', ?_⟩
      rw [normC_eq_of_matOfCols hL hn, matOfCols_mulC, hcy, ← hgc q hq, hmul, hqp]
  intro γ
  obtain ⟨c, hc, hcm⟩ := key γ.1 γ.2
  refine ⟨a, ?_⟩
  have h1 := (isOne_iff hL _).mp (hpow c hc)
  rw [matOfCols_sqIter, hcm] at h1
  have h2 : mat (((γ ^ 2 ^ a : ↥(Subgroup.closure {x : Γ | x ∈ gcs.map Prod.fst})) : Γ)) = 1 := by
    rw [Subgroup.coe_pow, hmatpow]
    exact h1
  exact Subtype.ext (hinj _ h2)

end CFSG.Quasithin.H13.A6.GR
