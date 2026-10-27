module

public import CFSG.Certificates.NativeSchreierCard
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

namespace CFSG.Quasithin.KGC31

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

variable {n k : ℕ}

@[expose] noncomputable def arrChain (hn : 1 ≤ n) (S : Array (Array ℕ)) (m : ℕ) (hm : m ≤ S.size)
    (base : Vector (Fin n) k) (hb : base.toList.Nodup) (W : Array (List ℤ)) :
    RawSchreierDatum n where
  degree_pos := hn
  originalCount := m
  strongCount := S.size
  baseCount := k
  originalCount_le := hm
  original := Vector.ofFn fun i : Fin m => permOfArr n S[i.val]!
  strong := Vector.ofFn fun j : Fin S.size => permOfArr n S[j.val]!
  base := base
  base_distinct := hb
  derivation j _ := toLetters j.val W[j.val]!

@[expose] def arrO (S : Array (Array ℕ)) (m : ℕ) : Array (Array ℕ) := S.extract 0 m

@[expose] def arrBase (base : Vector (Fin n) k) : Array ℕ := base.toArray.map Fin.val

theorem map_getElem! {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β) (A : Array α) {j : ℕ}
    (hj : j < A.size) : (A.map f)[j]! = f A[j]! := by
  rw [getElem!_pos _ j (by simpa using hj), getElem!_pos A j hj, Array.getElem_map]

theorem arrO_get {S : Array (Array ℕ)} {m j : ℕ} (hm : m ≤ S.size) (hj : j < m) :
    (arrO S m)[j]! = S[j]! := by
  rw [arrO, getElem!_pos _ j (by simp; omega), Array.getElem_extract,
    getElem!_pos S j (by omega)]
  simp

theorem arrChainArrays (hn : 1 ≤ n) {S : Array (Array ℕ)} {m : ℕ} (hm : m ≤ S.size)
    {base : Vector (Fin n) k} (hb : base.toList.Nodup) {W : Array (List ℤ)} {chunks : ℕ}
    (hF : ChainCheckFacts n (arrO S m) S (arrBase base) W chunks) :
    ChainArrays (arrChain hn S m hm base hb W) (arrO S m) S (arrBase base) W where
  orig_size := by simp [arrO, arrChain]; omega
  strong_size := rfl
  base_size := by simp [arrBase, arrChain]
  orig i := by
    obtain ⟨i, hi⟩ := i
    have hi' : i < m := hi
    have hj : i < S.size := by omega
    have h := hF.strong_inv i hj
    rw [rawInvs, map_getElem! _ _ hj] at h
    have e : (arrChain hn S m hm base hb W).original.get ⟨i, hi⟩ = permOfArr n S[i]! := by
      change (Vector.ofFn fun i : Fin m => permOfArr n S[i.val]!).get ⟨i, hi'⟩ = _
      simp only [Vector.get, Vector.ofFn, Array.getElem_ofFn]
      rfl
    rw [e, arrO_get hm hi']
    exact (rep_permOfArr h).1
  strong j := by
    obtain ⟨j, hj⟩ := j
    have hj' : j < S.size := hj
    have h := hF.strong_inv j hj'
    rw [rawInvs, map_getElem! _ _ hj'] at h
    have e : (arrChain hn S m hm base hb W).strong.get ⟨j, hj⟩ = permOfArr n S[j]! := by
      change (Vector.ofFn fun j : Fin S.size => permOfArr n S[j.val]!).get ⟨j, hj'⟩ = _
      simp only [Vector.get, Vector.ofFn, Array.getElem_ofFn]
      rfl
    rw [e]
    exact (rep_permOfArr h).1
  base_val i := by
    have hi : (i : ℕ) < k := i.2
    change ((base.get i : Fin n) : ℕ) = (base.toArray.map Fin.val)[(i : ℕ)]!
    rw [getElem!_pos _ (i : ℕ) (by simpa using hi)]
    simp [Vector.get]
    rfl
  deriv _ _ := rfl

theorem arrChain_valid (hn : 1 ≤ n) {S : Array (Array ℕ)} {m : ℕ} (hm : m ≤ S.size)
    {base : Vector (Fin n) k} (hb : base.toList.Nodup) {W : Array (List ℤ)} {chunks : ℕ}
    (hc : 0 < chunks) (h : rawChainOK n (arrO S m) S (arrBase base) W chunks = true) :
    ValidSchreier (arrChain hn S m hm base hb W) :=
  (validSchreier_of_chainOK (arrChainArrays hn hm hb (chainCheckFacts h)) hc h).1

theorem card_arrChain (hn : 1 ≤ n) {S : Array (Array ℕ)} {m : ℕ} (hm : m ≤ S.size)
    {base : Vector (Fin n) k} (hb : base.toList.Nodup) {W : Array (List ℤ)} {chunks : ℕ}
    (hc : 0 < chunks) (h : rawChainOK n (arrO S m) S (arrBase base) W chunks = true) :
    Nat.card (arrChain hn S m hm base hb W).originalSubgroup =
      (rawOrbitSizes n S (arrBase base)).prod :=
  card_originalSubgroup_of_chainOK (arrChainArrays hn hm hb (chainCheckFacts h)) hc h

theorem arrChain_original_toList (hn : 1 ≤ n) (S : Array (Array ℕ)) (m : ℕ) (hm : m ≤ S.size)
    (base : Vector (Fin n) k) (hb : base.toList.Nodup) (W : Array (List ℤ)) :
    (arrChain hn S m hm base hb W).original.toList =
      (List.range m).map fun i => permOfArr n S[i]! := by
  change (Vector.ofFn fun i : Fin m => permOfArr n S[i.val]!).toList = _
  rw [Vector.toList_ofFn, List.ofFn_eq_map]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp

theorem arrChain_originalSubgroup (hn : 1 ≤ n) (S : Array (Array ℕ)) (m : ℕ) (hm : m ≤ S.size)
    (base : Vector (Fin n) k) (hb : base.toList.Nodup) (W : Array (List ℤ)) :
    (arrChain hn S m hm base hb W).originalSubgroup =
      Subgroup.closure {g | ∃ i < m, permOfArr n S[i]! = g} := by
  rw [RawSchreierDatum.originalSubgroup, arrChain_original_toList]
  congr 1
  ext g
  simp

theorem invCand_eq_foldl' (n : ℕ) (t : Array ℕ) :
    invCand n t = (List.range n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) := by
  unfold invCand
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

theorem rep_invCand_of_rep {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    Rep n (invCand n t) g⁻¹ := by
  have key : ∀ k ≤ n, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0)).size = n ∧ ∀ i < k, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0))[t[i]!]! = i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, hi⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set r := (List.range k).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0)
      have htk : t[k]! < n := ht.lt (by omega)
      refine ⟨by rw [Array.size_set!, hs], fun i hik => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hlt | rfl
      · have hne : t[i]! ≠ t[k]! := by
          intro e
          rw [ht.apply (by omega : i < n), ht.apply (by omega : k < n)] at e
          have := g.injective (Fin.ext e)
          simp at this
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
        exact hi i hlt
      · rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact htk)]
  intro x
  obtain ⟨hs, hi⟩ := key n le_rfl
  rw [invCand_eq_foldl']
  have e : t[(g⁻¹ x : Fin n).val]! = x.val := by
    rw [ht.apply (g⁻¹ x).2]
    simp
  rw [← e, hi _ (g⁻¹ x).2]

end CFSG.Quasithin.KGC31

end
