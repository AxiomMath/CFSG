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
public import Mathlib.RingTheory.PiTensorProduct
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

namespace CFSG.Sporadic.LySchreier

variable {M : Type*} [DecidableEq M]

@[expose] def bfsVisit (gs : List (M → M)) (i : ℕ) (L : List M) : List M :=
  if h : i < L.length then
    gs.foldl (fun L' g => if g L[i] ∈ L' then L' else L' ++ [g L[i]]) L
  else L

@[expose] def bfsList (gs : List (M → M)) (root : M) (N : ℕ) : List M :=
  (List.range N).foldl (fun L i => bfsVisit gs i L) [root]

theorem bfsList_zero (gs : List (M → M)) (root : M) : bfsList gs root 0 = [root] := rfl

theorem bfsList_succ (gs : List (M → M)) (root : M) (N : ℕ) :
    bfsList gs root (N + 1) = bfsVisit gs N (bfsList gs root N) := by
  simp [bfsList, List.range_succ, List.foldl_append]

section Characterization

variable (gs : List (M → M)) (n : ℕ) (x : ℕ → M) (img : ℕ → ℕ → ℕ) (par lab : ℕ → ℕ)

@[expose] def discPos (j : ℕ) : ℕ := par j * gs.length + lab j

@[expose] def IsCut (s c : ℕ) : Prop :=
  1 ≤ c ∧ c ≤ n ∧ ∀ j, 1 ≤ j → j < n → (discPos gs par lab j < s ↔ j < c)

variable {gs n x img par lab}

omit [DecidableEq M] in
theorem IsCut.unique {s c c' : ℕ} (h : IsCut gs n par lab s c) (h' : IsCut gs n par lab s c') :
    c = c' := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := (h3' c h1 (by omega)).2 hlt
    exact absurd ((h3 c h1 (by omega)).1 this) (lt_irrefl _)
  · have := (h3 c' h1' (by omega)).2 hlt
    exact absurd ((h3' c' h1' (by omega)).1 this) (lt_irrefl _)

omit [DecidableEq M] in
theorem IsCut.mono {s s' c c' : ℕ} (hs : s ≤ s') (h : IsCut gs n par lab s c)
    (h' : IsCut gs n par lab s' c') : c ≤ c' := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  by_contra hlt
  push Not at hlt
  have := (h3 c' h1' (by omega)).2 hlt
  exact absurd ((h3' c' h1' (by omega)).1 (lt_of_lt_of_le this hs)) (lt_irrefl _)

variable
  (hmono : ∀ j, 1 ≤ j → j + 1 < n → discPos gs par lab j < discPos gs par lab (j + 1))

omit [DecidableEq M] in
include hmono in
theorem discPos_strictMono {j j' : ℕ} (hj : 1 ≤ j) (hjj' : j < j') (hj' : j' < n) :
    discPos gs par lab j < discPos gs par lab j' := by
  induction j', hjj' using Nat.le_induction with
  | base => exact hmono j hj hj'
  | succ j' hle ih => exact (ih (by omega)).trans (hmono j' (by omega) hj')

omit [DecidableEq M] in
include hmono in
theorem exists_isCut (hn : 1 ≤ n) (s : ℕ) : ∃ c, IsCut gs n par lab s c := by
  classical
  have hex : ∃ c, 1 ≤ c ∧ (c = n ∨ (c < n ∧ s ≤ discPos gs par lab c)) := ⟨n, hn, Or.inl rfl⟩
  have hc := Nat.find_spec hex
  have hmin : ∀ j < Nat.find hex, ¬(1 ≤ j ∧ (j = n ∨ (j < n ∧ s ≤ discPos gs par lab j))) :=
    fun j hj => Nat.find_min hex hj
  have hcn : Nat.find hex ≤ n := Nat.find_min' hex ⟨hn, Or.inl rfl⟩
  refine ⟨Nat.find hex, hc.1, hcn, fun j hj1 hjn => ⟨fun hjs => ?_, fun hjc => ?_⟩⟩
  · by_contra hjc
    push Not at hjc
    rcases hc.2 with hcn' | ⟨hcn', hsc⟩
    · omega
    · rcases Nat.lt_or_ge (Nat.find hex) j with hlt | hge
      · exact absurd (lt_of_le_of_lt (hsc.trans
          (discPos_strictMono hmono hc.1 hlt hjn).le) hjs) (lt_irrefl _)
      · have : Nat.find hex = j := le_antisymm hjc hge
        rw [this] at hsc
        omega
  · by_contra hjs
    push Not at hjs
    exact hmin j hjc ⟨hj1, Or.inr ⟨hjn, hjs⟩⟩

variable
  (hinj : ∀ i < n, ∀ j < n, x i = x j → i = j)
  (himg : ∀ i < n, ∀ (k : ℕ) (hk : k < gs.length), img k i < n ∧ gs[k] (x i) = x (img k i))
  (htree : ∀ j, 1 ≤ j → j < n → par j < j ∧ lab j < gs.length ∧ img (lab j) (par j) = j)
  (hdisc : ∀ i < n, ∀ k < gs.length,
    img k i = 0 ∨ discPos gs par lab (img k i) ≤ i * gs.length + k)

include hmono hinj himg htree hdisc in
theorem step_cut {i k c : ℕ} (hk : k < gs.length) (hc : IsCut gs n par lab (i * gs.length + k) c)
    (hic : i < c) :
    ∃ c', IsCut gs n par lab (i * gs.length + k + 1) c' ∧
      (if gs[k] (x i) ∈ (List.range c).map x then (List.range c).map x
        else (List.range c).map x ++ [gs[k] (x i)]) = (List.range c').map x := by
  obtain ⟨hc1, hcn, hcut⟩ := hc
  have hin : i < n := lt_of_lt_of_le hic hcn
  obtain ⟨htn, hte⟩ := himg i hin k hk
  set t := img k i with ht
  set s := i * gs.length + k with hs
  have hpos_eq : ∀ j, 1 ≤ j → j < n → discPos gs par lab j = s → j = t := by
    intro j hj1 hjn hjs
    obtain ⟨hpj, hlj, hij⟩ := htree j hj1 hjn
    unfold discPos at hjs
    have hpar : par j = i := by
      rcases lt_trichotomy (par j) i with hlt | heq | hgt
      · have : (par j + 1) * gs.length ≤ i * gs.length := Nat.mul_le_mul_right _ hlt
        rw [add_mul] at this
        omega
      · exact heq
      · have : (i + 1) * gs.length ≤ par j * gs.length := Nat.mul_le_mul_right _ hgt
        rw [add_mul] at this
        omega
    have hlab : lab j = k := by rw [hpar] at hjs; omega
    rw [ht, ← hij, hpar, hlab]
  by_cases hpresent : t = 0 ∨ discPos gs par lab t < s
  ·
    have htc : t < c := by
      rcases Nat.eq_zero_or_pos t with h0 | hpos
      · omega
      · rcases hpresent with h | h
        · omega
        · exact (hcut t hpos htn).1 h
    have hmem : gs[k] (x i) ∈ (List.range c).map x := by
      rw [hte]
      exact List.mem_map.2 ⟨t, List.mem_range.2 htc, rfl⟩
    refine ⟨c, ⟨hc1, hcn, fun j hj1 hjn => ?_⟩, by rw [ite_eq_left hmem]⟩
    rw [← hcut j hj1 hjn]
    constructor
    · intro hj
      rcases Nat.lt_or_ge (discPos gs par lab j) s with h | h
      · exact h
      · have he : discPos gs par lab j = s := by omega
        have hjt := hpos_eq j hj1 hjn he
        subst hjt
        rcases hpresent with h' | h'
        · omega
        · omega
    · intro hj; omega
  ·
    push Not at hpresent
    obtain ⟨ht0, hge⟩ := hpresent
    have hts : discPos gs par lab t = s := by
      rcases hdisc i hin k hk with h | h
      · exact absurd h ht0
      · exact le_antisymm h hge
    have ht1 : 1 ≤ t := Nat.one_le_iff_ne_zero.2 ht0
    have htc : c ≤ t := by
      by_contra hlt
      push Not at hlt
      have := (hcut t ht1 htn).2 hlt
      omega
    have htc' : t = c := by
      by_contra hne
      have hlt : c < t := lt_of_le_of_ne htc (Ne.symm hne)
      have hc' : ¬(discPos gs par lab c < s) := fun h => lt_irrefl c ((hcut c hc1 (by omega)).1 h)
      exact hc' (hts ▸ discPos_strictMono hmono hc1 hlt htn)
    have hnot : gs[k] (x i) ∉ (List.range c).map x := by
      rw [hte]
      intro hm
      obtain ⟨j, hj, hjx⟩ := List.mem_map.1 hm
      rw [List.mem_range] at hj
      have := hinj j (by omega) t htn hjx
      omega
    refine ⟨c + 1, ⟨by omega, by omega, fun j hj1 hjn => ?_⟩, ?_⟩
    · constructor
      · intro hj
        rcases Nat.lt_or_ge (discPos gs par lab j) s with h | h
        · have := (hcut j hj1 hjn).1 h
          omega
        · have he : discPos gs par lab j = s := by omega
          have := hpos_eq j hj1 hjn he
          omega
      · intro hj
        rcases Nat.lt_or_ge j c with h | h
        · have := (hcut j hj1 hjn).2 h
          omega
        · have : j = t := by omega
          rw [this, hts]
          omega
    · rw [ite_eq_right hnot, List.range_succ, List.map_append, hte, htc']
      rfl

include hmono hinj himg htree hdisc in
theorem visit_cut {i c : ℕ} (hc : IsCut gs n par lab (i * gs.length) c) (hic : i < c) :
    ∃ c', IsCut gs n par lab ((i + 1) * gs.length) c' ∧
      bfsVisit gs i ((List.range c).map x) = (List.range c').map x := by
  have hlen : i < ((List.range c).map x).length := by simpa using hic
  have hget : ((List.range c).map x)[i] = x i := by simp
  set F : List M → (M → M) → List M := fun L' g => if g (x i) ∈ L' then L' else L' ++ [g (x i)]
    with hF
  have key : ∀ k ≤ gs.length, ∃ c', IsCut gs n par lab (i * gs.length + k) c' ∧
      (gs.take k).foldl F ((List.range c).map x) = (List.range c').map x := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨c, by simpa using hc, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨c', hc', he⟩ := ih (by omega)
      have hcc' : c ≤ c' := IsCut.mono (by omega) hc hc'
      obtain ⟨c'', hc'', he'⟩ := step_cut hmono hinj himg htree hdisc (by omega) hc'
        (by omega)
      refine ⟨c'', by simpa [Nat.add_assoc] using hc'', ?_⟩
      rw [List.take_add_one, List.foldl_append, he]
      simp only [List.getElem?_eq_getElem (show k < gs.length by omega), Option.toList_some,
        List.foldl_cons, List.foldl_nil, hF]
      exact he'
  obtain ⟨c', hc', he⟩ := key gs.length le_rfl
  refine ⟨c', by simpa [add_mul] using hc', ?_⟩
  unfold bfsVisit
  rw [dite_eq_left hlen]
  simp only [hget]
  rw [List.take_length] at he
  exact he

include hmono hinj himg htree hdisc in
theorem bfsList_eq {root : M} (hn : 1 ≤ n) (h0 : x 0 = root) {N : ℕ} (hN : n ≤ N + 1) :
    bfsList gs root N = (List.range n).map x := by
  have hK : ∀ j, 1 ≤ j → j < n → discPos gs par lab j < (par j + 1) * gs.length := by
    intro j hj1 hjn
    have := (htree j hj1 hjn).2.1
    unfold discPos
    rw [add_mul]
    omega
  have claim : ∀ N, ∃ c, IsCut gs n par lab (N * gs.length) c ∧
      bfsList gs root N = (List.range c).map x := by
    intro N
    induction N with
    | zero =>
      refine ⟨1, ⟨le_rfl, hn, fun j hj1 hjn => ?_⟩, by simp [bfsList_zero, h0]⟩
      simp only [zero_mul, Nat.not_lt_zero, false_iff, not_lt]
      exact hj1
    | succ N ih =>
      obtain ⟨c, hc, he⟩ := ih
      rw [bfsList_succ, he]
      by_cases hNc : N < c
      · exact visit_cut hmono hinj himg htree hdisc hc hNc
      · push Not at hNc
        have hlen : ¬N < ((List.range c).map x).length := by simpa using hNc
        refine ⟨c, ⟨hc.1, hc.2.1, fun j hj1 hjn => ?_⟩, by rw [bfsVisit, dite_eq_right hlen]⟩
        rw [← hc.2.2 j hj1 hjn]
        constructor
        · intro hj
          have hpar : par j * gs.length < (N + 1) * gs.length :=
            lt_of_le_of_lt (Nat.le_add_right _ _) hj
          have hpar' : par j < N + 1 := Nat.lt_of_mul_lt_mul_right hpar
          rcases Nat.lt_or_ge (par j) N with hlt | hge
          · exact lt_of_lt_of_le (hK j hj1 hjn) (Nat.mul_le_mul_right _ hlt)
          · exfalso
            have hpj : par j = N := by omega
            have hjN : N < j := hpj ▸ (htree j hj1 hjn).1
            have hcn : c < n := by omega
            have hpc := (htree c hc.1 hcn).1
            have : discPos gs par lab c < N * gs.length :=
              lt_of_lt_of_le (hK c hc.1 hcn) (Nat.mul_le_mul_right _ (by omega))
            exact lt_irrefl c ((hc.2.2 c hc.1 hcn).1 this)
        · intro hj
          exact lt_of_lt_of_le hj (Nat.mul_le_mul_right _ (Nat.le_succ N))
  obtain ⟨c, hc, he⟩ := claim N
  have hcut : IsCut gs n par lab (N * gs.length) n := by
    refine ⟨hn, le_rfl, fun j hj1 hjn => ⟨fun _ => hjn, fun _ => ?_⟩⟩
    exact lt_of_lt_of_le (hK j hj1 hjn)
      (Nat.mul_le_mul_right _ (by have := (htree j hj1 hjn).1; omega))
  rw [he, hc.unique hcut]

end Characterization

end CFSG.Sporadic.LySchreier
