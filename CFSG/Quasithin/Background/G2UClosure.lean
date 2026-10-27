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

public section

namespace CFSG.Quasithin.G2U

@[expose] def build (one : List ℕ) (mul : List ℕ → List ℕ → List ℕ) (gens : List (List ℕ))
    (par : List (ℕ × ℕ)) : Array (List ℕ) :=
  par.foldl (fun acc ps => acc.push (mul (acc.getD ps.1 one) (gens.getD ps.2 one))) #[one]

@[expose] def indexMap (es : Array (List ℕ)) : Std.HashMap (List ℕ) ℕ :=
  (List.range es.size).foldl (fun m t => m.insert (es.getD t []) t) {}

@[expose] def found (es : Array (List ℕ)) (m : Std.HashMap (List ℕ) ℕ) (y : List ℕ) : Bool :=
  match m.get? y with
  | some t => decide (t < es.size) && decide (es.getD t [] = y)
  | none => false

@[expose] def closedCheck (mul : List ℕ → List ℕ → List ℕ) (gens : List (List ℕ))
    (es : Array (List ℕ)) : Bool :=
  let m := indexMap es
  (List.range es.size).all fun v => gens.all fun g => found es m (mul (es.getD v []) g)

@[expose] def distinctCheck (es : Array (List ℕ)) : Bool :=
  let m := indexMap es
  (List.range es.size).all fun t => m.get? (es.getD t []) == some t

@[expose] def allCheck (p : List ℕ → Bool) (es : Array (List ℕ)) : Bool :=
  (List.range es.size).all fun t => p (es.getD t [])

@[expose] def bfsStep (mul : List ℕ → List ℕ → List ℕ) (gens : Array (List ℕ))
    (st : Array (List ℕ) × Array (ℕ × ℕ) × Std.HashMap (List ℕ) Unit) (head : ℕ) :
    Array (List ℕ) × Array (ℕ × ℕ) × Std.HashMap (List ℕ) Unit :=
  if head < st.1.size then
    (List.range gens.size).foldl (fun st s =>
      let y := mul (st.1.getD head []) (gens.getD s [])
      if st.2.2.contains y then st else (st.1.push y, st.2.1.push (head, s), st.2.2.insert y ()))
      st
  else st

@[expose] def bfsParents (one : List ℕ) (mul : List ℕ → List ℕ → List ℕ)
    (gens : List (List ℕ)) (fuel : ℕ) : List (ℕ × ℕ) :=
  ((List.range fuel).foldl (bfsStep mul gens.toArray)
    (#[one], #[], ({} : Std.HashMap (List ℕ) Unit).insert one ())).2.1.toList

variable {M : Type*} [Monoid M] (d : List ℕ → M) (one : List ℕ)
  (mul : List ℕ → List ℕ → List ℕ) (gens : List (List ℕ))

private theorem getD_mem {P : List ℕ → Prop} {acc : Array (List ℕ)} (h : ∀ x ∈ acc, P x)
    (h1 : P one) (i : ℕ) : P (acc.getD i one) := by
  rw [Array.getD]
  split_ifs with hi
  · exact h _ (Array.getElem_mem hi)
  · exact h1

private theorem list_getD_mem {P : List ℕ → Prop} (h : ∀ c ∈ gens, P c) (h1 : P one) (i : ℕ) :
    P (gens.getD i one) := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : gens[i]? with
  | none => exact h1
  | some c => exact h c (List.mem_of_getElem? hi)

private theorem foldl_push_mem {P : List ℕ → Prop} (h1 : P one)
    (hmul : ∀ x y, P x → P y → P (mul x y)) (hg : ∀ c ∈ gens, P c) :
    ∀ (par : List (ℕ × ℕ)) (acc : Array (List ℕ)), (∀ x ∈ acc, P x) →
      ∀ x ∈ par.foldl (fun acc ps => acc.push (mul (acc.getD ps.1 one) (gens.getD ps.2 one)))
        acc, P x := by
  intro par
  induction par with
  | nil => exact fun acc h => h
  | cons ps par ih =>
    intro acc h
    rw [List.foldl_cons]
    refine ih _ fun x hx => ?_
    rcases Array.mem_push.mp hx with hx | rfl
    · exact h x hx
    · exact hmul _ _ (getD_mem one h h1 _) (list_getD_mem one gens hg h1 _)

theorem decode_mem_closure_build (hone : d one = 1) (hmul : ∀ x y, d (mul x y) = d x * d y)
    (par : List (ℕ × ℕ)) :
    ∀ x ∈ build one mul gens par, d x ∈ Submonoid.closure {y | ∃ c ∈ gens, d c = y} := by
  refine foldl_push_mem one mul gens (P := fun x => d x ∈ Submonoid.closure _) ?_ ?_ ?_ par
    #[one] ?_
  · rw [hone]
    exact one_mem _
  · intro x y hx hy
    rw [hmul]
    exact mul_mem hx hy
  · exact fun c hc => Submonoid.subset_closure ⟨c, hc, rfl⟩
  · intro x hx
    rw [Array.mem_singleton.mp hx, hone]
    exact one_mem _

private theorem foldl_push_getD_zero (par : List (ℕ × ℕ)) :
    ∀ acc : Array (List ℕ), 0 < acc.size →
      (par.foldl (fun acc ps => acc.push (mul (acc.getD ps.1 one) (gens.getD ps.2 one))) acc
        ).getD 0 [] = acc.getD 0 [] ∧
      0 < (par.foldl (fun acc ps => acc.push (mul (acc.getD ps.1 one) (gens.getD ps.2 one)))
        acc).size := by
  induction par with
  | nil => exact fun acc h => ⟨rfl, h⟩
  | cons ps par ih =>
    intro acc h
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (acc.push (mul (acc.getD ps.1 one) (gens.getD ps.2 one)))
      (by rw [Array.size_push]; omega)
    refine ⟨h1.trans ?_, h2⟩
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
    rw [ite_eq_right (by omega)]

theorem build_getD_zero (par : List (ℕ × ℕ)) : (build one mul gens par).getD 0 [] = one :=
  (foldl_push_getD_zero one mul gens par #[one] (by simp)).1

theorem build_size_pos (par : List (ℕ × ℕ)) : 0 < (build one mul gens par).size :=
  (foldl_push_getD_zero one mul gens par #[one] (by simp)).2

theorem closedCheck_spec {es : Array (List ℕ)} (h : closedCheck mul gens es = true) :
    ∀ v < es.size, ∀ c ∈ gens, ∃ t < es.size, es.getD t [] = mul (es.getD v []) c := by
  intro v hv c hc
  simp only [closedCheck, List.all_eq_true, List.mem_range] at h
  have h' := h v hv c hc
  simp only [found] at h'
  split at h'
  · rename_i t _
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
    exact ⟨t, h'.1, h'.2⟩
  · exact absurd h' Bool.false_ne_true

theorem distinctCheck_spec {es : Array (List ℕ)} (h : distinctCheck es = true) {t t' : ℕ}
    (ht : t < es.size) (ht' : t' < es.size) (e : es.getD t [] = es.getD t' []) : t = t' := by
  simp only [distinctCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have h1 := h t ht
  rw [e, h t' ht'] at h1
  exact (Option.some_injective _ h1).symm

theorem allCheck_spec {p : List ℕ → Bool} {es : Array (List ℕ)} (h : allCheck p es = true)
    {t : ℕ} (ht : t < es.size) : p (es.getD t []) = true := by
  simp only [allCheck, List.all_eq_true, List.mem_range] at h
  exact h t ht

theorem image_closure_eq {G : Type*} [Group G] [Finite G] (f : G →* M)
    (hone : d one = 1) (hmul : ∀ x y, d (mul x y) = d x * d y) (S : Set G)
    (hS : f '' S = {y | ∃ c ∈ gens, d c = y}) (par : List (ℕ × ℕ))
    (h : closedCheck mul gens (build one mul gens par) = true) :
    f '' (Subgroup.closure S : Set G) =
      {y | ∃ t < (build one mul gens par).size, d ((build one mul gens par).getD t []) = y} := by
  set es := build one mul gens par
  have hcl : f '' (Subgroup.closure S : Set G) =
      (Submonoid.closure {y | ∃ c ∈ gens, d c = y} : Set M) := by
    rw [← hS, ← MonoidHom.map_mclosure, Submonoid.coe_map, ← Subgroup.closure_toSubmonoid_of_finite]
    rfl
  rw [hcl]
  apply Set.Subset.antisymm
  · intro y hy
    induction hy using Submonoid.closure_induction_right with
    | one => exact ⟨0, build_size_pos one mul gens par, by rw [build_getD_zero, hone]⟩
    | mul_right x _ z hz ih =>
      obtain ⟨v, hv, rfl⟩ := ih
      obtain ⟨c, hc, rfl⟩ := hz
      obtain ⟨t, ht, e⟩ := closedCheck_spec mul gens h v hv c hc
      exact ⟨t, ht, by rw [e, hmul]⟩
  · rintro _ ⟨t, ht, rfl⟩
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht, Option.getD_some]
    exact decode_mem_closure_build d one mul gens hone hmul par _ (Array.getElem_mem ht)

theorem card_closure_eq {G : Type*} [Group G] [Finite G] (f : G →* M)
    (hf : Function.Injective f) (hone : d one = 1) (hmul : ∀ x y, d (mul x y) = d x * d y)
    (S : Set G) (hS : f '' S = {y | ∃ c ∈ gens, d c = y}) (par : List (ℕ × ℕ))
    (h : closedCheck mul gens (build one mul gens par) = true)
    (hdist : distinctCheck (build one mul gens par) = true)
    (hd : ∀ t < (build one mul gens par).size, ∀ t' < (build one mul gens par).size,
      d ((build one mul gens par).getD t []) = d ((build one mul gens par).getD t' []) →
        (build one mul gens par).getD t [] = (build one mul gens par).getD t' []) :
    Nat.card (Subgroup.closure S) = (build one mul gens par).size := by
  set es := build one mul gens par
  have himg := image_closure_eq d one mul gens f hone hmul S hS par h
  have hrange : f '' (Subgroup.closure S : Set G) =
      Set.range fun t : Fin es.size => d (es.getD t []) := by
    rw [himg]
    ext y
    exact ⟨fun ⟨t, ht, e⟩ => ⟨⟨t, ht⟩, e⟩, fun ⟨t, e⟩ => ⟨t, t.2, e⟩⟩
  have hinj : Function.Injective fun t : Fin es.size => d (es.getD t []) :=
    fun t t' e => Fin.ext (distinctCheck_spec hdist t.2 t'.2 (hd t t.2 t' t'.2 e))
  calc Nat.card (Subgroup.closure S)
      = Nat.card (f '' (Subgroup.closure S : Set G)) :=
        (Nat.card_image_of_injective hf _).symm
    _ = Nat.card (Fin es.size) := by
        rw [hrange]
        exact Nat.card_range_of_injective hinj
    _ = es.size := Nat.card_fin _

end CFSG.Quasithin.G2U
