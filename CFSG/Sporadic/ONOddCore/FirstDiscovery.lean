module

public import CFSG.Perm.OrbitTree
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open scoped Classical

section Defs

variable {G H : Type*} [Group G] [Group H]

@[expose] def evalPos (imgs : List H) (w : List ℕ) : H := (w.map fun l => imgs.getD (l - 1) 1).prod

theorem evalPos_nil (imgs : List H) : evalPos imgs [] = 1 := rfl

theorem evalPos_cons (imgs : List H) (l : ℕ) (w : List ℕ) :
    evalPos imgs (l :: w) = imgs.getD (l - 1) 1 * evalPos imgs w := by
  simp [evalPos]

theorem evalPos_append (imgs : List H) (w w' : List ℕ) :
    evalPos imgs (w ++ w') = evalPos imgs w * evalPos imgs w' := by
  simp [evalPos]

theorem map_evalPos {K : Type*} [Group K] (φ : H →* K) (imgs : List H) (w : List ℕ) :
    φ (evalPos imgs w) = evalPos (imgs.map φ) w := by
  simp only [evalPos, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  simp only [Function.comp_apply]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases imgs[l - 1]? <;> simp

@[expose] def visit (gens : List G) (x : G) (w : List ℕ) (D : List (G × List ℕ)) :
    List (G × List ℕ) :=
  gens.zipIdx.foldl (fun D' gj =>
    if D'.any (fun e => decide (e.1 = gj.1 * x)) then D' else D' ++ [(gj.1 * x, (gj.2 + 1) :: w)])
    D

@[expose] def searchStep (gens : List G) (D : List (G × List ℕ)) (h : ℕ) : List (G × List ℕ) :=
  match D[h]? with
  | none => D
  | some e => visit gens e.1 e.2 D

@[expose] def discovered (gens : List G) (k : ℕ) : List (G × List ℕ) :=
  (List.range k).foldl (searchStep gens) [(1, [])]

@[expose] def firstWord [Finite G] (gens : List G) (x : G) : List ℕ :=
  match (discovered gens (Nat.card G)).find? (fun e => decide (e.1 = x)) with
  | some e => e.2
  | none => []

@[expose] def substFun [Finite G] (gens : List G) (imgs : List H) (x : G) : H :=
  evalPos imgs (firstWord gens x)

end Defs

section Search

variable {G : Type*} [Group G] (gens : List G)

@[expose] def SearchInv (D : List (G × List ℕ)) : Prop :=
  (∀ e ∈ D, evalPos gens e.2 = e.1) ∧ (D.map Prod.fst).Nodup

theorem getD_of_mem_zipIdx {g : G} {j : ℕ} (h : (g, j) ∈ gens.zipIdx) : gens.getD j 1 = g := by
  rw [List.mem_zipIdx_iff_getElem?] at h
  simp [List.getD_eq_getElem?_getD, h]

theorem visit_inv {x : G} {w : List ℕ} (hxw : evalPos gens w = x) :
    ∀ (L : List (G × ℕ)) (D : List (G × List ℕ)), (∀ gj ∈ L, gj ∈ gens.zipIdx) →
      SearchInv gens D → SearchInv gens (L.foldl (fun D' gj =>
        if D'.any (fun e => decide (e.1 = gj.1 * x)) then D'
        else D' ++ [(gj.1 * x, (gj.2 + 1) :: w)]) D) ∧
        D <+: L.foldl (fun D' gj =>
          if D'.any (fun e => decide (e.1 = gj.1 * x)) then D'
          else D' ++ [(gj.1 * x, (gj.2 + 1) :: w)]) D ∧
        ∀ gj ∈ L, gj.1 * x ∈ (L.foldl (fun D' gj =>
          if D'.any (fun e => decide (e.1 = gj.1 * x)) then D'
          else D' ++ [(gj.1 * x, (gj.2 + 1) :: w)]) D).map Prod.fst
  | [], D, _, hD => ⟨hD, List.prefix_rfl, fun _ h => absurd h List.not_mem_nil⟩
  | gj :: L, D, hL, hD => by
    simp only [List.foldl_cons]
    set D₁ := if D.any (fun e => decide (e.1 = gj.1 * x)) then D
      else D ++ [(gj.1 * x, (gj.2 + 1) :: w)] with hD₁
    have hD₁inv : SearchInv gens D₁ ∧ D <+: D₁ ∧ gj.1 * x ∈ D₁.map Prod.fst := by
      by_cases hany : D.any (fun e => decide (e.1 = gj.1 * x)) = true
      · rw [hD₁, ite_eq_left hany]
        refine ⟨hD, List.prefix_rfl, ?_⟩
        obtain ⟨e, he, hex⟩ := List.any_eq_true.1 hany
        exact List.mem_map.2 ⟨e, he, of_decide_eq_true hex⟩
      · rw [hD₁, ite_eq_right hany]
        refine ⟨⟨fun e he => ?_, ?_⟩, List.prefix_append _ _, by simp⟩
        · rcases List.mem_append.1 he with he | he
          · exact hD.1 e he
          · rw [List.mem_singleton] at he
            subst he
            simp only
            rw [evalPos_cons, Nat.add_sub_cancel, getD_of_mem_zipIdx gens (hL gj
              List.mem_cons_self), hxw]
        · rw [List.map_append, List.nodup_append]
          refine ⟨hD.2, by simp, ?_⟩
          intro a ha b hb hab
          apply hany
          simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
          obtain ⟨e, he, hea⟩ := List.mem_map.1 ha
          exact List.any_eq_true.2 ⟨e, he, decide_eq_true (hea.trans (hab.trans hb))⟩
    obtain ⟨h1, h2, h3⟩ := visit_inv hxw L D₁ (fun g hg => hL g (List.mem_cons_of_mem _ hg))
      hD₁inv.1
    refine ⟨h1, hD₁inv.2.1.trans h2, fun g hg => ?_⟩
    rcases List.mem_cons.1 hg with rfl | hg
    · exact (List.Sublist.map Prod.fst h2.sublist).subset hD₁inv.2.2
    · exact h3 g hg

theorem searchStep_inv {D : List (G × List ℕ)} (hD : SearchInv gens D) (h : ℕ) :
    SearchInv gens (searchStep gens D h) ∧ D <+: searchStep gens D h := by
  unfold searchStep
  cases hDh : D[h]? with
  | none => exact ⟨hD, List.prefix_rfl⟩
  | some e =>
    have he : e ∈ D := List.mem_of_getElem? hDh
    obtain ⟨h1, h2, -⟩ := visit_inv gens (hD.1 e he) gens.zipIdx D (fun _ h => h) hD
    exact ⟨h1, h2⟩

theorem discovered_succ (k : ℕ) :
    discovered gens (k + 1) = searchStep gens (discovered gens k) k := by
  simp only [discovered, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem discovered_zero : discovered gens 0 = [(1, [])] := rfl

theorem discovered_inv (k : ℕ) : SearchInv gens (discovered gens k) := by
  induction k with
  | zero => exact ⟨by simp [discovered_zero, evalPos], by simp [discovered_zero]⟩
  | succ k ih =>
    rw [discovered_succ]
    exact (searchStep_inv gens ih k).1

theorem discovered_prefix_succ (k : ℕ) : discovered gens k <+: discovered gens (k + 1) := by
  rw [discovered_succ]
  exact (searchStep_inv gens (discovered_inv gens k) k).2

theorem discovered_prefix {k k' : ℕ} (h : k ≤ k') : discovered gens k <+: discovered gens k' := by
  induction h with
  | refl => exact List.prefix_rfl
  | step _ ih => exact ih.trans (discovered_prefix_succ gens _)

theorem discovered_stable {k : ℕ} (hk : (discovered gens k).length ≤ k) :
    ∀ k', k ≤ k' → discovered gens k' = discovered gens k := by
  intro k' hk'
  induction k', hk' using Nat.le_induction with
  | base => rfl
  | succ m hle ih =>
    rw [discovered_succ, ih]
    unfold searchStep
    rw [List.getElem?_eq_none (by omega)]

theorem length_discovered_le [Finite G] (k : ℕ) : (discovered gens k).length ≤ Nat.card G := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hn := (discovered_inv gens k).2
  rw [← List.length_map (f := Prod.fst), Nat.card_eq_fintype_card]
  exact hn.length_le_card

theorem discovered_closed [Finite G] {i : ℕ} (hi : i < (discovered gens (Nat.card G)).length)
    {g : G} (hg : g ∈ gens) :
    g * ((discovered gens (Nat.card G))[i]).1 ∈ (discovered gens (Nat.card G)).map Prod.fst := by
  set K := Nat.card G
  have hiK : i < K := lt_of_lt_of_le hi (length_discovered_le gens K)
  have hi' : i < (discovered gens i).length := by
    by_contra hlt
    push Not at hlt
    have := discovered_stable gens hlt K hiK.le
    rw [this] at hi
    omega
  have hpre := discovered_prefix gens hiK.le
  have hpre1 := discovered_prefix gens (Nat.succ_le_of_lt hiK)
  have hget : (discovered gens K)[i] = (discovered gens i)[i] := by
    rw [hpre.getElem hi']
  have hstep := discovered_succ gens i
  unfold searchStep at hstep
  rw [List.getElem?_eq_getElem hi'] at hstep
  simp only at hstep
  have hinv := discovered_inv gens i
  have he : (discovered gens i)[i] ∈ discovered gens i := List.getElem_mem hi'
  obtain ⟨-, -, hall⟩ := visit_inv gens (hinv.1 _ he) gens.zipIdx (discovered gens i)
    (fun _ h => h) hinv
  obtain ⟨j, hj⟩ : ∃ j, (g, j) ∈ gens.zipIdx := by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    exact ⟨j, List.mem_zipIdx_iff_getElem?.2 (by simp [hj])⟩
  have h1 : g * ((discovered gens i)[i]).1 ∈ (discovered gens (i + 1)).map Prod.fst := by
    have := hall (g, j) hj
    rwa [← visit, ← hstep] at this
  have e : (discovered gens (Nat.card G))[i] = (discovered gens i)[i] := hget
  rw [e]
  exact (List.Sublist.map Prod.fst hpre1.sublist).subset h1

theorem mem_discovered [Finite G] (hgen : Subgroup.closure {g | g ∈ gens} = ⊤) (x : G) :
    x ∈ (discovered gens (Nat.card G)).map Prod.fst := by
  let F : Set G := {y | y ∈ (discovered gens (Nat.card G)).map Prod.fst}
  have hSF : ∀ s ∈ {g | g ∈ gens}, ∀ y ∈ F, s • y ∈ F := by
    intro s hs y hy
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    exact discovered_closed gens hi hs
  have h1 : (1 : G) ∈ F := by
    have : (discovered gens 0) <+: discovered gens (Nat.card G) :=
      discovered_prefix gens (Nat.zero_le _)
    exact (List.Sublist.map Prod.fst this.sublist).subset (by simp [discovered])
  have hx : x ∈ Subgroup.closure {g | g ∈ gens} := by rw [hgen]; trivial
  have := CFSG.Perm.smul_mem_of_finite_of_mem_closure (Set.toFinite F) hSF hx h1
  rwa [smul_eq_mul, mul_one] at this

theorem evalPos_firstWord [Finite G] (hgen : Subgroup.closure {g | g ∈ gens} = ⊤) (x : G) :
    evalPos gens (firstWord gens x) = x := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 (mem_discovered gens hgen x)
  unfold firstWord
  cases hf : (discovered gens (Nat.card G)).find? (fun e' => decide (e'.1 = e.1)) with
  | none =>
    exfalso
    rw [List.find?_eq_none] at hf
    exact hf e he (decide_eq_true rfl)
  | some e' =>
    have he' := List.mem_of_find?_eq_some hf
    have hx := List.find?_some hf
    simp only [decide_eq_true_eq] at hx
    simp only
    rw [(discovered_inv gens _).1 e' he', hx]

theorem substFun_eq_of_hom {H : Type*} [Group H] [Finite G]
    (hgen : Subgroup.closure {g | g ∈ gens} = ⊤) (φ : G →* H) (x : G) :
    substFun gens (gens.map φ) x = φ x := by
  rw [substFun, ← map_evalPos, evalPos_firstWord gens hgen]

end Search

end CFSG.Sporadic.ONOddCore
