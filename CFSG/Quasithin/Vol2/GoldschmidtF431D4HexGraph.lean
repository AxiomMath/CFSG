module

public import Certificates.Data.D4HexBase
public import CFSG.Quasithin.Background.F3Paths
public import Mathlib.Algebra.Group.Action.Sum

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.D4Hex CFSG.Quasithin

abbrev HexVtx : Type := Fin 819 ⊕ Fin 2457

@[expose] def hexLine (v : Fin 2457) : Set (Fin 819) :=
  {p | ∃ k < 3, lineTab[3 * (v : ℕ) + k]! = (p : ℕ)}

@[expose] def hexAdj : HexVtx → HexVtx → Prop
  | Sum.inl p, Sum.inr v => p ∈ hexLine v
  | Sum.inr v, Sum.inl p => p ∈ hexLine v
  | _, _ => False

@[expose] def hexGraph : SimpleGraph HexVtx where
  Adj := hexAdj
  symm := ⟨by
    intro a b h
    cases a <;> cases b <;> exact h⟩
  loopless := ⟨by
    intro a h
    cases a <;> exact h⟩

theorem hexGraph_adj_inl_inr {p : Fin 819} {v : Fin 2457} :
    hexGraph.Adj (Sum.inl p) (Sum.inr v) ↔ p ∈ hexLine v := Iff.rfl

theorem hexGraph_adj_inr_inl {p : Fin 819} {v : Fin 2457} :
    hexGraph.Adj (Sum.inr v) (Sum.inl p) ↔ p ∈ hexLine v := Iff.rfl

theorem hexGraph_not_adj_inl {p q : Fin 819} : ¬ hexGraph.Adj (Sum.inl p) (Sum.inl q) :=
  fun h => h

theorem hexGraph_not_adj_inr {v w : Fin 2457} : ¬ hexGraph.Adj (Sum.inr v) (Sum.inr w) :=
  fun h => h

@[expose] def hexCode : HexVtx → ℕ
  | Sum.inl p => p
  | Sum.inr v => 819 + v

@[expose] def hexOfCode (n : ℕ) : HexVtx :=
  if h : n < 819 then Sum.inl ⟨n, h⟩
  else if h' : n - 819 < 2457 then Sum.inr ⟨n - 819, h'⟩ else Sum.inl 0

theorem hexCode_lt (x : HexVtx) : hexCode x < 3276 := by
  cases x with
  | inl p => have := p.2; simp only [hexCode]; omega
  | inr v => have := v.2; simp only [hexCode]; omega

theorem hexOfCode_inl {n : ℕ} (h : n < 819) : hexOfCode n = Sum.inl ⟨n, h⟩ := by
  simp [hexOfCode, h]

theorem hexOfCode_inr {n : ℕ} (h1 : 819 ≤ n) (h2 : n < 3276) :
    hexOfCode n = Sum.inr ⟨n - 819, by omega⟩ := by
  have h1 : ¬ n < 819 := by omega
  have h2 : n - 819 < 2457 := by omega
  simp [hexOfCode, h1, h2]

theorem hexOfCode_hexCode (x : HexVtx) : hexOfCode (hexCode x) = x := by
  cases x with
  | inl p => rw [show hexCode (Sum.inl p) = p from rfl, hexOfCode_inl p.2]
  | inr v =>
    have h1 : 819 ≤ hexCode (Sum.inr v : HexVtx) := by
      show 819 ≤ 819 + (v : ℕ)
      omega
    rw [hexOfCode_inr h1 (hexCode_lt _)]
    exact congrArg Sum.inr (Fin.ext (by show 819 + (v : ℕ) - 819 = v; omega))

theorem hexCode_hexOfCode {n : ℕ} (hn : n < 3276) : hexCode (hexOfCode n) = n := by
  by_cases h : n < 819
  · rw [hexOfCode_inl h]
    rfl
  · rw [hexOfCode_inr (by omega) hn]
    show 819 + (n - 819) = n
    omega

theorem hexCode_injective : Function.Injective hexCode := fun x y h =>
  (hexOfCode_hexCode x).symm.trans ((congrArg hexOfCode h).trans (hexOfCode_hexCode y))

theorem hexGraphAction_of {X : Type*} [Group X] [MulAction X (Fin 819)] [MulAction X (Fin 2457)]
    (h : ∀ (x : X) (p : Fin 819) (v : Fin 2457), x • p ∈ hexLine (x • v) ↔ p ∈ hexLine v) :
    GraphAction X hexGraph where
  adj_smul x a b := by
    cases a <;> cases b
    · exact Iff.rfl
    · rename_i p v
      exact h x p v
    · rename_i v p
      exact h x p v
    · exact Iff.rfl

end CFSG.Quasithin.D4Hex
