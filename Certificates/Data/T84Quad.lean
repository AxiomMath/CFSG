module

public import Certificates.Data.Asc82NormA6

public section

namespace Certificates.T84Quad

open Matrix
open Certificates.A5GL42 (Mat4 Vec4 ofCode vecOfCode)

@[expose] def matsS0 : Finset Mat4 := (Certificates.Asc82NormA6.codesS0.map ofCode).toFinset

@[expose] def e1 : Vec4 := vecOfCode 1

structure Facts : Prop where
  trans : ∀ v : Vec4, v ≠ 0 → ∃ a ∈ matsS0, a *ᵥ e1 = v
  fix : ∀ w : Vec4, (∀ a ∈ matsS0, a *ᵥ e1 = e1 → a *ᵥ w = w) → w = 0 ∨ w = e1

def matL : List Mat4 := Certificates.Asc82NormA6.codesS0.map ofCode

def vecL : List Vec4 := (List.range 16).map vecOfCode

theorem mem_matL {a : Mat4} : a ∈ matL ↔ a ∈ matsS0 := by
  simp [matL, matsS0]

theorem mem_vecL (v : Vec4) : v ∈ vecL := by
  have h : ∀ a b c d : ZMod 2, ![a, b, c, d] ∈ vecL := by decide
  have hv : v = ![v 0, v 1, v 2, v 3] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  exact h _ _ _ _

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

@[expose] def check (_ : Unit := ()) : Bool :=
  let M := matL
  let V := vecL
  decide (∀ v ∈ V, v ≠ 0 → ∃ a ∈ M, a *ᵥ e1 = v) &&
    decide (∀ w ∈ V, (∀ a ∈ M, a *ᵥ e1 = e1 → a *ᵥ w = w) → w = 0 ∨ w = e1)

theorem facts_of_check (h : check () = true) : Facts := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun v hv => ?_, fun w hw => ?_⟩
  · obtain ⟨a, ha, hav⟩ := h1 v (mem_vecL v) hv
    exact ⟨a, mem_matL.mp ha, hav⟩
  · exact h2 w (mem_vecL w) fun a ha => hw a (mem_matL.mp ha)

end Certificates.T84Quad
