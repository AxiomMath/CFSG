module

public import Certificates.Data.FzFusK2

public section

namespace Certificates.FzFus

open Certificates.FzJ36

@[expose] def D5M (u a b : Model) : Prop :=
  KEq (a * b) (b * a) ∧ ¬ KEq u 1 ∧ ¬ KEq (a * a) 1 ∧ ¬ KEq (b * b) 1 ∧
    ¬ KEq (a * a * (b * b)) 1 ∧ ¬ KEq (a * a) u ∧ ¬ KEq (b * b) u ∧
    ¬ KEq (a * a * (b * b)) u ∧ ¬ KEq (a * a) (b * b) ∧ ¬ KEq (a * a * (b * b)) (a * a) ∧
    ¬ KEq (a * a * (b * b)) (b * b)

@[expose] def d5b (u a b : Model) : Bool :=
  kb (a * b) (b * a) && !kb u 1 && !kb (a * a) 1 && !kb (b * b) 1 && !kb (a * a * (b * b)) 1 &&
    !kb (a * a) u && !kb (b * b) u && !kb (a * a * (b * b)) u && !kb (a * a) (b * b) &&
    !kb (a * a * (b * b)) (a * a) && !kb (a * a * (b * b)) (b * b)

theorem d5b_iff {u a b : Model} : d5b u a b = true ↔ D5M u a b := by
  simp only [d5b, D5M, Bool.and_eq_true, Bool.not_eq_true', kb_iff, kb_eq_false, and_assoc]

@[expose] def Pair7Fact : Prop := ∀ a b : Model, ¬ D5M z3M a b

@[expose] def pair7Check (_ : Unit := ()) : Bool :=
  let l := allM ()
  l.all fun a => l.all fun b => !d5b z3M a b

theorem pair7Check_sound (h : pair7Check () = true) : Pair7Fact := by
  intro a b hd
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp h a (allM_mem a)) b (allM_mem b)
  rw [Bool.not_eq_true'] at h1
  exact absurd (d5b_iff.mpr hd) (by rw [h1]; decide)

@[expose] def fusCheck (_ : Unit := ()) : Bool :=
  classCheck () && rowsCheck () && subsCheck () && pair7Check ()

theorem fusCheck_sound (h : fusCheck () = true) :
    ClassFact ∧ RowsFact ∧ SubsFact ∧ Pair7Fact := by
  simp only [fusCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨classCheck_sound h1, rowsCheck_sound h2, subsCheck_sound h3, pair7Check_sound h4⟩

end Certificates.FzFus
