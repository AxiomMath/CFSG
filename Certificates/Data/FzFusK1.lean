module

public import Certificates.Data.FzFusM

public section

namespace Certificates.FzFus

open Certificates.FzJ36

@[expose] def kb (g h : Model) : Bool := decide (KEq g h)

theorem kb_iff {g h : Model} : kb g h = true ↔ KEq g h := by
  simp [kb]

theorem kb_eq_false {g h : Model} : kb g h = false ↔ ¬ KEq g h := by
  simp [kb]

@[expose] def allQ (_ : Unit := ()) : List Q8 :=
  [QuaternionGroup.a 0, QuaternionGroup.a 1, QuaternionGroup.a 2, QuaternionGroup.a 3,
   QuaternionGroup.xa 0, QuaternionGroup.xa 1, QuaternionGroup.xa 2, QuaternionGroup.xa 3]

theorem allQ_mem (q : Q8) : q ∈ allQ () := by
  revert q
  decide

@[expose] def allM (_ : Unit := ()) : List Model :=
  let l := allQ ()
  l.flatMap fun q1 => l.flatMap fun q2 => l.flatMap fun q3 =>
    [⟨(q1, q2, q3), 1⟩, ⟨(q1, q2, q3), Multiplicative.ofAdd 1⟩]

theorem allM_mem (g : Model) : g ∈ allM () := by
  obtain ⟨⟨q1, q2, q3⟩, e⟩ := g
  have he : ∀ e : Multiplicative (ZMod 2), e = 1 ∨ e = Multiplicative.ofAdd 1 := by decide
  rcases he e with rfl | rfl <;>
    exact List.mem_flatMap.mpr ⟨q1, allQ_mem q1,
      List.mem_flatMap.mpr ⟨q2, allQ_mem q2,
        List.mem_flatMap.mpr ⟨q3, allQ_mem q3, by simp⟩⟩⟩

@[expose] def IsInvM (m : Model) : Prop := KEq (m * m) 1 ∧ ¬ KEq m 1

@[expose] def isInvB (m : Model) : Bool := kb (m * m) 1 && !kb m 1

theorem isInvB_iff {m : Model} : isInvB m = true ↔ IsInvM m := by
  simp only [isInvB, IsInvM, Bool.and_eq_true, Bool.not_eq_true', kb_iff, kb_eq_false]

@[expose] def ClassFact : Prop :=
  ∀ m : Model, IsInvM m → ∃ g : Model, KEq (g * m * g⁻¹) (rep (clsOf m))

@[expose] def classCheck (_ : Unit := ()) : Bool :=
  let l := allM ()
  l.all fun m => !isInvB m || (let r := rep (clsOf m); l.any fun g => kb (g * m * g⁻¹) r)

theorem classCheck_sound (h : classCheck () = true) : ClassFact := by
  intro m hm
  have h1 := List.all_eq_true.mp h m (allM_mem m)
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h1
  rcases h1 with h1 | h1
  · exact absurd (isInvB_iff.mpr hm) (by rw [h1]; decide)
  · obtain ⟨g, -, hg⟩ := List.any_eq_true.mp h1
    exact ⟨g, kb_iff.mp hg⟩

end Certificates.FzFus
