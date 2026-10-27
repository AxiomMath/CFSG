module

public import Certificates.Data.FzJtN

public section

namespace Certificates.FzJt

open Certificates.FzJ36 Certificates.FzFus

@[expose] def zs4 (_ : Unit := ()) : List Model := [1, z1M, z3M, z1M * z3M]

@[expose] def F2Fact : Prop :=
  ∀ q : Q8, (q = QuaternionGroup.a 1 ∨ q = QuaternionGroup.xa 0 ∨ q = QuaternionGroup.xa 3) →
    ¬ MJ (mkE 1 1 q)

@[expose] def F3Fact : Prop :=
  ∀ q : Q8, q * q = QuaternionGroup.a 2 → ∀ v w : Model, IsInvM v → IsInvM w →
    KEq (v * mkE 1 1 q) (mkE 1 1 q * v) → KEq (w * mkE 1 1 q) (mkE 1 1 q * w) →
    ¬ KEq v w → KEq (v * w) (w * v) → InZ v ∨ InZ w ∨ InZ (v * w)

@[expose] def F4Fact : Prop :=
  ∀ n : Model, KEq (n * n) z3M → (∀ q : Q8, ¬ KEq n (mkE 1 1 q)) →
    (n.right = 1 → ∃ q : Q8, ∃ z ∈ zs4 (), KEq n (mkE 1 1 q * z)) →
    ∃ v w : Model, KEq (v * n) (n * v) ∧ KEq (w * n) (n * w) ∧ IsInvM v ∧ IsInvM w ∧
      ¬ KEq v w ∧ KEq (v * w) (w * v) ∧ ¬ InZ v ∧ ¬ InZ w ∧ ¬ InZ (v * w)

@[expose] def f2Reps : List Q8 := [QuaternionGroup.a 1, QuaternionGroup.xa 0, QuaternionGroup.xa 3]

@[expose] def sixQ : List Q8 :=
  [QuaternionGroup.a 1, QuaternionGroup.a 3, QuaternionGroup.xa 0, QuaternionGroup.xa 1,
    QuaternionGroup.xa 2, QuaternionGroup.xa 3]

theorem sixQ_mem (q : Q8) (hq : q * q = QuaternionGroup.a 2) : q ∈ sixQ := by
  revert q
  decide

@[expose] def centInv (l : List Model) (a : Model) : List Model :=
  l.filter fun g => isInvB g && kb (g * a) (a * g)

@[expose] def centInvNZ (l Z : List Model) (n : Model) : List Model :=
  l.filter fun g => isInvB g && kb (g * n) (n * g) && !inZb Z g

@[expose] def f2Check (_ : Unit := ()) : Bool :=
  f2Reps.all fun q => fzJCheck (mkE 1 1 q) ()

@[expose] def f3Check (_ : Unit := ()) : Bool :=
  let l := allM ()
  let Z := zList ()
  sixQ.all fun q =>
    let C := centInv l (mkE 1 1 q)
    C.all fun v => C.all fun w =>
      kb v w || !kb (v * w) (w * v) || inZb Z v || inZb Z w || inZb Z (v * w)

@[expose] def f4Check (_ : Unit := ()) : Bool :=
  let l := allM ()
  let Q := allQ ()
  let Z := zList ()
  let Z4 := zs4 ()
  l.all fun n =>
    !kb (n * n) z3M || !(Q.all fun q => !kb n (mkE 1 1 q)) ||
    (decide (n.right = 1) && !(Q.any fun q => Z4.any fun z => kb n (mkE 1 1 q * z))) ||
    (let C := centInvNZ l Z n
     C.any fun v => C.any fun w => !kb v w && kb (v * w) (w * v) && !inZb Z (v * w))

@[expose] def fzJtCheck (_ : Unit := ()) : Bool := f2Check () && f3Check () && f4Check ()

theorem f2Check_sound (h : f2Check () = true) : F2Fact := by
  intro q hq
  have hmem : q ∈ f2Reps := by
    rcases hq with rfl | rfl | rfl <;> simp [f2Reps]
  exact fzJCheck_sound _ (List.all_eq_true.mp h q hmem)

theorem f3Check_sound (h : f3Check () = true) : F3Fact := by
  intro q hq v w hv hw hva hwa hvw hc
  unfold f3Check at h
  have h1 := List.all_eq_true.mp h q (sixQ_mem q hq)
  have hmem : ∀ g : Model, IsInvM g → KEq (g * mkE 1 1 q) (mkE 1 1 q * g) →
      g ∈ centInv (allM ()) (mkE 1 1 q) := fun g hg hga => by
    simp only [centInv, List.mem_filter, Bool.and_eq_true]
    exact ⟨allM_mem g, isInvB_iff.mpr hg, kb_iff.mpr hga⟩
  have h2 := List.all_eq_true.mp h1 v (hmem v hv hva)
  have h3 := List.all_eq_true.mp h2 w (hmem w hw hwa)
  simp only [Bool.or_eq_true, Bool.not_eq_true', kb_eq_false, kb_iff, inZb_iff] at h3
  rcases h3 with (((h3 | h3) | h3) | h3) | h3
  · exact absurd h3 hvw
  · exact absurd hc h3
  · exact Or.inl h3
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr h3)

theorem f4Check_sound (h : f4Check () = true) : F4Fact := by
  intro n h1 h2 h3
  unfold f4Check at h
  have hn := List.all_eq_true.mp h n (allM_mem n)
  have hA : (!kb (n * n) z3M) = false := by simp [kb_iff.mpr h1]
  have hB : (!(allQ ()).all fun q => !kb n (mkE 1 1 q)) = false := by
    have : ((allQ ()).all fun q => !kb n (mkE 1 1 q)) = true :=
      List.all_eq_true.mpr fun q _ => by simp [kb_eq_false.mpr (h2 q)]
    simp [this]
  have hC : (decide (n.right = 1) &&
      !((allQ ()).any fun q => (zs4 ()).any fun z => kb n (mkE 1 1 q * z))) = false := by
    by_cases hr : n.right = 1
    · obtain ⟨q, z, hz, hk⟩ := h3 hr
      have : ((allQ ()).any fun q => (zs4 ()).any fun z => kb n (mkE 1 1 q * z)) = true :=
        List.any_eq_true.mpr ⟨q, allQ_mem q, List.any_eq_true.mpr ⟨z, hz, kb_iff.mpr hk⟩⟩
      simp [this]
    · simp [hr]
  rw [hA, hB, hC, Bool.false_or, Bool.false_or, Bool.false_or] at hn
  obtain ⟨v, hv, hn⟩ := List.any_eq_true.mp hn
  obtain ⟨w, hw, hn⟩ := List.any_eq_true.mp hn
  simp only [centInvNZ, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
    inZb_eq_false, isInvB_iff, kb_iff] at hv hw hn
  obtain ⟨-, ⟨hvI, hvc⟩, hvZ⟩ := hv
  obtain ⟨-, ⟨hwI, hwc⟩, hwZ⟩ := hw
  obtain ⟨⟨hvw, hcomm⟩, hvwZ⟩ := hn
  exact ⟨v, w, hvc, hwc, hvI, hwI, by simpa [kb_eq_false] using hvw, hcomm, hvZ, hwZ, hvwZ⟩

theorem fzJtCheck_sound (h : fzJtCheck () = true) : F2Fact ∧ F3Fact ∧ F4Fact := by
  simp only [fzJtCheck, Bool.and_eq_true] at h
  exact ⟨f2Check_sound h.1.1, f3Check_sound h.1.2, f4Check_sound h.2⟩

end Certificates.FzJt
