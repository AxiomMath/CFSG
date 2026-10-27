module

public import Certificates.Data.FzFusK1
public import Certificates.Data.FzFusPhi

public section

namespace Certificates.FzFus

open Certificates.FzJ36

@[expose] def RowOK (e w : Model) (u v : Cls) : Prop :=
  KEq (w * e) (e * w) ∧ IsInvM w ∧ ¬ KEq w e ∧ IsInvM (w * e) ∧ clsOf w = u ∧ clsOf (w * e) = v

@[expose] def rowOKb (e w : Model) (u v : Cls) : Bool :=
  kb (w * e) (e * w) && isInvB w && !kb w e && isInvB (w * e) && decide (clsOf w = u) &&
    decide (clsOf (w * e) = v)

theorem rowOKb_iff {e w : Model} {u v : Cls} : rowOKb e w u v = true ↔ RowOK e w u v := by
  simp only [rowOKb, RowOK, Bool.and_eq_true, Bool.not_eq_true', kb_iff, kb_eq_false, isInvB_iff,
    decide_eq_true_eq, and_assoc]

@[expose] def RowsFact : Prop :=
  ∀ r ∈ rowTable, ∃ w : Model, RowOK (rep r.1) w r.2.1 r.2.2

@[expose] def rowsCheck (_ : Unit := ()) : Bool :=
  let l := allM ()
  rowTable.all fun r => let e := rep r.1; l.any fun w => rowOKb e w r.2.1 r.2.2

theorem rowsCheck_sound (h : rowsCheck () = true) : RowsFact := by
  intro r hr
  obtain ⟨w, -, hw⟩ := List.any_eq_true.mp (List.all_eq_true.mp h r hr)
  exact ⟨w, rowOKb_iff.mp hw⟩

@[expose] def SubsFact : Prop :=
  ∀ s ∈ subTable, ∀ m : Model, IsInvM m → phi s.1 s.2.1 m = 1 → clsOf m ∈ s.2.2

@[expose] def subsCheck (_ : Unit := ()) : Bool :=
  let l := allM ()
  subTable.all fun s => l.all fun m =>
    !isInvB m || !decide (phi s.1 s.2.1 m = 1) || decide (clsOf m ∈ s.2.2)

theorem subsCheck_sound (h : subsCheck () = true) : SubsFact := by
  intro s hs m hm hphi
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp h s hs) m (allM_mem m)
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at h1
  rcases h1 with (h1 | h1) | h1
  · exact absurd (isInvB_iff.mpr hm) (by rw [h1]; decide)
  · exact absurd hphi h1
  · exact h1

end Certificates.FzFus
