module

public import CFSG.LocalAnalysis.StandardType.FS81.Defs

public section

namespace CFSG.StandardType.FrameRoute.FS81.E7Frame

@[expose] def e7Good (e : Coords 8) : Prop :=
  (wt e = 1 ∧ (e 0 ≠ 0 ∨ e 1 ≠ 0)) ∨ (wt e = 2 ∧ e 0 = 0 ∧ e 1 = 0) ∨
    (wt e = 3 ∧ e 0 ≠ 0 ∧ e 1 ≠ 0) ∨
    (wt e = 7 ∧ e 0 = 0 ∧ ∏ i : Fin 6, e i.succ.succ = 1) ∨
    (wt e = 7 ∧ e 1 = 0 ∧ ∏ i : Fin 6, e i.succ.succ = -1)

instance (e : Coords 8) : Decidable (e7Good e) := by
  unfold e7Good
  infer_instance

theorem e7Good.ne_zero {e : Coords 8} (h : e7Good e) : e ≠ 0 := by
  rintro rfl
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [wt] at h1

theorem e7Good_e1 : e7Good (Pi.single 1 1) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem orth_e0 : ∀ v : Coords 8, e7Good v → ¬ e7Good (v + Pi.single 0 1) →
    ¬ e7Good (v - Pi.single 0 1) → v ≠ Pi.single 0 1 → v + Pi.single 0 1 ≠ 0 → v 0 = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem orth_e1_check : ∀ v : Coords 8, e7Good v ∧ v 0 = 0 ∧
    ¬ e7Good (Pi.single 1 1 + v) ∧ ¬ e7Good (Pi.single 1 1 - v) ∧ v ≠ Pi.single 1 1 ∧
      Pi.single 1 1 + v ≠ 0 → wt v = 2 ∧ v 1 = 0 := by
  decide +kernel

theorem orth_e1 {v : Coords 8} (hv : e7Good v) (hv0 : v 0 = 0)
    (hp : ¬ e7Good (Pi.single 1 1 + v)) (hm : ¬ e7Good (Pi.single 1 1 - v))
    (h1 : v ≠ Pi.single 1 1) (h2 : Pi.single 1 1 + v ≠ 0) : wt v = 2 ∧ v 1 = 0 :=
  orth_e1_check v ⟨hv, hv0, hp, hm, h1, h2⟩

set_option maxRecDepth 100000 in
theorem card_good_zero :
    (Finset.univ.filter fun v : Coords 8 => e7Good v ∧ v 0 = 0).card = 126 := by
  decide +kernel

theorem d6_vec : ∀ i j : Fin 6, i ≠ j → ∀ c : ZMod 3, c ≠ 0 →
    e7Good (Pi.single i.succ.succ 1 + c • Pi.single j.succ.succ 1) ∧
    ¬ e7Good (Pi.single 1 1 + (Pi.single i.succ.succ 1 + c • Pi.single j.succ.succ 1)) ∧
    ¬ e7Good (Pi.single 1 1 - (Pi.single i.succ.succ 1 + c • Pi.single j.succ.succ 1)) := by
  decide +kernel

end CFSG.StandardType.FrameRoute.FS81.E7Frame
