module

public import CFSG.Quasithin.H13.GoldschmidtU43BPhi

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

set_option synthInstance.maxSize 1024

@[expose] def InP1 (v : V4) : Prop := v 2 = 0 ∧ v 3 = 0

@[expose] def InP2 (v : V4) : Prop := v 0 = 0 ∧ v 1 = 0

instance : DecidablePred InP1 := fun v => inferInstanceAs (Decidable (v 2 = 0 ∧ v 3 = 0))

instance : DecidablePred InP2 := fun v => inferInstanceAs (Decidable (v 0 = 0 ∧ v 1 = 0))

theorem perp_planes : ∀ v w : V4, InP1 v → InP2 w → bq v w = 0 := by
  decide +kernel

theorem q_plane1 : ∀ v : V4, InP1 v → v ≠ 0 → q v = 1 := by
  decide +kernel

@[expose] def SwapC (c : Fin 4 → V4) : Prop :=
  (∀ v, InP1 v → InP2 (app c v)) ∧ (∀ v, InP2 v → InP1 (app c v))

instance (c : Fin 4 → V4) : Decidable (SwapC c) :=
  inferInstanceAs (Decidable ((∀ v, InP1 v → InP2 (app c v)) ∧ (∀ v, InP2 v → InP1 (app c v))))

@[expose] def Cube1 (c : Fin 4 → V4) : Prop := comp c (comp c c) = idc

instance (c : Fin 4 → V4) : Decidable (Cube1 c) :=
  inferInstanceAs (Decidable (comp c (comp c c) = idc))

theorem card_cube1 : (Finset.univ.filter (fun x : OC => Cube1 x.cols)).card = 9 := by
  decide +kernel

theorem cube1_closed : ∀ x y : OC, Cube1 x.cols → Cube1 y.cols →
    Cube1 (comp x.cols y.cols) := by
  decide +kernel

theorem cube1_fixed : ∀ ξ : V4, ξ ≠ 0 → ∃ x : OC, Cube1 x.cols ∧ app x.cols ξ ≠ ξ := by
  decide +kernel

theorem exists_rho1 : ∃ x : OC, Cube1 x.cols ∧ x.cols ≠ idc ∧ ∀ v, InP2 v → app x.cols v = v := by
  decide +kernel

theorem rho_rot : ∀ x : OC, Cube1 x.cols → x.cols ≠ idc → (∀ v, InP2 v → app x.cols v = v) →
    ∀ ξ : V4, InP1 ξ → ξ ≠ 0 → app x.cols ξ ≠ ξ ∧
      ξ + app x.cols ξ + app x.cols (app x.cols ξ) = 0 := by
  decide +kernel

theorem fix_swap : ∀ τ α : V4, LinePair τ α → ∀ x : OC, FixPair τ α x → x.cols ≠ idc →
    SwapC x.cols ∧ comp x.cols x.cols = idc ∧ ∀ ξ : V4, app x.cols ξ = ξ → Aset τ α ξ := by
  decide +kernel

theorem fix_pair : ∀ τ α β : V4, LinePair τ α → LinePair τ β → bq α β = 1 →
    ∀ x : OC, FixPair τ α x → x.cols ≠ idc → ∀ y : OC, FixPair τ β y → y.cols ≠ idc →
      comp x.cols y.cols = comp y.cols x.cols ∧ x.cols ≠ y.cols := by
  decide +kernel

@[expose] def SwapPair (x y : Fin 4 → V4) : Prop :=
  SwapC x ∧ SwapC y ∧ comp x x = idc ∧ comp y y = idc ∧ comp x y = comp y x ∧ x ≠ y

instance (x y : Fin 4 → V4) : Decidable (SwapPair x y) :=
  inferInstanceAs (Decidable (SwapC x ∧ SwapC y ∧ comp x x = idc ∧ comp y y = idc ∧
    comp x y = comp y x ∧ x ≠ y))

theorem cprime_inv : ∀ x : OC, ∀ y : OC, SwapPair x.cols y.cols → ∀ r : OC, Cube1 r.cols →
    comp (comp x.cols y.cols) (comp r.cols (comp x.cols y.cols)) = comp r.cols r.cols := by
  decide +kernel

theorem cprime_refl : ∀ x : OC, ∀ y : OC, SwapPair x.cols y.cols →
    ∃ n : V4, InP1 n ∧ n ≠ 0 ∧ app (comp x.cols y.cols) n = n ∧
      ∀ ξ : V4, InP1 ξ → ξ ≠ 0 → ξ ≠ n → app (comp x.cols y.cols) ξ = ξ + n := by
  decide +kernel

theorem exists_other_plane1 : ∀ n : V4, InP1 n → n ≠ 0 → ∃ n' : V4, InP1 n' ∧ n' ≠ 0 ∧ n' ≠ n := by
  decide +kernel

theorem span_four : ∀ s : OC, SwapC s.cols → comp s.cols s.cols = idc → ∀ ρ : OC, Cube1 ρ.cols →
    ρ.cols ≠ idc → (∀ v, InP2 v → app ρ.cols v = v) → ∀ n : V4, InP1 n → n ≠ 0 →
    ∀ ξ : V4, ∃ e₁ e₂ e₃ e₄ : ZMod 2, ξ = e₁ • n + e₂ • app ρ.cols (app ρ.cols n) +
      e₃ • app s.cols n + e₄ • app s.cols (app ρ.cols (app ρ.cols n)) := by
  decide +kernel

end CFSG.Quasithin.H13.U43
