module

public import CFSG.Quasithin.H13.GoldschmidtU43Act

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

@[expose] def LinePair (τ α : V4) : Prop :=
  q τ = 0 ∧ q α = 0 ∧ bq τ α = 0 ∧ τ ≠ 0 ∧ α ≠ 0 ∧ τ ≠ α

instance (τ α : V4) : Decidable (LinePair τ α) :=
  inferInstanceAs (Decidable (q τ = 0 ∧ q α = 0 ∧ bq τ α = 0 ∧ τ ≠ 0 ∧ α ≠ 0 ∧ τ ≠ α))

@[expose] def Aset (τ α v : V4) : Prop := v = 0 ∨ v = τ ∨ v = α ∨ v = τ + α

instance (τ α v : V4) : Decidable (Aset τ α v) :=
  inferInstanceAs (Decidable (v = 0 ∨ v = τ ∨ v = α ∨ v = τ + α))

@[expose] def PresA (τ α : V4) (x : OC) : Prop :=
  Aset τ α (app x.cols τ) ∧ Aset τ α (app x.cols α)

instance (τ α : V4) : DecidablePred (PresA τ α) := fun x =>
  inferInstanceAs (Decidable (Aset τ α (app x.cols τ) ∧ Aset τ α (app x.cols α)))

@[expose] def FixPair (τ α : V4) (x : OC) : Prop := app x.cols τ = τ ∧ app x.cols α = α

instance (τ α : V4) : DecidablePred (FixPair τ α) := fun x =>
  inferInstanceAs (Decidable (app x.cols τ = τ ∧ app x.cols α = α))

theorem card_presA_le : ∀ τ α : V4, LinePair τ α →
    (Finset.univ.filter (fun x : OC => PresA τ α x)).card ≤ 12 := by
  decide +kernel

theorem card_fixPair_le : ∀ τ α : V4, LinePair τ α →
    (Finset.univ.filter (fun x : OC => FixPair τ α x)).card ≤ 2 := by
  decide +kernel

theorem card_order_three_pos : ∀ τ α : V4, LinePair τ α →
    0 < (Finset.univ.filter
      (fun x : OC => Ord3 x.cols ∧ PresA τ α x ∧ app x.cols τ ≠ τ)).card := by
  decide +kernel

theorem exists_order_three (τ α : V4) (h : LinePair τ α) :
    ∃ x : OC, Ord3 x.cols ∧ PresA τ α x ∧ app x.cols τ ≠ τ := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (card_order_three_pos τ α h)
  exact ⟨x, (Finset.mem_filter.mp hx).2⟩

theorem perp_line : ∀ τ α : V4, LinePair τ α → ∀ x : V4, bq x τ = 0 → bq x α = 0 →
    Aset τ α x := by
  decide +kernel

end CFSG.Quasithin.H13.U43
