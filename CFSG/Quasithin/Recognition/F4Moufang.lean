module

public import CFSG.Quasithin.Background.F3Amalgam

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.F7 CFSG.Quasithin.RankTwoAmalgam.Completion

universe u w w'

@[expose] def MoufangHat (α : RankTwoAmalgam.{u}) (m : ℕ) : Prop :=
  ∀ p : GPath α.graphHat m, p.NoBack → ∀ ŷ ŷ' : α.Γhat, α.graphHat.Adj (p m) ŷ →
    α.graphHat.Adj (p m) ŷ' → ŷ ≠ p (m - 1) → ŷ' ≠ p (m - 1) →
    ∃ h : ↥(α.Ghat1 ⊔ α.Ghat2),
      (∀ i, 1 ≤ i → i ≤ m - 1 → ∀ w, α.graphHat.Adj (p i) w → h • w = w) ∧ h • ŷ = ŷ'

end CFSG.Quasithin
