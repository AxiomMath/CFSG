module

public import CFSG.Quasithin.Background.B4Models
import CFSG.Quasithin.Background.B69Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

open CFSG.Quasithin

variable {W : Type} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {H : Subgroup (MulAut W)}

theorem natRealizes_nonempty_mulEquiv (h : (FFModel.nat Γ).Realizes H ⊤ ⊥) :
    Nonempty (↥Γ ≃* ↥H) := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨MulEquiv.ofBijective π ⟨CFSG.Quasithin.B69.natRealizes_injective hπ, hπ.1⟩⟩

theorem natRealizes_card_eq (h : (FFModel.nat Γ).Realizes H ⊤ ⊥) :
    Nat.card ↥H = Nat.card ↥Γ := by
  obtain ⟨e⟩ := natRealizes_nonempty_mulEquiv h
  exact Nat.card_congr e.toEquiv.symm

theorem natRealizes_pCore_eq_bot (p : ℕ) (h : (FFModel.nat Γ).Realizes H ⊤ ⊥)
    (hΓ : CFSG.pCore p ↥Γ = ⊥) : CFSG.pCore p ↥H = ⊥ := by
  obtain ⟨e⟩ := natRealizes_nonempty_mulEquiv h
  have hmap := CFSG.pCore_map_iso p e
  simpa [hΓ] using hmap.symm

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

end
