module

public import CFSG.Quasithin.Background.B4Models
import CFSG.Quasithin.Background.F918Z3DNat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

theorem s16c13bcA_nat_orbit_transfer {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} (hR : (FFModel.nat Γ).Realizes H (⊤ : Subgroup W) ⊥) :
    ∃ φ : W ≃ (ι → K), (∀ w : W, φ w = 0 ↔ w = 1) ∧ ∀ w₁ w₂ : W,
      (w₂ ∈ MulAction.orbit ↥H w₁ ↔ φ w₂ ∈ MulAction.orbit ↥Γ (φ w₁)) ∧
      Nat.card (MulAction.orbit ↥H w₁) = Nat.card (MulAction.orbit ↥Γ (φ w₁)) := by
  unfold FFModel.nat at hR
  obtain ⟨π, hRπ⟩ := hR
  obtain ⟨b, hb⟩ := CFSG.Quasithin.Z3D.exists_column_of_nat_realizes (H := H) hRπ
  have hπs : Function.Surjective π := hRπ.1
  let φ : W ≃ (ι → K) := b.toEquiv.trans Multiplicative.toAdd
  have hφ : ∀ w : W, φ w = (b w).toAdd := fun _ => rfl
  have hkey : ∀ (γ : ↥Γ) (w : W), φ (π γ • w) = γ • φ w := by
    intro γ w
    change (b ((π γ : MulAut W) w)).toAdd = γ • (b w).toAdd
    rw [hb γ w, toAdd_ofAdd]
    rfl
  refine ⟨φ, ?_, ?_⟩
  · intro w
    have hb1 : b w = 1 ↔ w = 1 := by
      constructor
      · intro h
        exact b.injective (by rw [h, map_one])
      · intro h
        rw [h, map_one]
    rw [hφ]
    exact toAdd_eq_zero.trans hb1
  · intro w₁ w₂
    have horbit : ∀ x : W, (x ∈ MulAction.orbit ↥H w₁ ↔ φ x ∈ MulAction.orbit ↥Γ (φ w₁)) := by
      intro x
      constructor
      · intro h
        rw [MulAction.mem_orbit_iff] at h ⊢
        obtain ⟨hH, hh⟩ := h
        obtain ⟨γ, rfl⟩ := hπs hH
        exact ⟨γ, by rw [← hh, hkey γ w₁]⟩
      · intro h
        rw [MulAction.mem_orbit_iff] at h ⊢
        obtain ⟨γ, hγ⟩ := h
        refine ⟨π γ, ?_⟩
        apply φ.injective
        rw [hkey γ w₁, hγ]
    exact ⟨horbit w₂, Nat.card_congr (Equiv.subtypeEquiv φ horbit)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
