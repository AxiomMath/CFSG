module

public import CFSG.Quasithin.EmptyFaithful.S153MStrong2
public import CFSG.Quasithin.Background.B6Offenders

public section

namespace CFSG.Quasithin.S146zU.UC2

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Strong

variable {V : Type} [CommGroup V] [Finite V]

theorem card_mul_card_fixV_le (hV : ∀ v : V, v ^ 2 = 1) {Γ L₁ L₂ : Subgroup (MulAut V)}
    {τ : MulAut V} (h : S153M.TwoNat L₁ L₂ τ) (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hΓ : ffJ Γ = L₁ ⊔ L₂) {A : Subgroup (MulAut V)} (hAΓ : A ≤ Γ) (hA1 : A ≠ ⊥)
    (hA2 : IsElemAbelian2 A) : Nat.card ↥A * Nat.card ↥(fixV A) ≤ Nat.card V := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨B, ⟨hBA, hB0⟩, hmax⟩ := Set.exists_max_image
    {B : Subgroup (MulAut V) | B ≤ A ∧ B ≠ ⊥} (fun B => Nat.card ↥B * Nat.card ↥(fixV B))
    (Set.toFinite _) ⟨A, le_rfl, hA1⟩
  have hAmax : Nat.card ↥A * Nat.card ↥(fixV A) ≤ Nat.card ↥B * Nat.card ↥(fixV B) :=
    hmax A ⟨le_rfl, hA1⟩
  have hBe : IsElemAbelian2 B := B6.isElemAbelian2_mono hA2 hBA
  have hBoff : IsFFStarOffender Γ B := by
    refine ⟨hBA.trans hAΓ, hB0, hBe, fun B' hB' => ?_⟩
    by_cases hB'0 : B' = ⊥
    · subst hB'0
      rw [B1.card_bot_mul_card_fixV]
      exact hlt.le.trans hAmax
    · exact hmax B' ⟨hB'.trans hBA, hB'0⟩
  have hBJ : B ≤ L₁ ⊔ L₂ := hΓ ▸ B6.le_ffJ hBoff
  have := S153M.not_strong_of_twoNat hV h hcomm hBJ hB0 hBe
  omega

theorem not_isStrongFFModule (hV : ∀ v : V, v ^ 2 = 1) {Γ L₁ L₂ : Subgroup (MulAut V)}
    {τ : MulAut V} (h : S153M.TwoNat L₁ L₂ τ) (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hΓ : ffJ Γ = L₁ ⊔ L₂) : ¬ IsStrongFFModule Γ := by
  rintro ⟨A, hAΓ, hA1, hA2, hlt⟩
  have := card_mul_card_fixV_le hV h hcomm hΓ hAΓ hA1 hA2
  omega

end Strong

end CFSG.Quasithin.S146zU.UC2
