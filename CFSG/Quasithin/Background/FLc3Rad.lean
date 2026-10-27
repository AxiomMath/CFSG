module

public import CFSG.Quasithin.Background.FLc3Out
public import CFSG.Quasithin.Background.Module

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.FLc

open Matrix CFSG.Quasithin

variable {V : Type} [CommGroup V]

theorem not_ff_of_radical {n : ℕ} {ρ : SLt n →* MulAut V} (hρ : Function.Injective ρ)
    {Q : Subgroup (MulAut V)} (hQ : Q ≤ (Ut n).map ρ) {I : Set ℕ}
    (hnorm : ∀ x ∈ QI n I, ∀ a ∈ Q, ρ x * a * (ρ x)⁻¹ ∈ Q)
    (hmod : ∀ A'' : Subgroup (SLt n), A'' ≤ Ut n →
      (∀ y ∈ A'', ∀ i j : Fin n, i < j → (∀ d ∈ I, (i : ℕ) < d → (j : ℕ) < d) → mat y i j = 0) →
      A'' ≠ ⊥ → Nat.card (A''.map ρ) * Nat.card (fixV (A''.map ρ)) < Nat.card V)
    {A : Subgroup (MulAut V)} (hAQ : A ≤ Q) (hA : A ≠ ⊥) :
    Nat.card A * Nat.card (fixV A) < Nat.card V := by
  set Y : Subgroup (SLt n) := Q.comap ρ with hY
  have hYU : Y ≤ Ut n := by
    intro y hy
    obtain ⟨u, hu, hρu⟩ := hQ hy
    have : u = y := hρ hρu
    rw [← this]
    exact hu
  have hYnorm : ∀ x ∈ QI n I, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y := by
    intro x hx y hy
    show ρ (x * y * x⁻¹) ∈ Q
    rw [map_mul, map_mul, map_inv]
    exact hnorm x hx (ρ y) hy
  set A'' : Subgroup (SLt n) := A.comap ρ with hA''
  have hA''Y : A'' ≤ Y := fun y hy => hAQ hy
  have hmap : A''.map ρ = A := by
    rw [hA'', Subgroup.map_comap_eq]
    have hAr : A ≤ ρ.range := fun a ha => by
      obtain ⟨u, -, hu⟩ := hQ (hAQ ha)
      exact ⟨u, hu⟩
    exact inf_eq_right.2 hAr
  have hA''ne : A'' ≠ ⊥ := by
    intro h
    apply hA
    rw [← hmap, h, Subgroup.map_bot]
  have := hmod A'' (hA''Y.trans hYU) (fun y hy i j hij hblock =>
    entry_zero_of_normalized hYU hYnorm hij hblock (hA''Y hy)) hA''ne
  rw [hmap] at this
  exact this

end CFSG.Quasithin.FLc
