module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Set.Card

public section

namespace CFSG.Monster.Existence.Compat

variable {G : Type*} [Group G]

theorem card_conj_orbit_mul_card_inf_centralizer (H : Subgroup G) (γ : G) :
    Nat.card {x : G | ∃ h ∈ H, h * γ * h⁻¹ = x} *
      Nat.card ↥(H ⊓ Subgroup.centralizer ({γ} : Set G)) = Nat.card H := by
  let φ : H →* ConjAct G := ConjAct.toConjAct.toMonoidHom.comp H.subtype
  let : MulAction H G := MulAction.compHom G φ
  have hsmul : ∀ (h : H) (x : G), h • x = (h : G) * x * (h : G)⁻¹ := fun h x => rfl
  have hcard := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H γ)
  rw [Nat.card_prod] at hcard
  have hor : ((MulAction.orbit H γ : Set G)) = {x : G | ∃ h ∈ H, h * γ * h⁻¹ = x} := by
    ext x
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, h.2, (hsmul h γ).symm ▸ rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, rfl⟩
  have hst : Nat.card (MulAction.stabilizer H γ) =
      Nat.card ↥(H ⊓ Subgroup.centralizer ({γ} : Set G)) := by
    have key : ∀ h : MulAction.stabilizer H γ, (h.1 : G) * γ = γ * (h.1 : G) := by
      intro h
      have h1 : (h.1 : H) • γ = γ := h.2
      rw [hsmul] at h1
      exact mul_inv_eq_iff_eq_mul.1 h1
    have key2 : ∀ x : ↥(H ⊓ Subgroup.centralizer ({γ} : Set G)),
        (⟨x.1, x.2.1⟩ : H) • γ = γ := by
      intro x
      rw [hsmul]
      have := Subgroup.mem_centralizer_singleton_iff.1 x.2.2
      show x.1 * γ * x.1⁻¹ = γ
      rw [this, mul_inv_cancel_right]
    exact Nat.card_congr
      { toFun := fun h => ⟨h.1, h.1.2, Subgroup.mem_centralizer_singleton_iff.2 (key h)⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, key2 x⟩
        left_inv := fun h => rfl
        right_inv := fun x => rfl }
  rw [← hor, ← hst]
  exact hcard

theorem exists_conj_of_card {H : Subgroup G} {S : Set G} {n : ℕ}
    (hfin : Finite H) (hS : S.Finite)
    (hstable : ∀ h ∈ H, ∀ x ∈ S, h * x * h⁻¹ ∈ S)
    (hn : ∀ x ∈ S, Nat.card ↥(H ⊓ Subgroup.centralizer ({x} : Set G)) = n)
    (hcard : n * S.ncard = Nat.card H) {γ γ' : G} (hγ : γ ∈ S) (hγ' : γ' ∈ S) :
    ∃ g ∈ H, g * γ * g⁻¹ = γ' := by
  have hH : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have h1 := card_conj_orbit_mul_card_inf_centralizer H γ
  rw [hn γ hγ] at h1
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hcard
    exact hH hcard.symm
  set R : Set G := {x : G | ∃ h ∈ H, h * γ * h⁻¹ = x} with hR
  have hRS : R ⊆ S := by
    rintro _ ⟨h, hh, rfl⟩
    exact hstable h hh γ hγ
  have hRcard : R.ncard = S.ncard := by
    have : Nat.card R * n = n * S.ncard := by rw [h1, hcard]
    rw [Nat.card_coe_set_eq] at this
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hn0) (by rw [this, mul_comm])
  have hRS' : R = S := Set.eq_of_subset_of_ncard_le hRS (le_of_eq hRcard.symm) hS
  rw [← hRS'] at hγ'
  obtain ⟨h, hh, rfl⟩ := hγ'
  exact ⟨h, hh, rfl⟩

end CFSG.Monster.Existence.Compat
